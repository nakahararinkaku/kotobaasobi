from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path
from collections import defaultdict
from urllib.parse import urlparse, parse_qs, quote
from urllib.request import Request, urlopen
import csv
import gzip
import json
import os
import re
import threading
import time
import uuid

ROOT = Path(__file__).resolve().parent
DATA = ROOT / "data" / "posts.json"
SYN_SRC = ROOT / "data" / "synonyms.txt"
OPEN_JSON = ROOT / "data" / "open-lexicon.json"
WN_TAB = ROOT / "data" / "wn-data-jpn.tab"
SUDACHI_URL = "https://raw.githubusercontent.com/WorksApplications/SudachiDict/develop/src/main/text/synonyms.txt"
WN_URL = "https://raw.githubusercontent.com/omwn/omw-data/main/wns/jpn/wn-data-jpn.tab"

SEEDS = [
    {"text": "朝の川面に、白い花びらがゆっくりと流れていた。", "ago": 3},
    {"text": "誰かの声が、水の奥でほどけていく。", "ago": 8},
    {"text": "私は岸で靴を脱ぎ、足元の冷たい砂を見た。", "ago": 12},
    {"text": "遠い橋の下を、光が薄く折れている。", "ago": 18},
    {"text": "ことばは葉のように、触れずにすれちがう。", "ago": 22},
    {"text": "午後の風が、水面に小さな皺を残した。", "ago": 28},
    {"text": "まだ名前のないまま、流れは続いていく。", "ago": 34},
]

_lexicon = None
_lex_mtime = 0
_lex_lock = threading.Lock()
_miss_cache = {}


def load_posts():
    DATA.parent.mkdir(exist_ok=True)
    if not DATA.exists():
        now = int(time.time() * 1000)
        posts = [
            {
                "id": uuid.uuid4().hex,
                "text": seed["text"],
                "t": now - seed["ago"] * 60_000,
                "guest": "river",
            }
            for seed in SEEDS
        ]
        save_posts(posts)
        return posts
    try:
        data = json.loads(DATA.read_text(encoding="utf-8"))
        return data.get("posts", [])
    except (json.JSONDecodeError, OSError):
        return []


def save_posts(posts):
    DATA.parent.mkdir(exist_ok=True)
    DATA.write_text(
        json.dumps({"posts": posts[-500:]}, ensure_ascii=False, indent=2),
        encoding="utf-8",
    )


def _http_get(url, timeout=25):
    req = Request(url, headers={"User-Agent": "kotobaasobi/1.0"})
    with urlopen(req, timeout=timeout) as res:
        return res.read()


def keep_lemma(lemma):
    lemma = (lemma or "").strip()
    if not lemma or len(lemma) > 6:
        return ""
    if lemma.isascii() and len(lemma) > 10:
        return ""
    if any(ch.isdigit() for ch in lemma) and len(lemma) > 4:
        return ""
    return lemma


def merge_group(mapping, words, cap=10):
    uniq = []
    seen = set()
    for word in words:
        word = keep_lemma(word)
        if not word or word in seen:
            continue
        seen.add(word)
        uniq.append(word)
    if len(uniq) < 2:
        return
    uniq = uniq[:12]
    for word in uniq:
        others = [item for item in uniq if item != word][:cap]
        if word not in mapping:
            mapping[word] = others
            continue
        have = set(mapping[word])
        for item in others:
            if item not in have:
                mapping[word].append(item)
                have.add(item)
        mapping[word] = mapping[word][:cap]


def ensure_wordnet():
    DATA.parent.mkdir(exist_ok=True)
    if WN_TAB.exists() and WN_TAB.stat().st_size > 1000:
        return
    WN_TAB.write_bytes(_http_get(WN_URL, timeout=120))


def ensure_sudachi():
    DATA.parent.mkdir(exist_ok=True)
    if SYN_SRC.exists() and SYN_SRC.stat().st_size > 1000:
        return
    SYN_SRC.write_bytes(_http_get(SUDACHI_URL, timeout=60))


def dirty_group(words):
    blob = " ".join(words)
    if re.search(r"[A-Za-z]", blob):
        return True
    return any(mark in blob for mark in ("会社", "工業", "銀行", "株式会社", "制度", "空港", "テレビ", "日産", "バス"))


def wordnet_groups():
    ensure_wordnet()
    groups = defaultdict(list)
    for line in WN_TAB.read_text(encoding="utf-8").splitlines():
        if "\tjpn:lemma\t" not in line:
            continue
        syn, _, lemma = line.split("\t", 2)
        lemma = keep_lemma(lemma)
        if lemma:
            groups[syn].append(lemma)
    return {syn: words for syn, words in groups.items() if not dirty_group(words)}


def sudachi_groups():
    ensure_sudachi()
    groups = defaultdict(list)
    for line in SYN_SRC.read_text(encoding="utf-8").splitlines():
        line = line.strip()
        if not line:
            continue
        row = next(csv.reader([line]))
        while len(row) < 9:
            row.append("")
        if (row[2] or "0") == "2":
            continue
        lemma = keep_lemma(row[8])
        if lemma:
            groups[row[0]].append(lemma)
    return groups


def is_jp(text):
    return any("\u3040" <= ch <= "\u30ff" or "\u4e00" <= ch <= "\u9fff" for ch in text)


def slim_mapping(mapping):
    slim = {}
    for word, syns in mapping.items():
        if not is_jp(word) or len(word) > 6:
            continue
        keep = [item for item in syns if is_jp(item) and len(item) <= 6][:8]
        if keep:
            slim[word] = keep
    return slim


_sudachi = None

def sudachi_lexicon():
    global _sudachi
    if _sudachi is not None:
        return _sudachi
    mapping = {}
    for words in sudachi_groups().values():
        joined = " ".join(words)
        if any(mark in joined for mark in ("銀行", "株式会社", "テレビ", "バス", "空港", "日産")):
            continue
        merge_group(mapping, words)
    _sudachi = slim_mapping(mapping)
    return _sudachi


def build_lexicon():
    mapping = {}
    for words in wordnet_groups().values():
        merge_group(mapping, words)
    mapping = slim_mapping(mapping)
    extra = sudachi_lexicon()
    for word, syns in extra.items():
        if word not in mapping:
            continue
        have = set(mapping[word])
        for item in syns:
            if item not in have:
                mapping[word].append(item)
                have.add(item)
        mapping[word] = mapping[word][:8]
    OPEN_JSON.write_text(json.dumps(mapping, ensure_ascii=False, separators=(",", ":")), encoding="utf-8")
    return mapping


def lexicon():
    global _lexicon, _lex_mtime
    mtime = OPEN_JSON.stat().st_mtime if OPEN_JSON.exists() else 0
    if _lexicon is not None and mtime == _lex_mtime:
        return _lexicon
    with _lex_lock:
        mtime = OPEN_JSON.stat().st_mtime if OPEN_JSON.exists() else 0
        if _lexicon is not None and mtime == _lex_mtime:
            return _lexicon
        if OPEN_JSON.exists() and OPEN_JSON.stat().st_size > 1000:
            _lexicon = json.loads(OPEN_JSON.read_text(encoding="utf-8"))
            _lex_mtime = OPEN_JSON.stat().st_mtime
            return _lexicon
        _lexicon = build_lexicon()
        _lex_mtime = OPEN_JSON.stat().st_mtime if OPEN_JSON.exists() else 0
        return _lexicon


def wiktionary_syns(word):
    out = []
    try:
        raw = _http_get(
            "https://ja.wiktionary.org/w/api.php?action=parse&redirects=1&prop=wikitext&format=json&page="
            + quote(word),
            timeout=12,
        )
        data = json.loads(raw.decode("utf-8"))
        wt = ((data.get("parse") or {}).get("wikitext") or {}).get("*") or ""
        for match in re.finditer(r"\{\{\s*(?:syn|synonyms)\|ja\|([^}]+)\}\}", wt, re.I):
            for part in match.group(1).split("|"):
                part = keep_lemma(part.split("=")[-1] if "=" in part else part)
                if part and part != word and part not in out:
                    out.append(part)
        section = re.search(r"===\s*類義語\s*===([\s\S]*?)(?:\n===[^=]|\n==[^=])", wt)
        if section:
            for match in re.finditer(r"\[\[([^\]|#]+)", section.group(1)):
                part = keep_lemma(match.group(1))
                if part and part != word and part not in out:
                    out.append(part)
    except Exception:
        return []
    return out[:12]


def conceptnet_syns(word):
    out = []
    try:
        raw = _http_get(
            f"https://api.conceptnet.io/query?node=/c/ja/{quote(word)}&rel=/r/Synonym&limit=24",
            timeout=8,
        )
        data = json.loads(raw.decode("utf-8"))
        for edge in data.get("edges") or []:
            for side in ("start", "end"):
                node = edge.get(side) or {}
                label = keep_lemma(node.get("label") or "")
                term = node.get("term") or ""
                if "/c/ja/" not in term:
                    continue
                if label and label != word and label not in out:
                    out.append(label)
    except Exception:
        return []
    return out[:12]


def lookup_syns(word):
    word = keep_lemma((word or "").strip()[:40]) or (word or "").strip()[:40]
    if not word:
        return []
    local = lexicon().get(word)
    if local:
        return local
    extra = sudachi_lexicon().get(word)
    if extra:
        return extra
    if word in _miss_cache:
        return _miss_cache[word]
    found = wiktionary_syns(word) or conceptnet_syns(word)
    _miss_cache[word] = found
    if found:
        mapping = lexicon()
        mapping[word] = found
        for syn in found:
            mapping.setdefault(syn, [])
            if word not in mapping[syn]:
                mapping[syn].append(word)
    return found


class Handler(SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def log_message(self, fmt, *args):
        pass

    def send_json(self, payload, status=200, cache="no-store"):
        raw = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        encode = "gzip" in (self.headers.get("Accept-Encoding") or "") and len(raw) > 2048
        if encode:
            raw = gzip.compress(raw, 6)
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Cache-Control", cache)
        if encode:
            self.send_header("Content-Encoding", "gzip")
        self.send_header("Content-Length", str(len(raw)))
        self.end_headers()
        self.wfile.write(raw)

    def do_GET(self):
        parsed = urlparse(self.path)
        path = parsed.path
        query = parse_qs(parsed.query)
        if path == "/api/posts":
            self.send_json({"posts": load_posts()})
            return
        if path == "/api/lexicon":
            try:
                data = lexicon()
                self.send_json(
                    {
                        "source": "日本語WordNet / Sudachi同義語辞書 / ウィクショナリー",
                        "license": "wordnet / Apache-2.0 / CC BY-SA",
                        "count": len(data),
                        "map": data,
                    },
                    cache="public, max-age=86400",
                )
            except Exception as err:
                self.send_json({"error": str(err), "map": {}, "count": 0}, 500)
            return
        if path == "/api/synonyms":
            word = (query.get("q") or [""])[0]
            try:
                self.send_json({"q": word, "syns": lookup_syns(word)}, cache="public, max-age=3600")
            except Exception as err:
                self.send_json({"q": word, "syns": [], "error": str(err)}, 500)
            return
        super().do_GET()

    def do_POST(self):
        if urlparse(self.path).path != "/api/posts":
            self.send_error(404)
            return
        length = int(self.headers.get("Content-Length", "0") or 0)
        try:
            body = json.loads(self.rfile.read(length) or b"{}")
        except json.JSONDecodeError:
            self.send_json({"error": "invalid"}, 400)
            return
        text = str(body.get("text") or "").strip()[:240]
        guest = str(body.get("guest") or "")[:80]
        if not text:
            self.send_json({"error": "empty"}, 400)
            return
        posts = load_posts()
        post = {
            "id": uuid.uuid4().hex,
            "text": text,
            "t": int(time.time() * 1000),
            "guest": guest,
        }
        posts.append(post)
        save_posts(posts)
        self.send_json(post)


if __name__ == "__main__":
    host = os.environ.get("HOST", "0.0.0.0")
    port = int(os.environ.get("PORT", "8765"))
    server = ThreadingHTTPServer((host, port), Handler)
    print(f"http://{host}:{port}/", flush=True)
    server.serve_forever()
