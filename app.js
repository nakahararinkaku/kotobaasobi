const PARTICLES = [
  "について",
  "にとって",
  "として",
  "という",
  "といった",
  "ながら",
  "けれども",
  "から",
  "まで",
  "より",
  "ので",
  "のに",
  "など",
  "だけ",
  "ばかり",
  "ほど",
  "くらい",
  "ぐらい",
  "こそ",
  "さえ",
  "でも",
  "しか",
  "つつ",
  "たり",
  "たら",
  "なら",
  "ては",
  "では",
  "のは",
  "のが",
  "って",
  "は",
  "が",
  "を",
  "に",
  "で",
  "と",
  "の",
  "も",
  "へ",
  "や",
  "な",
];

const GLUE = ["の", "と", "や", "に", "を", "が", "は", "で", "へ", "も"];
const CLEAR_PARTICLES = new Set(["は", "が", "を", "に", "で", "と", "の", "も", "へ", "や", "から", "まで", "より", "て", "こそ", "さえ"]);
const PARTICLE_SWAP = {
  は: ["が", "も", "こそ"],
  が: ["は", "も", "の"],
  を: ["に", "へ", "と"],
  に: ["を", "へ", "で"],
  で: ["に", "から", "を"],
  と: ["や", "の", "に"],
  の: ["が", "と", "へ"],
  も: ["は", "が", "さえ"],
  へ: ["に", "を", "まで"],
  や: ["と", "の", "が"],
  から: ["まで", "より", "で"],
  まで: ["から", "へ", "に"],
  より: ["から", "ほど", "の"],
  て: ["つつ", "ながら", "と"],
};
const ALL_CLEAR = [...CLEAR_PARTICLES];
const MAX_TOKENS = 100;
const TOUCH_R = 92;
const TOUCH_R_PART = 64;

const THESAURUS = {};
let LEXICON = null;

const HIRA_LEXICON = `
わたし あなた かれ かのじょ ぼく きみ これ それ あれ どれ
ここ そこ あそこ だれ なに なん なぜ どうして どう こんな そんな あんな
せかい ことば こころ ひかり かげ ゆめ うみ そら やま かわ みち まち
あめ ゆき かぜ ひ つき ほし はな き いし すな なみ しお
まど いえ ひと こえ おと め て あし からだ いき
しずか おおきい ちいさい しろい くろい あかい あおい あたらしい ふるい
あたたかい つめたい ふかい あさい とおい ちかい はやい おそい
しらない しっている わからない わかる おもっている かんがえる かんじる
ある いる する なる いく くる みる きく いう はなす かく
たべる のむ ねる おきる あるく はしる およぐ とぶ おちる
うまれる しぬ すき きらい ほしい いたい
ゆっくり すぐに また もう まだ ずっと きっと たぶん すこし たくさん
けさ きょう あした きのう いま いつ つぎ まえ のち
あいだ なか そと うえ した まえ うしろ となり
はなし はじまり おわり ひかり やみ あかり かげ
しずく なみだ おもい きもち いみ かたち いろ おと
れいぞうこ ぽけっと ポケット
ひらがな かんじ ぶんしょう
`.trim().split(/\s+/).filter(Boolean);

const AUX_ENDINGS = [
  "なかった",
  "ました",
  "ません",
  "でした",
  "ではない",
  "じゃない",
  "ている",
  "ていた",
  "てる",
  "ない",
  "ます",
  "です",
  "だった",
  "だ",
];

let SENSE_LIST = [...HIRA_LEXICON].sort((a, b) => b.length - a.length);
let SENSE_SET = new Set(SENSE_LIST);

function rebuildSense() {
  SENSE_LIST = [...new Set(HIRA_LEXICON)].sort((a, b) => b.length - a.length);
  SENSE_SET = new Set(SENSE_LIST);
}
const STORE_KEY = "kotobaasobi-sea-v1";
const AUTHOR_KEY = "kotobaasobi-author";
const WINDOW_MS = 45 * 60 * 1000;
const DEPTH_SCREENS = 9;
const SEED_TEXTS = [
  "朝の川面に、白い花びらがゆっくりと流れていた。",
  "誰かの声が、水の奥でほどけていく。",
  "私は岸で靴を脱ぎ、足元の冷たい砂を見た。",
  "遠い橋の下を、光が薄く折れている。",
  "ことばは葉のように、触れずにすれちがう。",
  "午後の風が、水面に小さな皺を残した。",
  "まだ名前のないまま、流れは続いていく。",
];

const canvas = document.getElementById("field");
const ctx = canvas ? canvas.getContext("2d") : null;
const wordsLayer = document.getElementById("words");
const form = document.getElementById("composer");
const input = document.getElementById("sentence");

const tokens = [];
const spawnQ = [];
let lastSpawnAt = 0;
const textCount = new Map();
const ripples = [];
const touchCool = new Map();
let tokenSeq = 0;
let spawnedBand = -1;
let packing = false;
let seaWords = [];
let seaCorpus = [];

let width = 0;
let height = 0;
let dpr = 1;
let scrollY = 0;
let seaHeight = 0;
let authorId = ensureAuthor();

function ensureAuthor() {
  let id = localStorage.getItem(AUTHOR_KEY);
  if (!id) {
    id = `a-${Math.random().toString(36).slice(2, 10)}`;
    localStorage.setItem(AUTHOR_KEY, id);
  }
  return id;
}

function mulberry32(seed) {
  let a = seed >>> 0;
  return () => {
    a += 0x6d2b79f5;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

function hashStr(s) {
  let h = 2166136261;
  for (let i = 0; i < s.length; i++) {
    h ^= s.charCodeAt(i);
    h = Math.imul(h, 16777619);
  }
  return h >>> 0;
}

function pick(rng, list) {
  if (!Array.isArray(list) || !list.length) return null;
  const fn = typeof rng === "function" ? rng : Math.random;
  return list[Math.floor(fn() * list.length)];
}

function pickFresh(rng, list) {
  const uniq = [...new Set((list || []).filter(Boolean))];
  if (!uniq.length) return null;
  const ranked = uniq
    .map((w) => ({ w, n: countText(w) }))
    .sort((a, b) => a.n - b.n);
  const rare = ranked.filter((x) => x.n < 2);
  const use = rare.length ? rare : ranked.slice(0, Math.min(6, ranked.length));
  return pick(rng, use.map((x) => x.w));
}

function lemmaOf(text) {
  const w = String(text || "");
  if (!w) return w;
  if (INFLECT[w]) return w;
  for (const [base, forms] of Object.entries(INFLECT)) {
    if (forms.includes(w)) return base;
  }
  if (w.endsWith("て") && INFLECT[`${w.slice(0, -1)}る`]) return `${w.slice(0, -1)}る`;
  if (w.endsWith("た") && INFLECT[`${w.slice(0, -1)}る`]) return `${w.slice(0, -1)}る`;
  if (w.endsWith("ない") && INFLECT[`${w.slice(0, -2)}る`]) return `${w.slice(0, -2)}る`;
  return w;
}

function neighborsOf(text) {
  const base = lemmaOf(text);
  const skip = new Set([text, base, ...(INFLECT[base] || [])]);
  const lists = [LEXICON && LEXICON[text], LEXICON && LEXICON[base], THESAURUS[text], THESAURUS[base]];
  const out = [];
  const seen = new Set();
  for (const list of lists) {
    for (const syn of list || []) {
      if (!syn || skip.has(syn) || seen.has(syn)) continue;
      if (lemmaOf(syn) === base) continue;
      seen.add(syn);
      out.push(syn);
    }
  }
  return out;
}

function contentSeeds(list) {
  return (list || []).filter((w) => w && w.length >= 2 && !/^(する|ある|いる|なる|ない|こと|もの|よう)$/.test(w));
}

function oneSynonym(text, rng) {
  const list = neighborsOf(text);
  if (!list.length) {
    askOpenSynonyms(text);
    return null;
  }
  return pick(rng, list);
}

function rewriteLine(parts, rng, intensity) {
  if (intensity <= 0) {
    return (parts || [])
      .filter((tok) => tok && tok.text)
      .map((tok) => ({ text: tok.text, kind: tok.kind, origin: tok.origin || tok.text }));
  }
  const p = Math.min(0.78, 0.2 + intensity * 0.2);
  return (parts || [])
    .map((tok) => {
      if (!tok || !tok.text) return null;
      if (tok.kind === "particle") {
        const text = rng() < 0.28 + intensity * 0.1 ? swapClearParticle(tok.text, rng, intensity >= 2) : tok.text;
        return { text, kind: "particle" };
      }
      const origin = tok.origin || tok.text;
      if (rng() >= p) return { text: origin, kind: "word", origin };
      const syn = oneSynonym(origin, rng);
      return { text: syn || origin, kind: "word", origin };
    })
    .filter(Boolean);
}

function lineFromPost(corpus, rng, intensity) {
  const post = pick(rng, corpus);
  if (!post?.tokens?.length) return { line: [], post: null };
  return { line: rewriteLine(post.tokens, rng, intensity), post };
}

function expandRelated(seeds, hops = 1, cap = 12) {
  const out = [];
  const seen = new Set();
  for (const seed of seeds || []) {
    for (const syn of neighborsOf(seed)) {
      if (!syn || seen.has(syn)) continue;
      seen.add(syn);
      out.push(syn);
      if (out.length >= cap) return out;
    }
  }
  return out;
}

function synonymsOf(text, hops = 1) {
  if (!text) return [];
  const bag = new Set();
  const add = (list) => {
    for (const item of list || []) {
      if (item && item !== text) bag.add(item);
    }
  };
  add(THESAURUS[text]);
  if (LEXICON && LEXICON[text]) add(LEXICON[text]);
  const stems = [text];
  const cuts = ["なかった", "ません", "ました", "られない", "ている", "てる", "でした", "だった", "させる", "される", "しない"];
  for (const cut of cuts) {
    if (text.endsWith(cut) && text.length > cut.length + 1) stems.push(text.slice(0, -cut.length));
  }
  if (text.endsWith("しない") && text.length > 3) stems.push(`${text.slice(0, -3)}する`);
  if (text.endsWith("した") && text.length > 2) stems.push(`${text.slice(0, -2)}する`);
  for (const stem of stems) {
    add(THESAURUS[stem]);
    if (LEXICON && LEXICON[stem]) add(LEXICON[stem]);
    if (stem !== text && THESAURUS[stem]) bag.add(stem);
  }
  if (hops > 1) {
    for (const syn of [...bag]) {
      add(THESAURUS[syn]);
      if (LEXICON && LEXICON[syn]) add(LEXICON[syn]);
    }
  }
  if (bag.size < 2) askOpenSynonyms(text);
  return [...bag].filter((s) => s !== text).slice(0, hops > 1 ? 28 : 16);
}

const synonymMiss = new Set();
function askOpenSynonyms(text) {
  if (!text || synonymMiss.has(text) || THESAURUS[text] || (LEXICON && LEXICON[text])) return;
  synonymMiss.add(text);
  fetch(`/api/synonyms?q=${encodeURIComponent(text)}`)
    .then((res) => res.json())
    .then((data) => {
      const syns = (data.syns || []).filter((s) => s && s !== text);
      if (!syns.length) return;
      THESAURUS[text] = syns;
      for (const syn of syns) {
        if (!THESAURUS[syn]) THESAURUS[syn] = [text];
        else if (!THESAURUS[syn].includes(text)) THESAURUS[syn].push(text);
      }
    })
    .catch(() => {});
}

function relatedFromCorpus(text, words) {
  const chars = [...text].filter((ch) => /[一-龯]/.test(ch));
  if (!chars.length) return [];
  return words
    .map((w) => (typeof w === "string" ? w : w && w.text))
    .filter((w) => w && w !== text && chars.some((ch) => w.includes(ch)));
}

function tokenize(text) {
  const cleaned = text.replace(/\s+/g, " ").trim();
  if (!cleaned) return [];
  const chunks = cleaned.split(/([。、「」『』（）()！？!?、,.…・\s]+)/).filter(Boolean);
  const out = [];
  for (const chunk of chunks) {
    if (/^[。、「」『』（）()！？!?、,.…・\s]+$/.test(chunk)) continue;
    if (/^[A-Za-z0-9'’-]+$/.test(chunk)) {
      out.push({ text: chunk, kind: "word" });
      continue;
    }
    splitJapanese(chunk, out);
  }
  return out.filter((t) => t.text && t.text.length);
}

function longestSense(s) {
  const limit = Math.min(s.length, 12);
  for (let n = limit; n >= 2; n--) {
    if (SENSE_SET.has(s.slice(0, n))) return s.slice(0, n);
  }
  return null;
}

function fallbackCut(s) {
  for (let i = 1; i < s.length; i++) {
    const tail = s.slice(i);
    if (peelLeadingParticle(tail)) return s.slice(0, i);
    if (AUX_ENDINGS.some((a) => tail.startsWith(a))) return s.slice(0, i);
    if (i >= 2 && longestSense(tail)) return s.slice(0, i);
  }
  return s.slice(0, Math.min(2, s.length));
}

function splitHiragana(hira, out, afterContent) {
  let rest = hira;
  let after = afterContent;
  let guard = 0;
  while (rest && guard++ < 240) {
    const before = rest;
    const word = longestSense(rest);
    if (after) {
      let p = null;
      for (const cand of PARTICLES) {
        if (rest.startsWith(cand) && rest.length >= cand.length && cand.length >= 2) {
          p = cand;
          break;
        }
      }
      if (p && (!word || p.length >= word.length)) {
        out.push({ text: p, kind: "particle" });
        rest = rest.slice(p.length);
        after = true;
        if (rest === before) rest = rest.slice(1);
        continue;
      }
    }
    if (word) {
      emitWord(out, word);
      rest = rest.slice(word.length);
      after = true;
      if (rest === before) rest = rest.slice(1);
      continue;
    }
    if (after && CLEAR_PARTICLES.has(rest[0])) {
      out.push({ text: rest[0], kind: "particle" });
      rest = rest.slice(1);
      after = true;
      continue;
    }
    if (after) {
      let aux = null;
      for (const a of AUX_ENDINGS) {
        if (rest.startsWith(a)) {
          aux = a;
          break;
        }
      }
      if (aux) {
        out.push({ text: aux, kind: "word" });
        rest = rest.slice(aux.length);
        after = true;
        if (rest === before) rest = rest.slice(1);
        continue;
      }
    }
    const cut = fallbackCut(rest) || rest.slice(0, 1);
    emitWord(out, cut);
    rest = rest.slice(cut.length);
    after = true;
    if (rest === before) rest = rest.slice(1);
  }
}

function emitKanji(out, text) {
  if (text.length <= 2 || THESAURUS[text] || SENSE_SET.has(text)) {
    emitWord(out, text);
    return;
  }
  let i = 0;
  while (i < text.length) {
    const left = text.length - i;
    const n = left === 3 ? 2 : Math.min(2, left);
    emitWord(out, text.slice(i, i + n));
    i += n;
  }
}

function splitJapanese(chunk, out) {
  const runs = scriptRuns(chunk);
  let afterContent = false;
  for (const run of runs) {
    if (run.script === "kanji") {
      emitKanji(out, run.text);
      afterContent = true;
      continue;
    }
    if (run.script === "kata" || run.script === "latin") {
      emitWord(out, run.text);
      afterContent = true;
      continue;
    }
    if (run.script === "hira") {
      splitHiragana(run.text, out, afterContent);
      afterContent = true;
    }
  }
}

function scriptOf(ch) {
  if (/[一-龯々〆ヵヶ]/.test(ch)) return "kanji";
  if (/[ぁ-ん]/.test(ch)) return "hira";
  if (/[ァ-ヶー]/.test(ch)) return "kata";
  if (/[A-Za-z0-9]/.test(ch)) return "latin";
  return "other";
}

function scriptRuns(text) {
  const runs = [];
  for (const ch of text) {
    const script = scriptOf(ch);
    const last = runs[runs.length - 1];
    if (last && last.script === script) last.text += ch;
    else runs.push({ script, text: ch });
  }
  return runs;
}

function peelLeadingParticle(hira) {
  for (const p of PARTICLES) {
    if (hira.startsWith(p) && hira.length > p.length) return p;
  }
  return null;
}

function peelTrailingParticle(hira) {
  for (const p of PARTICLES) {
    if (hira.endsWith(p) && hira.length > p.length) return p;
  }
  return null;
}

function emitWord(out, text) {
  if (!text) return;
  const prev = out[out.length - 1];
  if (prev && prev.kind === "word" && /[一-龯]$/.test(prev.text) && /^[ぁ-ん]+$/.test(text) && text.length <= 2) {
    prev.text += text;
    return;
  }
  out.push({ text, kind: "word" });
}

function hydratePost(p) {
  const text = String(p.text || "").trim();
  if (!text) return null;
  return {
    id: p.id || `${p.t || Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
    authorId: p.authorId || p.guest || "river",
    text,
    tokens: tokenize(text),
    t: Number(p.t) || Date.now(),
  };
}

function loadPosts() {
  try {
    const raw = JSON.parse(localStorage.getItem(STORE_KEY) || "[]");
    const cutoff = Date.now() - 24 * 60 * 60 * 1000;
    return raw
      .map(hydratePost)
      .filter((p) => p && p.t > cutoff)
      .slice(-120);
  } catch {
    return [];
  }
}

function savePosts(posts) {
  localStorage.setItem(STORE_KEY, JSON.stringify(posts.slice(-120)));
}

function seedLocalPosts() {
  if (loadPosts().length) return;
  const now = Date.now();
  savePosts(
    SEED_TEXTS.map((text, i) =>
      hydratePost({
        id: `seed-${i}`,
        authorId: "river",
        text,
        t: now - (i + 3) * 60_000,
      }),
    ).filter(Boolean),
  );
}

async function pullRemotePosts() {
  try {
    const res = await fetch("/api/posts");
    if (!res.ok) return;
    const data = await res.json();
    const remote = (data.posts || []).map(hydratePost).filter(Boolean);
    if (!remote.length) return;
    const byId = new Map(loadPosts().map((p) => [p.id, p]));
    for (const post of remote) byId.set(post.id, post);
    savePosts([...byId.values()].sort((a, b) => a.t - b.t));
  } catch {
    /* static host */
  }
}

function publishPost(post) {
  fetch("/api/posts", {
    method: "POST",
    headers: { "Content-Type": "application/json" },
    body: JSON.stringify({ text: post.text, guest: post.authorId }),
  }).catch(() => {});
}

function contemporaneous(posts, around = Date.now()) {
  return posts.filter((p) => Math.abs(p.t - around) <= WINDOW_MS);
}

function otherFirst(list, rng, author) {
  const others = list.filter((x) => x.authorId !== author);
  const pool = others.length && rng() < 0.72 ? others : list;
  return pick(rng, pool);
}

function swapClearParticle(text, rng, wild = false) {
  if (!CLEAR_PARTICLES.has(text)) return text;
  const family = PARTICLE_SWAP[text] || ALL_CLEAR;
  const pool = wild ? ALL_CLEAR.filter((p) => p !== text) : family.filter((p) => p !== text);
  if (!pool.length) return text;
  return pick(rng, pool);
}

function permuteParticles(parts, rng, wild = false) {
  return parts.map((part) => {
    if (part.kind !== "particle") return { ...part };
    return { text: swapClearParticle(part.text, rng, wild), kind: "particle" };
  });
}

const INFLECT = {
  する: ["しない", "した", "して", "しよう", "できない", "せず"],
  しない: ["する", "しなかった", "せず", "できない"],
  見る: ["見ない", "見た", "見て", "見よう", "見えない"],
  聞く: ["聞かない", "聞いた", "聞いて", "聞こえない"],
  言う: ["言わない", "言った", "言って", "言えない"],
  行く: ["行かない", "行った", "行って", "行けない"],
  来る: ["来ない", "来た", "来て", "来られない"],
  くる: ["こない", "きた", "きて"],
  なる: ["ならない", "なった", "なって", "なれない"],
  ある: ["ない", "あった", "あって", "ありえない"],
  いる: ["いない", "いた", "いて"],
  思う: ["思わない", "思った", "思って", "思えない"],
  わかる: ["わからない", "わかった", "わかって"],
  流れる: ["流れない", "流れた", "流れて"],
  拾う: ["拾わない", "拾った", "拾って"],
  置く: ["置かない", "置いた", "置いて"],
  沈む: ["沈まない", "沈んだ", "沈んで"],
  漂う: ["漂わない", "漂った", "漂って"],
  消える: ["消えない", "消えた", "消えて"],
  生む: ["生まない", "生んだ", "生んで"],
  知る: ["知らない", "知った", "知って"],
  見える: ["見えない", "見えた", "見えて"],
  できる: ["できない", "できた", "できて"],
  だ: ["ではない", "だった", "でなく"],
  です: ["ではない", "でした", "ではありません"],
};

function linkInflectToThesaurus() {
  /* Inflections stay in INFLECT; they are not treated as synonyms. */
}

const GODAN_END = {
  う: { nai: "わない", ta: "った", te: "って" },
  く: { nai: "かない", ta: "いた", te: "いて" },
  ぐ: { nai: "がない", ta: "いだ", te: "いで" },
  す: { nai: "さない", ta: "した", te: "して" },
  つ: { nai: "たない", ta: "った", te: "って" },
  ぬ: { nai: "なない", ta: "んだ", te: "んで" },
  ぶ: { nai: "ばない", ta: "んだ", te: "んで" },
  む: { nai: "まない", ta: "んだ", te: "んで" },
};

function wordRole(text) {
  const w = lemmaOf(String(text || ""));
  if (!w) return "N";
  if (INFLECT[w] || /する$/.test(w)) return "V";
  if (/(る|う|く|ぐ|す|つ|む|ぬ|ぶ)$/.test(w) && w.length >= 2) return "V";
  if (/(ない|かった)$/.test(w)) return "A";
  if (/い$/.test(w) && w.length >= 2 && !/(まい|たい)$/.test(w)) return "A";
  return "N";
}

function inflectWord(text, rng) {
  const w = String(text || "");
  if (!w) return w;
  if (INFLECT[w]) return pick(rng, INFLECT[w]) || w;
  if (w.endsWith("する") && w.length > 2) {
    const stem = w.slice(0, -2);
    return stem + (pick(rng, ["しない", "した", "して", "できない"]) || "しない");
  }
  if (w.endsWith("い") && w.length >= 2 && wordRole(w) === "A") {
    const stem = w.slice(0, -1);
    return stem + (pick(rng, ["くない", "かった", "くて", "ければ"]) || "くない");
  }
  if (w.endsWith("る") && w.length >= 2) {
    const stem = w.slice(0, -1);
    if (rng() < 0.65) return stem + (pick(rng, ["ない", "た", "て", "よう"]) || "ない");
    return stem + (pick(rng, ["らない", "った", "って"]) || "らない");
  }
  const last = w.slice(-1);
  const g = GODAN_END[last];
  if (g && w.length >= 2) {
    const stem = w.slice(0, -1);
    const form = pick(rng, [g.nai, g.ta, g.te]);
    return form ? stem + form : w;
  }
  return w;
}

function wobbleWord(text, rng, intensity) {
  let w = text == null ? "" : String(text);
  if (!w) return w;
  const syn = expandRelated([w], 1, 12);
  const fresh = pickFresh(rng, syn);
  if (fresh && rng() < 0.5 + intensity * 0.1) w = fresh;
  if (rng() < 0.08) w = inflectWord(w, rng);
  return w;
}

function splitPoolByRole(pool) {
  const N = [];
  const V = [];
  const A = [];
  const seen = new Set();
  for (const item of pool || []) {
    const text = item && item.text ? item.text : item;
    if (!text) continue;
    const role = wordRole(text);
    const key = `${role}:${lemmaOf(text)}`;
    if (seen.has(key)) continue;
    seen.add(key);
    if (role === "V") V.push(text);
    else if (role === "A") A.push(text);
    else N.push(text);
  }
  return { N, V, A };
}

const SENTENCE_PATTERNS = [
  ["N", "は", "N", "を", "V"],
  ["N", "が", "A"],
  ["N", "の", "N", "に", "V"],
  ["N", "は", "N", "で", "V"],
  ["N", "を", "V", "て", "V"],
  ["N", "が", "N", "を", "V"],
  ["N", "は", "まだ", "V"],
  ["N", "から", "N", "が", "V"],
  ["A", "N", "が", "V"],
  ["N", "は", "N", "ではない"],
];

function takeRole(bags, role, rng, intensity) {
  const bag = bags[role] && bags[role].length ? bags[role] : bags.N.length ? bags.N : bags.V.length ? bags.V : bags.A;
  const raw = pick(rng, bag) || "ことば";
  const cloud = expandRelated([raw], 1, 12);
  const chosen = pickFresh(rng, cloud) || raw;
  if (rng() < 0.08) return inflectWord(chosen, rng);
  return chosen;
}

function assembleSentence(pool, corpus, rng, intensity) {
  const fromPosts = (corpus || []).flatMap((p) => (p.tokens || []).filter((t) => t.kind === "word").map((t) => t.text));
  const fromPool = (pool || []).map((t) => t.text || t).filter(Boolean);
  const bags = splitPoolByRole([...fromPosts, ...fromPool]);
  const pattern = pick(rng, SENTENCE_PATTERNS) || SENTENCE_PATTERNS[0];
  const line = [];
  for (const slot of pattern) {
    if (slot === "N" || slot === "V" || slot === "A") {
      line.push({ text: takeRole(bags, slot, rng, intensity), kind: "word" });
    } else {
      line.push({ text: slot, kind: slot === "まだ" || slot === "ではない" ? "word" : "particle" });
    }
  }
  if (intensity >= 2 && rng() < 0.12) {
    const last = line[line.length - 1];
    if (last && last.kind === "word") last.text = inflectWord(last.text, rng);
  }
  return line.filter((p) => p && p.text);
}

function fillWord(original, wordPool, rng, intensity) {
  const base = original == null ? "" : String(original);
  if (intensity <= 0) return base;
  const seeds = [base];
  const cloud = expandRelated(seeds, 1, 12);
  const fresh = pickFresh(rng, cloud);
  if (fresh) return rng() < 0.2 ? inflectWord(fresh, rng) : fresh;
  return wobbleWord(base, rng, intensity);
}

function automaticLine(skeleton, wordPool, rng, intensity) {
  return skeleton.map((tok) => {
    if (tok.kind === "particle") {
      return { text: swapClearParticle(tok.text, rng, intensity >= 2), kind: "particle" };
    }
    return { text: fillWord(tok.text, wordPool, rng, intensity), kind: "word" };
  });
}

function exquisiteCorpse(aParts, bParts, rng, intensity) {
  const skeleton = aParts.length >= bParts.length ? aParts : bParts;
  const donor = (skeleton === aParts ? bParts : aParts).filter((t) => t.kind === "word");
  const pool = [...donor, ...skeleton.filter((t) => t.kind === "word")];
  let takeDonor = rng() > 0.5;
  return skeleton.map((tok) => {
    if (tok.kind === "particle") {
      return { text: swapClearParticle(tok.text, rng, intensity >= 1), kind: "particle" };
    }
    const source = takeDonor && donor.length ? pick(rng, donor).text : tok.text;
    takeDonor = !takeDonor;
    return { text: fillWord(source, pool, rng, intensity), kind: "word" };
  });
}

function matePair(aText, bText, rng, intensity) {
  const a0 = aText == null ? "" : String(aText);
  const b0 = bText == null ? "" : String(bText);
  const glue = swapClearParticle(pick(rng, ALL_CLEAR) || "の", rng, intensity >= 2);
  const a = fillWord(a0, [{ text: b0 }], rng, Math.min(intensity, 2)) || a0;
  const b = fillWord(b0, [{ text: a0 }], rng, Math.min(intensity, 2)) || b0;
  const fused =
    a.slice(0, Math.max(1, Math.ceil(a.length / 2))) + b.slice(-Math.max(1, Math.ceil(b.length / 2)));
  const syn = synonymsOf(a)[0] || synonymsOf(b)[0];
  if (intensity <= 1) {
    return [
      { text: a, kind: "word" },
      { text: glue, kind: "particle" },
      { text: b, kind: "word" },
    ];
  }
  const phrase = tokenize(a + glue + b);
  const kids = phrase.length
    ? phrase.slice(0, 5)
    : [
        { text: a, kind: "word" },
        { text: glue, kind: "particle" },
        { text: b, kind: "word" },
      ];
  if (intensity >= 3) {
    const extra = tokenize(fused);
    kids.push(...(extra.length ? extra : [{ text: fused, kind: "word" }]));
  } else if (rng() < 0.6) {
    kids.push({ text: fused, kind: "word" });
  }
  if (syn && rng() < 0.25) kids.push({ text: syn, kind: "word" });
  return kids.filter((p) => p && p.text).slice(0, intensity >= 3 ? 3 : 2);
}

function countText(text) {
  return textCount.get(text) || 0;
}

function bumpText(text, d) {
  if (!text) return;
  const n = (textCount.get(text) || 0) + d;
  if (n <= 0) textCount.delete(text);
  else textCount.set(text, n);
}

function uniqueWord(rng, pool, intensity) {
  const seeds = contentSeeds((pool || []).map((p) => p.text || p));
  const uniq = [];
  const seen = new Set();
  for (const w of seeds) {
    const key = lemmaOf(w);
    if (seen.has(key)) continue;
    seen.add(key);
    uniq.push(w);
  }
  const seed = pick(rng, uniq) || pick(rng, (pool || []).map((p) => p.text || p)) || "ことば";
  const cloud = expandRelated([seed], 1, 12);
  const hit = pickFresh(rng, cloud) || seed;
  return { text: hit, kind: "word" };
}

function inventFragment(pool, rng, intensity) {
  return uniqueWord(rng, pool, intensity);
}

function inventLine(pool, corpus, rng, intensity) {
  return lineFromPost(corpus, rng, intensity).line;
}

function placeBreeding(left, right, children, y, rng, extra) {
  const cx = width * (0.28 + rng() * 0.52);
  const parentExtra = { ...extra, child: false };
  createToken(left, cx - 46, y, parentExtra);
  createToken(right, cx + 46, y, parentExtra);
  children.slice(0, 2).forEach((part, i) => {
    createToken(part, cx + (i - (children.length - 1) / 2) * 28, y + 32 + Math.min(i, 3) * 14, {
      ...extra,
      echo: true,
      child: true,
    });
  });
}

function createToken(part, x, worldY, extra = {}) {
  if (!part || !part.text || !wordsLayer) return null;
  if (!extra.sourced && extra.echo && !extra.emitter && countText(part.text) >= 2) return null;
  const el = document.createElement("span");
  const echo = extra.echo || part.kind === "echo";
  const kind = echo ? "word" : part.kind;
  el.className = `chip is-${kind}${extra.alien ? " is-alien" : ""}${echo ? " is-echo" : ""}${extra.child ? " is-child" : ""}${extra.decay ? " is-decay" : ""}${extra.emitter ? " is-emitter" : ""}`;
  el.textContent = part.text;

  const px = Math.max(56, Math.min(Math.max(width, 320) - 56, x));
  const py = Math.max(48, worldY);
  const near = py > scrollY - height * 0.2 && py < scrollY + Math.max(height, 1) * 1.2;
  el.style.opacity = "0";
  el.style.transform = `translate(${px}px, ${py - scrollY}px) translate(-50%, -50%) rotate(0deg)`;
  if (!near) el.style.display = "none";
  wordsLayer.appendChild(el);

  const token = {
    id: ++tokenSeq,
    text: part.text,
    kind,
    echo,
    x: px,
    worldY: py,
    vx: extra.vx || 0,
    vy: extra.vy || 0,
    rot: (Math.random() - 0.5) * 8,
    spin: (Math.random() - 0.5) * 0.05,
    rotWobble: 0.00018 + Math.random() * 0.0004,
    arcSign: Math.random() < 0.5 ? -1 : 1,
    arcAmp: Math.pow(Math.random(), 1.4) * 0.28,
    arcFreq: 0.00014 + Math.random() * 0.00032,
    born: performance.now(),
    pulse: Math.random() * Math.PI * 2,
    drift: 0.4 + Math.random() * 0.7,
    phase: Math.random() * 1000,
    origin: extra.origin || part.origin || part.text,
    stage: extra.stage != null ? extra.stage : extra.depthBand || 0,
    authorId: extra.authorId || "",
    postId: extra.postId || "",
    alien: Boolean(extra.alien),
    depthBand: extra.depthBand || 0,
    glow: 0,
    decay: Boolean(extra.decay),
    life: extra.life != null ? extra.life : extra.decay ? 0.45 + Math.random() * 0.55 : 1,
    emitter: Boolean(extra.emitter),
    sourced: Boolean(extra.sourced),
    appear: 0,
    hidden: !near,
    el,
  };
  paintChip(token);
  tokens.push(token);
  bumpText(token.text, 1);
  if (!packing) cullIfNeeded();
  return token;
}

function paintChip(t, force) {
  if (!t?.el) return;
  const depth = depthAt(t.worldY);
  const band = (depth * 8) | 0;
  if (!force && t.paintBand === band && !t.decay) return;
  t.paintBand = band;
  const water = 230 - depth * 72;
  const ink = t.kind === "particle" ? 78 : 90;
  const shade = Math.round(Math.max(64, water - ink));
  t.el.style.color = `rgb(${shade}, ${shade}, ${Math.max(0, shade - 4)})`;
}

function retire(token) {
  bumpText(token.text, -1);
  token.el.remove();
  const idx = tokens.indexOf(token);
  if (idx >= 0) tokens.splice(idx, 1);
}

function cullIfNeeded() {
  const viewMid = scrollY + height * 0.5;
  const viewTop = scrollY - height * 0.1;
  const viewBot = scrollY + height * 1.1;
  while (tokens.length > MAX_TOKENS) {
    let worst = null;
    let worstScore = -1;
    for (const t of tokens) {
      const onScreen = t.worldY > viewTop && t.worldY < viewBot;
      if (onScreen && t.sourced) continue;
      const dist = Math.abs(t.worldY - viewMid) / Math.max(height, 1);
      let score = dist;
      if (t.emitter) score *= 0.15;
      else if (t.sourced) score *= 0.4;
      else if (t.decay || t.child) score *= 1.2;
      if (onScreen) score *= 0.12;
      if (t.worldY > seaHeight - height * 1.15) score *= 0.22;
      if (score > worstScore) {
        worstScore = score;
        worst = t;
      }
    }
    if (!worst) break;
    retire(worst);
  }
}

function clearTokens() {
  for (const t of tokens) t.el.remove();
  tokens.length = 0;
  spawnQ.length = 0;
  lastSpawnAt = 0;
  textCount.clear();
  touchCool.clear();
}

function enqueueToken(part, x, worldY, extra = {}) {
  if (!part || !part.text) return;
  spawnQ.push({ part, x, y: Math.max(48, worldY), extra });
}

function placePhrase(parts, y, rng, extra) {
  const list = (parts || []).filter((p) => p && p.text);
  if (!list.length) return;
  const n = list.length;
  const inner = Math.max(200, width - 120);
  const natural = (n - 1) * (n < 5 ? 70 : 58);
  const used = n < 5 ? natural : Math.min(inner, Math.max(natural, inner * 0.68));
  const origin = 60 + rng() * Math.max(0, inner - used);
  list.forEach((part, i) => {
    const u = n === 1 ? 0.5 : i / (n - 1);
    const x = origin + u * used;
    enqueueToken(part, x, y + Math.sin(i * 0.65) * 7, {
      ...extra,
      origin: part.origin || extra.origin,
      postId: extra.postId,
    });
  });
}

function flushSpawns(now) {
  if (scrolling || !spawnQ.length) return;
  if (now - lastSpawnAt < 280) return;
  const viewTop = scrollY - 30;
  const viewBot = scrollY + height + 50;
  const idx = spawnQ.findIndex((job) => job.y > viewTop && job.y < viewBot);
  if (idx < 0) return;
  const job = spawnQ.splice(idx, 1)[0];
  lastSpawnAt = now;
  createToken(job.part, job.x, job.y, job.extra);
}

function scatterPhrase(parts, extra = {}) {
  const list = (parts || []).filter((p) => p && p.text);
  if (!list.length) return;
  const rng = Math.random;
  placePhrase(list, height * (0.26 + rng() * 0.16), rng, extra);
}

function rememberPost(post) {
  seaCorpus = [...seaCorpus, post].slice(-12);
  const words = (post.tokens || []).filter((t) => t.kind === "word");
  seaWords = [...seaWords, ...words].slice(-80);
}

function ingestPost(post) {
  if (!post) return;
  rememberPost(post);
  if (!tokens.length) {
    rebuildSea();
    return;
  }
  scatterPhrase(post.tokens || [], {
    authorId: post.authorId,
    postId: post.id,
    depthBand: 0,
    stage: 0,
    sourced: true,
  });
  sowInputThroughSea(post);
  spawnRipple(width * 0.5, height * 0.42, 1.2);
  window.scrollTo({ top: 0, behavior: "smooth" });
}

function sowInputThroughSea(post) {
  if (!post?.tokens?.length) return;
  [1.25, 2.6, 4.4, 0.4].forEach((spot, i) => {
    const y = i < 3 ? height * spot : seaHeight - height * spot;
    const rng = Math.random;
    const line = rewriteLine(post.tokens, rng, mutateLevel(y));
    placePhrase(line, y, rng, {
      authorId: post.authorId,
      postId: post.id,
      alien: true,
      depthBand: mutateLevel(y),
      stage: 0,
    });
  });
}

function rebuildSea() {
  try {
    rebuildSeaInner();
  } catch (err) {
    console.error(err);
  }
}

function rebuildSeaInner() {
  if (width < 80 || height < 80) return;
  const posts = loadPosts();
  packing = true;
  clearTokens();
  seaHeight = height * DEPTH_SCREENS;
  const abyss = document.getElementById("abyss");
  if (abyss) abyss.style.height = `${seaHeight}px`;
  packing = false;
  if (!posts.length) {
    seaWords = [];
    seaCorpus = [];
    return;
  }

  packing = true;
  const nearby = contemporaneous(posts, posts[posts.length - 1].t);
  const corpus = nearby.length ? nearby : posts.slice(-8);
  seaCorpus = corpus;

  const shown = corpus.slice(-4);
  shown.forEach((post, pi) => {
    const rng = mulberry32(hashStr(post.id + "surface"));
    const baseY = height * (0.22 + (pi / Math.max(shown.length, 1)) * 0.28);
    placePhrase(post.tokens || [], baseY, rng, {
      authorId: post.authorId,
      postId: post.id,
      depthBand: 0,
      stage: 0,
      sourced: true,
    });
  });

  const words = corpus.flatMap((p) =>
    (p.tokens || []).filter((t) => t.kind === "word").map((t) => ({ ...t, postId: p.id, authorId: p.authorId })),
  );
  seaWords = words.length ? words : [{ text: "ことば", kind: "word" }];
  seedAbyss(corpus);
  packing = false;
  cullIfNeeded();
  spawnedBand = -1;
}

function seedAbyss(corpus) {
  const startY = height * 1.18;
  const floorY = seaHeight - height * 0.24;
  const ys = [];
  for (let y = startY; y < floorY; y += height * 0.5) ys.push(y);
  for (const floor of [seaHeight - height * 0.7, seaHeight - height * 0.38]) {
    if (!ys.some((y) => Math.abs(y - floor) < height * 0.16)) ys.push(floor);
  }
  ys.sort((a, b) => a - b);
  const ids = corpus.map((p) => p.id).join("|");

  ys.forEach((y, layer) => {
    const intensity = mutateLevel(y);
    const rng = mulberry32(hashStr(ids + "abyss" + Math.round(y)));
    const { line, post } = lineFromPost(corpus, rng, intensity);
    if (!line.length) return;
    placePhrase(line, y + rng() * 8, rng, {
      alien: true,
      depthBand: intensity,
      stage: intensity,
      postId: post?.id || "",
      authorId: post?.authorId || "",
    });
  });
}

function flow(x, y, t, depth) {
  const slow = 1 - depth * 0.62;
  const a = Math.sin(y * 0.0022 + t * 0.00011 + x * 0.0011) * 0.22 * slow;
  const b = Math.cos(x * 0.0018 - t * 0.00008 + y * 0.0009) * 0.16 * slow;
  const c = Math.sin((x * 0.4 + y) * 0.0012 + t * 0.00005) * 0.1 * slow;
  return { x: a + c * 0.6, y: b * 0.85 + Math.abs(a) * 0.04 };
}

function spawnRipple(x, y, scale = 1) {
  if (scrolling || ripples.length > 4) return;
  ripples.push({ x, y, r: 10, max: 120 + 70 * scale, alpha: 0.22 * scale, life: 1 });
}

const SPEED = 1.5;
let scrolling = false;
let scrollSettle = 0;
let frameN = 0;

window.addEventListener(
  "scroll",
  () => {
    scrolling = true;
    clearTimeout(scrollSettle);
    scrollSettle = setTimeout(() => {
      scrolling = false;
    }, 140);
  },
  { passive: true },
);

function surfaceBand() {
  return Math.max(height * 0.88, 240);
}

function isSurfaceToken(t) {
  return Boolean(t && t.sourced && (t.depthBand || 0) === 0 && t.worldY < surfaceBand());
}

function depthAt(worldY) {
  if (seaHeight <= height) return 0;
  return Math.max(0, Math.min(1, worldY / (seaHeight - height * 0.2)));
}

function mutateLevel(worldY) {
  const d = depthAt(worldY);
  if (d < 0.13) return 0;
  return Math.min(3, 1 + Math.floor((d - 0.13) * 3.6));
}

function updateTokens(dt, now) {
  const margin = 48;
  const viewTop = scrollY - height * 0.15;
  const viewBot = scrollY + height * 1.15;
  const busy = scrolling;
  const dying = [];

  for (let i = 0; i < tokens.length; i++) {
    const t = tokens[i];
    if (!t.el) continue;
    const near = t.worldY > viewTop && t.worldY < viewBot;

    if (t.decay) {
      t.life -= dt * (busy ? 0.0002 : 0.00014);
      if (t.life <= 0) {
        dying.push(t);
        continue;
      }
    }

    if (!near) {
      if (!busy && !isSurfaceToken(t)) t.worldY += dt * 0.00008;
      if (!t.hidden) {
        t.el.style.display = "none";
        t.hidden = true;
      }
      continue;
    }

    if (busy) {
      t.el.style.transform = `translate3d(${t.x}px, ${t.worldY - scrollY}px, 0) translate(-50%, -50%)`;
      if (t.hidden) {
        t.el.style.display = "";
        t.hidden = false;
      }
      continue;
    }

    t.vx *= 0.986;
    t.vy *= 0.986;
    t.x += t.vx * dt * 0.03 * SPEED + Math.sin(now * 0.00028 + t.pulse) * 0.012 * t.drift * SPEED;
    t.worldY += t.vy * dt * 0.03 * SPEED;
    if (isSurfaceToken(t)) {
      const cap = surfaceBand();
      if (t.worldY > cap) {
        t.worldY = cap;
        t.vy = 0;
      }
    } else if (t.worldY < seaHeight - height) {
      t.worldY += dt * 0.00008 * SPEED;
    }
    if (t.x < margin) {
      t.x = margin;
      t.vx = Math.abs(t.vx) * 0.3;
    } else if (t.x > width - margin) {
      t.x = width - margin;
      t.vx = -Math.abs(t.vx) * 0.3;
    }
    if (t.worldY < 72) t.worldY = 72;
    const maxY = seaHeight - height * 0.22;
    if (t.worldY > maxY) {
      t.worldY = maxY;
      t.vy = -Math.abs(t.vy) * 0.3;
    }

    if (t.appear < 1) {
      t.appear = Math.min(1, t.appear + dt * 0.0007);
      t.el.style.opacity = String(t.decay ? t.appear * Math.max(0.55, t.life) : t.appear);
    } else if (t.decay) {
      t.el.style.opacity = String(Math.max(0.55, t.life));
    }

    t.el.style.transform = `translate3d(${t.x}px, ${t.worldY - scrollY}px, 0) translate(-50%, -50%)`;
    if (frameN % 3 === 0) paintChip(t);
    if (t.hidden) {
      t.el.style.display = "";
      t.hidden = false;
    }
  }

  for (const t of dying) retire(t);
  if (!busy && frameN % 8 === 0) interfere(dt, now);
  if (!busy && frameN % 12 === 0) driftThesaurus(now);
  if (!busy && frameN % 15 === 0) {
    for (const t of tokens) {
      if (t.hidden || isSurfaceToken(t)) continue;
      if (t.worldY < viewTop || t.worldY > viewBot) continue;
      sinkMutate(t, depthAt(t.worldY));
    }
  }
}

let lastThesaurusPulse = 0;
function sinkMutate(token, depth) {
  if (isSurfaceToken(token) || depth < 0.13) return;
  const stage = mutateLevel(token.worldY);
  if (stage <= (token.stage || 0) || stage < 1) return;
  token.stage = stage;
  const rng = Math.random;
  if (token.kind === "particle") {
    if (stage >= 2) setTokenText(token, swapClearParticle(token.text, rng, stage >= 4));
    return;
  }
  const origin = token.origin || token.text;
  const next = oneSynonym(origin, rng);
  if (next && next !== token.text) setTokenText(token, next);
}

function driftThesaurus(now) {
  const viewDepth = depthAt(scrollY + height * 0.55);
  if (viewDepth < 0.14) return;
  const wait = 2600 - Math.min(viewDepth, 0.55) * 1100 + (viewDepth > 0.75 ? 900 : 0);
  if (now - lastThesaurusPulse < wait) return;
  lastThesaurusPulse = now;
  const vis = tokens.filter((t) => t.kind === "word" && !t.hidden && t.el && !isSurfaceToken(t) && depthAt(t.worldY) >= 0.13);
  if (!vis.length) return;
  const weights = vis.map((t) => Math.pow(depthAt(t.worldY), 1.6));
  const sum = weights.reduce((a, b) => a + b, 0);
  let r = Math.random() * sum;
  let t = vis[0];
  for (let i = 0; i < vis.length; i++) {
    r -= weights[i];
    if (r <= 0) {
      t = vis[i];
      break;
    }
  }
  const depth = depthAt(t.worldY);
  if (Math.random() > 0.15 + depth * 0.55) return;
  const next = oneSynonym(t.origin || t.text, Math.random);
  if (next && next !== t.text) setTokenText(t, next);
}

function setTokenText(token, text) {
  if (!text || !token || text === token.text) return;
  bumpText(token.text, -1);
  token.text = text;
  bumpText(text, 1);
  if (token.el) token.el.textContent = text;
  token.glow = 1;
}

function pairKey(a, b) {
  return a.id < b.id ? `${a.id}:${b.id}` : `${b.id}:${a.id}`;
}

function spawnOffspring(a, b) {
  const midY = (a.worldY + b.worldY) / 2;
  if (midY < height * 1.05) return;
  const depth = depthAt(midY);
  if (depth < 0.22 || depth > 0.76) return;
  const post = seaCorpus.find((p) => p.id === a.postId || p.id === b.postId) || pick(Math.random, seaCorpus);
  if (!post?.tokens?.length) return;
  const rng = Math.random;
  const intensity = mutateLevel(midY);
  const line = rewriteLine(post.tokens, rng, intensity);
  placePhrase(line, midY + 28, rng, {
    alien: true,
    depthBand: intensity,
    postId: post.id,
    authorId: post.authorId,
  });
}

function breedByDepth() {
  if (scrolling) return;
  if (scrollY < height * 0.92) return;
  const depth = depthAt(scrollY + height * 0.5);
  if (depth < 0.13) return;
  const viewTop = scrollY + 24;
  const viewBot = scrollY + height - 130;
  const here = tokens.filter((t) => t.worldY > viewTop && t.worldY < viewBot);
  const queuedHere = spawnQ.filter((job) => job.y > viewTop && job.y < viewBot).length;
  const want = 10 + Math.floor(Math.min(depth, 1) * 12);
  if (here.length + queuedHere >= want) return;
  if (queuedHere >= 8) return;

  const rng = Math.random;
  const y = Math.max(height * 1.12, viewTop + 80 + rng() * Math.max(90, height - 240));
  const intensity = mutateLevel(y);
  const { line, post } = lineFromPost(seaCorpus, rng, intensity);
  if (!line.length) return;
  placePhrase(line, y, rng, {
    alien: true,
    depthBand: intensity,
    stage: intensity,
    postId: post?.id || "",
    authorId: post?.authorId || "",
  });
}

function interfere(dt, now) {
  const viewTop = scrollY - 40;
  const viewBot = scrollY + height + 40;
  const visible = tokens.filter((t) => t.worldY > viewTop && t.worldY < viewBot);
  visible.sort((a, b) => a.worldY - b.worldY);
  const n = visible.length;
  for (let i = 0; i < n; i++) {
    const a = visible[i];
    for (let j = i + 1; j < n; j++) {
      const b = visible[j];
      if (b.worldY - a.worldY > 120) break;
      const dx = a.x - b.x;
      const dy = a.worldY - b.worldY;
      const d = Math.hypot(dx, dy) || 1;
      const reach = a.kind === "particle" || b.kind === "particle" ? TOUCH_R_PART : TOUCH_R;
      if (d >= reach) continue;

      const nx = dx / d;
      const ny = dy / d;
      const tx = -ny;
      const ty = nx;
      const prox = 1 - d / reach;
      const swirl = 0.028 * prox * dt;
      const push = (reach - d) * 0.0065;

      a.vx += tx * swirl * 0.9 + nx * push;
      a.vy += ty * swirl * 0.9 + ny * push;
      b.vx -= tx * swirl * 0.9 + nx * push;
      b.vy -= ty * swirl * 0.9 + ny * push;

      const share = 0.08 * prox;
      const avx = a.vx;
      const avy = a.vy;
      a.vx += (b.vx - a.vx) * share;
      a.vy += (b.vy - a.vy) * share;
      b.vx += (avx - b.vx) * share;
      b.vy += (avy - b.vy) * share;

      a.spin += prox * 0.004 * (a.id % 2 ? 1 : -1);
      b.spin += prox * 0.004 * (b.id % 2 ? 1 : -1);
      a.glow = Math.max(a.glow, prox * 0.9);
      b.glow = Math.max(b.glow, prox * 0.9);

      if (d > 38) continue;
      const key = pairKey(a, b);
      const lastHit = touchCool.get(key) || 0;
      if (now - lastHit < 1440) continue;
      touchCool.set(key, now);

      if (a.kind === "word" && b.kind === "word") {
        if (isSurfaceToken(a) || isSurfaceToken(b)) continue;
        const hitDepth = depthAt((a.worldY + b.worldY) / 2);
        if (hitDepth < 0.16) continue;
        if (Math.random() < 0.28 + hitDepth * 0.2) {
          const synA = oneSynonym(a.origin || a.text, Math.random);
          const synB = oneSynonym(b.origin || b.text, Math.random);
          if (synA) setTokenText(a, synA);
          if (synB) setTokenText(b, synB);
        }
      }
    }
  }
  if (touchCool.size > 400) touchCool.clear();
}

function drawWaves(now) {
  if (!ctx) return;
  const depth = Math.max(0, Math.min(1, scrollY / Math.max(seaHeight - height, 1)));
  const g = 230 - depth * 72;
  ctx.fillStyle = `rgb(${g | 0}, ${(g + 3) | 0}, ${(g + 10) | 0})`;
  ctx.fillRect(0, 0, width, height);
  if (scrolling) return;

  const yBase = ((now * 0.0004 + scrollY * 0.04) % (height + 60)) - 30;
  ctx.beginPath();
  const step = 56;
  for (let x = -40; x <= width + 40; x += step) {
    const y = yBase + Math.sin(x * 0.006 + now * 0.00016) * 11;
    if (x === -40) ctx.moveTo(x, y);
    else ctx.lineTo(x, y);
  }
  ctx.strokeStyle = `rgba(150, 158, 168, ${0.12 * (1 - depth * 0.4)})`;
  ctx.lineWidth = 1;
  ctx.stroke();
}

function updateRipples(dt) {
  for (let i = ripples.length - 1; i >= 0; i--) {
    const r = ripples[i];
    r.r += dt * 0.028;
    r.life -= dt * 0.00045;
    if (r.life <= 0 || r.r > r.max) ripples.splice(i, 1);
  }
}

function resize() {
  dpr = 1;
  width = window.innerWidth;
  height = window.innerHeight;
  seaHeight = height * DEPTH_SCREENS;
  const abyss = document.getElementById("abyss");
  if (abyss) abyss.style.height = `${seaHeight}px`;
  if (!canvas || !ctx) return;
  canvas.width = width;
  canvas.height = height;
  canvas.style.width = `${width}px`;
  canvas.style.height = `${height}px`;
  ctx.setTransform(1, 0, 0, 1, 0, 0);
}

function releaseSentence(text) {
  const parts = tokenize(text);
  if (!parts.length) return;
  const posts = loadPosts();
  const post = {
    id: `${Date.now()}-${Math.random().toString(36).slice(2, 7)}`,
    authorId,
    text,
    tokens: parts,
    t: Date.now(),
  };
  posts.push(post);
  savePosts(posts);
  try {
    channel.postMessage({ type: "post", post });
  } catch {
    /* ignore */
  }
  publishPost(post);
  ingestPost(post);
}

const channel = new BroadcastChannel("kotobaasobi-sea");
channel.addEventListener("message", (e) => {
  if (e.data?.type !== "post" || !e.data.post) return;
  const posts = loadPosts();
  if (posts.some((p) => p.id === e.data.post.id)) return;
  posts.push(e.data.post);
  savePosts(posts);
  ingestPost(e.data.post);
});

window.addEventListener("storage", (e) => {
  if (e.key === STORE_KEY) rebuildSea();
});

let last = performance.now();
function frame(now) {
  const dt = Math.min(40, now - last);
  last = now;
  scrollY = window.scrollY || 0;
  try {
    frameN += 1;
    updateTokens(dt, now);
    flushSpawns(now);
    if (!scrolling && frameN % 16 === 0) breedByDepth();
    drawWaves(now);
  } catch (err) {
    console.error(err);
  }
  requestAnimationFrame(frame);
}

function autosize() {
  if (!input) return;
  input.style.height = "auto";
  input.style.height = `${Math.min(input.scrollHeight, 110)}px`;
}

if (form && input) {
  form.addEventListener("submit", (e) => {
    e.preventDefault();
    const text = input.value.trim();
    if (!text) return;
    releaseSentence(text);
    input.value = "";
    autosize();
  });

  input.addEventListener("input", autosize);
  input.addEventListener("keydown", (e) => {
    if (e.key === "Enter" && !e.shiftKey) {
      e.preventDefault();
      form.requestSubmit();
    }
  });
}

let resizeTimer = 0;
window.addEventListener("resize", () => {
  resize();
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => {
    if (width > 80 && height > 80) rebuildSea();
  }, 280);
});

resize();
async function loadLexicon() {
  const urls = ["/api/lexicon", "data/open-lexicon.json"];
  for (const url of urls) {
    try {
      const res = await fetch(url);
      if (!res.ok) continue;
      const data = await res.json();
      const map = data.map || data;
      if (map && typeof map === "object" && !Array.isArray(map)) {
        LEXICON = map;
        return;
      }
    } catch {
      /* try next */
    }
  }
}

async function boot() {
  linkInflectToThesaurus();
  await pullRemotePosts();
  seedLocalPosts();
  if (width > 80 && height > 80) rebuildSea();
  requestAnimationFrame(frame);
  loadLexicon();
}
boot();
