'use strict';
// ======================================================================= Файлы SD-карты FTX-1 (MemList/*.dat)
// Формат разобран на бэкапах FTX-1 (прошивка 1.13) и проверен загрузкой в трансивер:
//   0..511     — строки пробелов с CRLF
//   512..575   — заголовок «MemList  80  XXXXXXXX» (XXXXXXXX — CRC32, см. crc()) + CRLF
//   576..      — тело, каждый байт сдвинут на KEY[i % 43]
// В расшифрованном теле: битовая карта занятых каналов (2 копии, смещения 20 и 584),
// записи каналов по 89 байт; частота канала n — по смещению 3083 + (n−1)·89.
const sdFile = (() => {
  const KEY = Uint8Array.from('1e271b12111619172425291c0d0b060403010205070c0e0f181d20222a2b08090a101314151a1f21282326'.match(/../g), h => parseInt(h, 16));
  const BODY = 576, HDR = 512, REC = 89, F0 = 3083, MAP = [20, 584], CH_MAX = 999;
  const MAGIC = [0x8f, 0x93, 0xc6, 0x35];         // хвост, который трансивер «дописывает» к CRC32
  const MODE = { 0x06: 'FM', 0x07: 'FM-N', 0x04: 'AM', 0x11: 'C4FM-DN' };
  const MODE_CODE = { 'FM': 0x06, 'FM-N': 0x07, 'C4FM-DN': 0x11 };  // в эти виды можно переключать
  const CTCSS = [67.0, 69.3, 71.9, 74.4, 77.0, 79.7, 82.5, 85.4, 88.5, 91.5, 94.8, 97.4, 100.0, 103.5, 107.2, 110.9, 114.8, 118.8,
    123.0, 127.3, 131.8, 136.5, 141.3, 146.2, 151.4, 156.7, 159.8, 162.2, 165.5, 167.9, 171.3, 173.8, 177.3, 179.9, 183.5, 186.2,
    189.9, 192.8, 196.6, 199.5, 203.5, 206.5, 210.7, 218.1, 225.7, 229.1, 233.6, 241.8, 250.3, 254.1];
  // тон в файле: 1 = TSQ, 2 = ENC; в редакторе: 1 = ENC, 2 = TSQ
  const TONE_IN = { 0: 0, 1: 2, 2: 1, 3: 3 }, TONE_OUT = { 0: 0, 1: 2, 2: 1, 3: 3 };

  let CRCT = null;
  function crc32(buf, crc = 0) {
    if (!CRCT) { CRCT = new Uint32Array(256); for (let i = 0; i < 256; i++) { let c = i; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; CRCT[i] = c >>> 0; } }
    crc = ~crc >>> 0;
    for (let i = 0; i < buf.length; i++) crc = CRCT[(crc ^ buf[i]) & 0xff] ^ (crc >>> 8);
    return ~crc >>> 0;
  }
  const crc = raw => crc32(MAGIC, crc32(raw.subarray(BODY)));
  const hex8 = v => v.toString(16).toUpperCase().padStart(8, '0');
  const dec = raw => { const d = new Uint8Array(raw.length - BODY); for (let i = 0; i < d.length; i++) d[i] = (raw[BODY + i] - KEY[i % 43]) & 0xff; return d; };
  const enc = d => { const r = new Uint8Array(d.length); for (let i = 0; i < d.length; i++) r[i] = (d[i] + KEY[i % 43]) & 0xff; return r; };
  const header = raw => String.fromCharCode(...raw.subarray(HDR, BODY));
  const recStart = ch => F0 + (ch - 1) * REC - 55;
  const u32 = (d, o) => ((d[o] << 24) | (d[o + 1] << 16) | (d[o + 2] << 8) | d[o + 3]) >>> 0;
  const put32 = (d, o, v) => { d[o] = v >>> 24 & 255; d[o + 1] = v >>> 16 & 255; d[o + 2] = v >>> 8 & 255; d[o + 3] = v & 255; };
  const used = (d, ch) => (d[MAP[0] + ((ch - 1) >> 3)] >> ((ch - 1) & 7)) & 1;
  const setUsed = (d, ch, on) => MAP.forEach(m => { const o = m + ((ch - 1) >> 3), b = 1 << ((ch - 1) & 7); d[o] = on ? d[o] | b : d[o] & ~b; });

  /** Разобрать файл. Возвращает {kind, ok, crcOk, chans:[{ch,...}], d}. Бросает Error на чужой файл. */
  function parse(buf) {
    const raw = buf instanceof Uint8Array ? buf : new Uint8Array(buf);
    if (raw.length < BODY + 1000) throw new Error('Файл слишком короткий — это не бэкап FTX-1');
    const h = header(raw), m = /^(\w+)\s+(\d+)\s+([0-9A-F]{8})/i.exec(h);
    if (!m) throw new Error('Нет заголовка FTX-1 (ожидалось «MemList … CRC»)');
    const kind = m[1], crcOk = parseInt(m[3], 16) === crc(raw);
    if (kind !== 'MemList') return { kind, crcOk, chans: [], d: null, raw };
    const d = dec(raw), chans = [];
    for (let ch = 1; ch <= CH_MAX; ch++) {
      const S = recStart(ch);
      if (!used(d, ch)) { chans.push({ ch, empty: true }); continue; }
      const code = d[S], sh = d[S + 2] >> 6, tm = d[S + 3] & 3, ci = d[S + 51];
      let name = ''; for (let i = 0; i < 12; i++) name += String.fromCharCode((d[S + 59 + 2 * i] << 8) | d[S + 60 + 2 * i]);
      const split = sh === 3;
      chans.push({
        ch, empty: false, freq: u32(d, S + 55), mode: MODE[code] || `код 0x${code.toString(16).padStart(2, '0')}`,
        name: name.replace(/[\0￿]/g, '').trimEnd(),
        shift: split ? 0 : sh === 1 ? 0 : sh === 0 ? 2 : 1,     // 0x40 симплекс, 0x00 «−», 0x80 «+»
        split, tx_freq: split ? u32(d, S + 83) : 0,
        tone_mode: TONE_IN[tm], ctcss: CTCSS[ci] ?? 88.5, dcs: 23, clar: 0, rx_clar: false, tx_clar: false,
      });
    }
    return { kind, crcOk, chans, d, raw };
  }

  /** Собрать новый файл: base — результат parse(), chans — каналы из редактора. Возвращает {bytes, changed, errors}. */
  function build(base, chans) {
    if (!base?.d) throw new Error('Сначала откройте файл MemList с флешки');
    const d = base.d.slice(), errors = [], changed = [];
    const orig = Object.fromEntries(base.chans.map(c => [c.ch, c]));
    const same = (a, b) => ['empty', 'freq', 'mode', 'name', 'shift', 'split', 'tx_freq', 'tone_mode'].every(k => String(a[k] ?? '') === String(b[k] ?? ''))
      && (!(a.tone_mode === 1 || a.tone_mode === 2) || Math.abs(a.ctcss - b.ctcss) < 0.05);
    for (const c of chans) {
      const o = orig[c.ch]; if (!o || c.ch < 1 || c.ch > CH_MAX) continue;
      if ((c.empty && o.empty) || (!c.empty && !o.empty && same(c, o))) continue;
      const S = recStart(c.ch);
      if (c.empty) { d.fill(0xff, S, S + REC); setUsed(d, c.ch, false); changed.push(c.ch); continue; }
      const err = m => errors.push(`${c.ch}: ${m}`);
      let code = MODE_CODE[c.mode];
      if (code === undefined && c.mode === o.mode && !o.empty) code = d[S];          // вид не меняли — оставляем как был
      if (code === undefined) { err(`вид «${c.mode}» в файл пока писать не умею (можно FM, FM-N, C4FM-DN)`); continue; }
      if (!(c.freq >= 30e3 && c.freq < 470e6)) { err('частота вне диапазона'); continue; }
      if (c.tone_mode === 3) { err('DCS в файл пока писать не умею'); continue; }
      if (o.empty) {                                   // новый канал — чистая запись по образцу простого FM-канала
        d.fill(0, S, S + REC); d[S + 2] = 0x40; d[S + 46] = 0x04; setUsed(d, c.ch, true);
      }
      d[S] = code;
      d[S + 2] = (d[S + 2] & 0x3f) | ((c.split ? 3 : c.shift === 1 ? 2 : c.shift === 2 ? 0 : 1) << 6);
      d[S + 3] = (d[S + 3] & ~3) | TONE_OUT[c.tone_mode || 0];
      if (c.tone_mode === 1 || c.tone_mode === 2) {
        const i = CTCSS.findIndex(t => Math.abs(t - c.ctcss) < 0.05);
        if (i < 0) { err(`нет такого тона ${c.ctcss}`); continue; }
        d[S + 51] = i;
      }
      put32(d, S + 55, Math.round(c.freq));
      const nm = String(c.name || '').replace(/[^\x20-\x7e]/g, '').slice(0, 12).padEnd(12, ' ');
      for (let i = 0; i < 12; i++) { d[S + 59 + 2 * i] = 0; d[S + 60 + 2 * i] = nm.charCodeAt(i); }
      put32(d, S + 83, c.split ? Math.round(c.tx_freq || c.freq) : 0);
      changed.push(c.ch);
    }
    const raw = new Uint8Array(base.raw.length);
    raw.set(base.raw.subarray(0, BODY)); raw.set(enc(d), BODY);
    const h = header(raw), m = /^(\w+\s+\d+\s+)([0-9A-F]{8})/i.exec(h);
    const sum = hex8(crc(raw));
    for (let i = 0; i < 8; i++) raw[HDR + m[1].length + i] = sum.charCodeAt(i);
    return { bytes: raw, changed, errors };
  }

  /** Имя файла как у трансивера: ГГГГ_ММ_ДД_NN.dat */
  function fileName(n = 1) {
    const t = new Date(), p = v => String(v).padStart(2, '0');
    return `${t.getFullYear()}_${p(t.getMonth() + 1)}_${p(t.getDate())}_${p(n)}.dat`;
  }
  return { parse, build, fileName, CTCSS, _crc: crc };
})();
if (typeof module !== 'undefined') module.exports = sdFile;
