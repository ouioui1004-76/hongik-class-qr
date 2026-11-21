/*
 * Standalone QR Code SVG Generator (ISO/IEC 18004)
 * Supports Byte Mode (UTF-8), ECC Level M, Versions 1..10 (up to 213 bytes)
 */
(function (global) {
  'use strict';

  // Version table for ECC Level M: [totalCodewords, ecCodewordsPerBlock, numBlocksGroup1, dataCwGroup1, numBlocksGroup2, dataCwGroup2]
  const VER_M = [
    null,
    [26, 10, 1, 16, 0, 0],     // V1  (21x21) cap 14B
    [44, 16, 1, 28, 0, 0],     // V2  (25x25) cap 26B
    [70, 26, 1, 44, 0, 0],     // V3  (29x29) cap 42B
    [100, 18, 2, 32, 0, 0],    // V4  (33x33) cap 62B
    [134, 24, 2, 43, 0, 0],    // V5  (37x37) cap 84B
    [172, 16, 4, 27, 0, 0],    // V6  (41x41) cap 106B
    [196, 18, 4, 31, 0, 0],    // V7  (45x45) cap 122B
    [242, 22, 2, 38, 2, 39],   // V8  (49x49) cap 152B
    [292, 22, 3, 36, 2, 37],   // V9  (53x53) cap 180B
    [346, 26, 4, 43, 1, 44],   // V10 (57x57) cap 213B
  ];

  const ALIGN_POS = [
    null,
    [],
    [6, 18],
    [6, 22],
    [6, 26],
    [6, 30],
    [6, 34],
    [6, 22, 38],
    [6, 24, 42],
    [6, 26, 46],
    [6, 28, 50],
  ];

  // GF(256) with primitive polynomial 0x11d
  const EXP = new Uint8Array(512);
  const LOG = new Uint8Array(256);
  (function initGF() {
    let x = 1;
    for (let i = 0; i < 255; i++) {
      EXP[i] = x;
      LOG[x] = i;
      x <<= 1;
      if (x & 0x100) x ^= 0x11d;
    }
    for (let i = 255; i < 512; i++) EXP[i] = EXP[i - 255];
  })();

  function gfMul(a, b) {
    if (a === 0 || b === 0) return 0;
    return EXP[LOG[a] + LOG[b]];
  }

  function rsGeneratorPoly(deg) {
    let poly = [1];
    for (let i = 0; i < deg; i++) {
      const next = new Array(poly.length + 1).fill(0);
      const factor = EXP[i];
      for (let j = 0; j < poly.length; j++) {
        next[j] ^= poly[j];
        next[j + 1] ^= gfMul(poly[j], factor);
      }
      poly = next;
    }
    return poly;
  }

  function rsRemainder(data, ecLen) {
    const gen = rsGeneratorPoly(ecLen);
    const rem = new Uint8Array(ecLen);
    for (let i = 0; i < data.length; i++) {
      const factor = data[i] ^ rem[0];
      for (let j = 0; j < ecLen - 1; j++) rem[j] = rem[j + 1];
      rem[ecLen - 1] = 0;
      for (let j = 0; j < ecLen; j++) {
        rem[j] ^= gfMul(gen[j + 1], factor);
      }
    }
    return rem;
  }

  function toUtf8Bytes(str) {
    if (typeof TextEncoder !== 'undefined') {
      return Array.from(new TextEncoder().encode(str));
    }
    const bytes = [];
    for (let i = 0; i < str.length; i++) {
      let c = str.charCodeAt(i);
      if (c < 0x80) bytes.push(c);
      else if (c < 0x800) bytes.push(0xc0 | (c >> 6), 0x80 | (c & 0x3f));
      else bytes.push(0xe0 | (c >> 12), 0x80 | ((c >> 6) & 0x3f), 0x80 | (c & 0x3f));
    }
    return bytes;
  }

  function pickVersion(byteLen) {
    for (let v = 1; v <= 10; v++) {
      const info = VER_M[v];
      const totalDataCw = info[2] * info[3] + info[4] * info[5];
      const countBits = v <= 9 ? 8 : 16;
      const totalBits = 4 + countBits + byteLen * 8;
      if (totalBits <= totalDataCw * 8) return v;
    }
    throw new Error('URL이 너무 깁니다 (최대 213바이트).');
  }

  function encodeData(bytes, v) {
    const info = VER_M[v];
    const totalDataCw = info[2] * info[3] + info[4] * info[5];
    const bits = [];
    function pushBits(val, len) {
      for (let i = len - 1; i >= 0; i--) bits.push((val >>> i) & 1);
    }
    // Mode 0100 (Byte)
    pushBits(0b0100, 4);
    pushBits(bytes.length, v <= 9 ? 8 : 16);
    for (const b of bytes) pushBits(b, 8);
    // Terminator
    const capBits = totalDataCw * 8;
    const term = Math.min(4, capBits - bits.length);
    pushBits(0, term);
    while (bits.length % 8 !== 0) bits.push(0);
    const dataCw = [];
    for (let i = 0; i < bits.length; i += 8) {
      let val = 0;
      for (let j = 0; j < 8; j++) val = (val << 1) | bits[i + j];
      dataCw.push(val);
    }
    const pads = [0xec, 0x11];
    let p = 0;
    while (dataCw.length < totalDataCw) {
      dataCw.push(pads[p]);
      p ^= 1;
    }

    // Split into blocks and compute RS ECC
    const ecPerBlock = info[1];
    const blocks = [];
    const ecBlocks = [];
    let offset = 0;
    for (let i = 0; i < info[2]; i++) {
      const blk = dataCw.slice(offset, offset + info[3]);
      offset += info[3];
      blocks.push(blk);
      ecBlocks.push(rsRemainder(blk, ecPerBlock));
    }
    for (let i = 0; i < info[4]; i++) {
      const blk = dataCw.slice(offset, offset + info[5]);
      offset += info[5];
      blocks.push(blk);
      ecBlocks.push(rsRemainder(blk, ecPerBlock));
    }

    // Interleave data codewords
    const finalCw = [];
    const maxDataLen = Math.max(info[3], info[5]);
    for (let i = 0; i < maxDataLen; i++) {
      for (const blk of blocks) {
        if (i < blk.length) finalCw.push(blk[i]);
      }
    }
    // Interleave EC codewords
    for (let i = 0; i < ecPerBlock; i++) {
      for (const ec of ecBlocks) finalCw.push(ec[i]);
    }
    return finalCw;
  }

  function formatBits(mask) {
    // ECC Level M = 00
    const data = (0b00 << 3) | mask;
    let rem = data;
    for (let i = 0; i < 10; i++) {
      rem = (rem << 1) ^ ((rem >>> 9) * 0x537);
    }
    return ((data << 10) | rem) ^ 0x5412;
  }

  function versionBits(v) {
    let rem = v;
    for (let i = 0; i < 12; i++) {
      rem = (rem << 1) ^ ((rem >>> 11) * 0x1f25);
    }
    return (v << 12) | rem;
  }

  function buildMatrix(v, codewords) {
    const size = v * 4 + 17;
    const mod = Array.from({ length: size }, () => new Uint8Array(size));
    const isFunc = Array.from({ length: size }, () => new Uint8Array(size));

    function setFunc(r, c, dark) {
      if (r < 0 || r >= size || c < 0 || c >= size) return;
      mod[r][c] = dark ? 1 : 0;
      isFunc[r][c] = 1;
    }

    // Finder patterns + separators
    function drawFinder(top, left) {
      for (let dr = -1; dr <= 7; dr++) {
        for (let dc = -1; dc <= 7; dc++) {
          const r = top + dr, c = left + dc;
          if (r < 0 || r >= size || c < 0 || c >= size) continue;
          const dist = Math.max(Math.abs(dr - 3), Math.abs(dc - 3));
          const dark = dist !== 2 && dist !== 4;
          setFunc(r, c, dark);
        }
      }
    }
    drawFinder(0, 0);
    drawFinder(0, size - 7);
    drawFinder(size - 7, 0);

    // Alignment patterns
    const pos = ALIGN_POS[v];
    for (let i = 0; i < pos.length; i++) {
      for (let j = 0; j < pos.length; j++) {
        if ((i === 0 && j === 0) || (i === 0 && j === pos.length - 1) || (i === pos.length - 1 && j === 0)) continue;
        const cr = pos[i], cc = pos[j];
        for (let dr = -2; dr <= 2; dr++) {
          for (let dc = -2; dc <= 2; dc++) {
            const dist = Math.max(Math.abs(dr), Math.abs(dc));
            setFunc(cr + dr, cc + dc, dist !== 1);
          }
        }
      }
    }

    // Timing patterns
    for (let i = 8; i < size - 8; i++) {
      if (!isFunc[6][i]) setFunc(6, i, i % 2 === 0);
      if (!isFunc[i][6]) setFunc(i, 6, i % 2 === 0);
    }

    // Reserve format info & dark module
    for (let i = 0; i <= 8; i++) {
      if (i !== 6) {
        isFunc[8][i] = 1;
        isFunc[i][8] = 1;
      }
    }
    for (let i = 0; i < 8; i++) isFunc[8][size - 1 - i] = 1;
    for (let i = 0; i < 7; i++) isFunc[size - 1 - i][8] = 1;
    setFunc(size - 8, 8, true);

    // Version info for v >= 7
    if (v >= 7) {
      const vb = versionBits(v);
      for (let i = 0; i < 18; i++) {
        const bit = ((vb >>> i) & 1) === 1;
        const a = Math.floor(i / 3);
        const b = size - 11 + (i % 3);
        setFunc(a, b, bit);
        setFunc(b, a, bit);
      }
    }

    // Place data bits
    let bitIdx = 0;
    const totalBits = codewords.length * 8;
    for (let right = size - 1; right >= 1; right -= 2) {
      if (right === 6) right = 5;
      for (let vert = 0; vert < size; vert++) {
        for (let j = 0; j < 2; j++) {
          const c = right - j;
          const upward = ((right + 1) & 2) === 0;
          const r = upward ? size - 1 - vert : vert;
          if (!isFunc[r][c]) {
            let bit = 0;
            if (bitIdx < totalBits) {
              bit = (codewords[bitIdx >>> 3] >>> (7 - (bitIdx & 7))) & 1;
            }
            mod[r][c] = bit;
            bitIdx++;
          }
        }
      }
    }

    function applyFormat(m, mask) {
      const fb = formatBits(mask);
      for (let i = 0; i <= 5; i++) m[8][i] = (fb >>> (14 - i)) & 1;
      m[8][7] = (fb >>> 8) & 1;
      m[8][8] = (fb >>> 7) & 1;
      m[7][8] = (fb >>> 6) & 1;
      for (let i = 0; i <= 5; i++) m[5 - i][8] = (fb >>> (5 - i)) & 1;
      for (let i = 0; i < 8; i++) m[8][size - 1 - i] = (fb >>> i) & 1;
      for (let i = 0; i < 7; i++) m[size - 7 + i][8] = (fb >>> (14 - i)) & 1;
      m[size - 8][8] = 1;
    }

    function maskCond(mask, r, c) {
      switch (mask) {
        case 0: return (r + c) % 2 === 0;
        case 1: return r % 2 === 0;
        case 2: return c % 3 === 0;
        case 3: return (r + c) % 3 === 0;
        case 4: return (Math.floor(r / 2) + Math.floor(c / 3)) % 2 === 0;
        case 5: return ((r * c) % 2) + ((r * c) % 3) === 0;
        case 6: return (((r * c) % 2) + ((r * c) % 3)) % 2 === 0;
        case 7: return (((r + c) % 2) + ((r * c) % 3)) % 2 === 0;
      }
      return false;
    }

    function penalty(m) {
      let score = 0;
      // N1: runs >= 5
      for (let r = 0; r < size; r++) {
        let run = 1;
        for (let c = 1; c < size; c++) {
          if (m[r][c] === m[r][c - 1]) run++;
          else { if (run >= 5) score += 3 + (run - 5); run = 1; }
        }
        if (run >= 5) score += 3 + (run - 5);
      }
      for (let c = 0; c < size; c++) {
        let run = 1;
        for (let r = 1; r < size; r++) {
          if (m[r][c] === m[r - 1][c]) run++;
          else { if (run >= 5) score += 3 + (run - 5); run = 1; }
        }
        if (run >= 5) score += 3 + (run - 5);
      }
      // N2: 2x2 blocks
      for (let r = 0; r < size - 1; r++) {
        for (let c = 0; c < size - 1; c++) {
          const v0 = m[r][c];
          if (v0 === m[r][c + 1] && v0 === m[r + 1][c] && v0 === m[r + 1][c + 1]) score += 3;
        }
      }
      // N4: dark ratio
      let dark = 0;
      for (let r = 0; r < size; r++) for (let c = 0; c < size; c++) if (m[r][c]) dark++;
      const pct = Math.abs((dark * 100) / (size * size) - 50);
      score += Math.floor(pct / 5) * 10;
      return score;
    }

    let bestMask = 0;
    let bestScore = Infinity;
    let bestMat = null;
    for (let mask = 0; mask < 8; mask++) {
      const m = mod.map((row) => row.slice());
      for (let r = 0; r < size; r++) {
        for (let c = 0; c < size; c++) {
          if (!isFunc[r][c] && maskCond(mask, r, c)) m[r][c] ^= 1;
        }
      }
      applyFormat(m, mask);
      const sc = penalty(m);
      if (sc < bestScore) {
        bestScore = sc;
        bestMask = mask;
        bestMat = m;
      }
    }
    return bestMat;
  }

  function makeQRMatrix(text) {
    const bytes = toUtf8Bytes(String(text));
    const v = pickVersion(bytes.length);
    const cw = encodeData(bytes, v);
    return buildMatrix(v, cw);
  }

  function makeQRSvg(text, quietZone = 4) {
    const mat = makeQRMatrix(text);
    const n = mat.length;
    const total = n + quietZone * 2;
    let d = '';
    for (let r = 0; r < n; r++) {
      for (let c = 0; c < n; c++) {
        if (mat[r][c]) {
          d += `M${c + quietZone},${r + quietZone}h1v1h-1z`;
        }
      }
    }
    return `<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 ${total} ${total}" shape-rendering="crispEdges"><rect width="${total}" height="${total}" fill="#ffffff"/><path d="${d}" fill="#000000"/></svg>`;
  }

  global.HongikQR = { makeQRMatrix, makeQRSvg };
})(typeof window !== 'undefined' ? window : globalThis);
