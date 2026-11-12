
"use strict";
/* ============================================================
   Chess core — complete legal-move engine:
   castling, en passant, promotion,
   pins/check evasion via pseudo-legal + king-safety filter,
   plus a forced-mate solver used to judge quiz moves.
   Board index = rank * 8 + file, rank 0 = rank 1, file 0 = a.
   ============================================================ */
const fileOf = (sq) => sq & 7;
const rankOf = (sq) => sq >> 3;
const makeSq = (file, rank) => rank * 8 + file;
const onBoard = (file, rank) => file >= 0 && file < 8 && rank >= 0 && rank < 8;
function squareName(sq) { return "abcdefgh"[fileOf(sq)] + String(rankOf(sq) + 1); }
function parseSquare(name) {
  const file = "abcdefgh".indexOf(name[0] || "");
  const rank = Number(name[1]) - 1;
  return makeSq(file, rank);
}
function colorOf(piece) { return piece === piece.toUpperCase() ? "w" : "b"; }
function kindOf(piece) { return piece.toLowerCase(); }
function opponent(color) { return color === "w" ? "b" : "w"; }

function parseFEN(fen) {
  const parts = fen.trim().split(/\s+/);
  const placement = parts[0] || "";
  const board = new Array(64).fill(null);
  const rows = placement.split("/");
  for (let row = 0; row < 8; row++) {
    const rank = 7 - row;
    let file = 0;
    for (const ch of rows[row] || "") {
      if (/\d/.test(ch)) file += Number(ch);
      else { board[makeSq(file, rank)] = ch; file += 1; }
    }
  }
  const castlingRaw = parts[2] || "-";
  return {
    board,
    turn: parts[1] === "b" ? "b" : "w",
    castling: castlingRaw === "-" ? "" : castlingRaw,
    ep: parts[3] && parts[3] !== "-" ? parseSquare(parts[3]) : -1,
    halfmove: Number(parts[4] || 0),
    fullmove: Number(parts[5] || 1),
  };
}

function findKing(board, color) {
  const target = color === "w" ? "K" : "k";
  for (let sq = 0; sq < 64; sq++) if (board[sq] === target) return sq;
  return -1;
}

const KNIGHT_JUMPS = [[1,2],[2,1],[2,-1],[1,-2],[-1,-2],[-2,-1],[-2,1],[-1,2]];
const KING_STEPS = [[1,0],[1,1],[0,1],[-1,1],[-1,0],[-1,-1],[0,-1],[1,-1]];
const BISHOP_DIRS = [[1,1],[1,-1],[-1,1],[-1,-1]];
const ROOK_DIRS = [[1,0],[-1,0],[0,1],[0,-1]];

function isSquareAttacked(board, target, by) {
  const tf = fileOf(target), tr = rankOf(target);
  const pawnRank = by === "w" ? tr - 1 : tr + 1;
  const pawnGlyph = by === "w" ? "P" : "p";
  for (const df of [-1, 1]) {
    const f = tf + df;
    if (onBoard(f, pawnRank) && board[makeSq(f, pawnRank)] === pawnGlyph) return true;
  }
  const knightGlyph = by === "w" ? "N" : "n";
  for (const [df, dr] of KNIGHT_JUMPS) {
    const f = tf + df, r = tr + dr;
    if (onBoard(f, r) && board[makeSq(f, r)] === knightGlyph) return true;
  }
  const kingGlyph = by === "w" ? "K" : "k";
  for (const [df, dr] of KING_STEPS) {
    const f = tf + df, r = tr + dr;
    if (onBoard(f, r) && board[makeSq(f, r)] === kingGlyph) return true;
  }
  const bishopGlyph = by === "w" ? "B" : "b";
  const rookGlyph = by === "w" ? "R" : "r";
  const queenGlyph = by === "w" ? "Q" : "q";
  for (const [dirs, glyphs] of [[BISHOP_DIRS, [bishopGlyph, queenGlyph]], [ROOK_DIRS, [rookGlyph, queenGlyph]]]) {
    for (const [df, dr] of dirs) {
      let f = tf + df, r = tr + dr;
      while (onBoard(f, r)) {
        const p = board[makeSq(f, r)];
        if (p != null) { if (glyphs.includes(p)) return true; break; }
        f += df; r += dr;
      }
    }
  }
  return false;
}

function isInCheck(state, color) {
  const king = findKing(state.board, color);
  if (king < 0) return false;
  return isSquareAttacked(state.board, king, opponent(color));
}

function addCastling(state, color, kingFrom, moves) {
  const { board, castling } = state;
  const home = color === "w" ? 0 : 7;
  if (kingFrom !== makeSq(4, home)) return;
  const enemy = opponent(color);
  const rookGlyph = color === "w" ? "R" : "r";
  if (isSquareAttacked(board, kingFrom, enemy)) return;
  const trySide = (right, rookFile, emptyFiles, safeFiles, castle) => {
    if (!castling.includes(right)) return;
    if (board[makeSq(rookFile, home)] !== rookGlyph) return;
    for (const ef of emptyFiles) if (board[makeSq(ef, home)] !== null) return;
    for (const sf of safeFiles) if (isSquareAttacked(board, makeSq(sf, home), enemy)) return;
    moves.push({ from: kingFrom, to: makeSq(castle === "K" ? 6 : 2, home), capture: false, castle });
  };
  trySide(color === "w" ? "K" : "k", 7, [5, 6], [5, 6], "K");
  trySide(color === "w" ? "Q" : "q", 0, [1, 2, 3], [3, 2], "Q");
}

function pseudoMoves(state, color) {
  const { board } = state;
  const moves = [];
  const dir = color === "w" ? 1 : -1;
  const startRank = color === "w" ? 1 : 6;
  const promoRank = color === "w" ? 7 : 0;
  const pushPawnMove = (from, to, capture, extra) => {
    if (rankOf(to) === promoRank) {
      for (const promotion of ["q", "r", "b", "n"]) moves.push(Object.assign({ from, to, capture, promotion }, extra || {}));
    } else {
      moves.push(Object.assign({ from, to, capture }, extra || {}));
    }
  };
  for (let from = 0; from < 64; from++) {
    const piece = board[from];
    if (piece == null || colorOf(piece) !== color) continue;
    const kind = kindOf(piece);
    const f = fileOf(from), r = rankOf(from);
    if (kind === "p") {
      const oneR = r + dir;
      if (onBoard(f, oneR) && board[makeSq(f, oneR)] === null) {
        pushPawnMove(from, makeSq(f, oneR), false);
        const twoR = r + 2 * dir;
        if (r === startRank && board[makeSq(f, twoR)] === null) {
          moves.push({ from, to: makeSq(f, twoR), capture: false, doublePush: true });
        }
      }
      for (const df of [-1, 1]) {
        const cf = f + df;
        if (!onBoard(cf, oneR)) continue;
        const to = makeSq(cf, oneR);
        const target = board[to];
        if (target != null && colorOf(target) !== color) pushPawnMove(from, to, true);
        else if (to === state.ep) {
          const victim = board[makeSq(cf, r)];
          if (victim === (color === "w" ? "p" : "P")) moves.push({ from, to, capture: true, enPassant: true });
        }
      }
      continue;
    }
    if (kind === "n" || kind === "k") {
      const jumps = kind === "n" ? KNIGHT_JUMPS : KING_STEPS;
      for (const [df, dr] of jumps) {
        const tf = f + df, tr = r + dr;
        if (!onBoard(tf, tr)) continue;
        const to = makeSq(tf, tr);
        const target = board[to];
        if (target == null) moves.push({ from, to, capture: false });
        else if (colorOf(target) !== color) moves.push({ from, to, capture: true });
      }
      if (kind === "k") addCastling(state, color, from, moves);
      continue;
    }
    const dirs = kind === "b" ? BISHOP_DIRS : kind === "r" ? ROOK_DIRS : KING_STEPS;
    for (const [df, dr] of dirs) {
      let tf = f + df, tr = r + dr;
      while (onBoard(tf, tr)) {
        const to = makeSq(tf, tr);
        const target = board[to];
        if (target == null) moves.push({ from, to, capture: false });
        else { if (colorOf(target) !== color) moves.push({ from, to, capture: true }); break; }
        tf += df; tr += dr;
      }
    }
  }
  return moves;
}

function applyMove(state, move) {
  const board = state.board.slice();
  const piece = board[move.from];
  if (piece == null) return state;
  const color = colorOf(piece);
  board[move.from] = null;
  if (move.enPassant) board[makeSq(fileOf(move.to), rankOf(move.from))] = null;
  let placed = piece;
  if (move.promotion) placed = color === "w" ? move.promotion.toUpperCase() : move.promotion;
  board[move.to] = placed;
  if (move.castle) {
    const home = color === "w" ? 0 : 7;
    if (move.castle === "K") { board[makeSq(5, home)] = board[makeSq(7, home)]; board[makeSq(7, home)] = null; }
    else { board[makeSq(3, home)] = board[makeSq(0, home)]; board[makeSq(0, home)] = null; }
  }
  let castling = state.castling;
  const strip = (chars) => { for (const c of chars) castling = castling.replace(c, ""); };
  if (piece === "K") strip("KQ");
  if (piece === "k") strip("kq");
  if (move.from === makeSq(0, 0) || move.to === makeSq(0, 0)) strip("Q");
  if (move.from === makeSq(7, 0) || move.to === makeSq(7, 0)) strip("K");
  if (move.from === makeSq(0, 7) || move.to === makeSq(0, 7)) strip("q");
  if (move.from === makeSq(7, 7) || move.to === makeSq(7, 7)) strip("k");
  return {
    board,
    turn: opponent(state.turn),
    castling,
    ep: move.doublePush ? makeSq(fileOf(move.from), rankOf(move.from) + (color === "w" ? 1 : -1)) : -1,
    halfmove: kindOf(piece) === "p" || move.capture ? 0 : state.halfmove + 1,
    fullmove: color === "b" ? state.fullmove + 1 : state.fullmove,
  };
}

function legalMoves(state, color) {
  color = color || state.turn;
  const enemy = opponent(color);
  const effective = state.turn === color ? state : Object.assign({}, state, { turn: color });
  return pseudoMoves(effective, color).filter((move) => {
    const next = applyMove(effective, move);
    const king = findKing(next.board, color);
    return king >= 0 && !isSquareAttacked(next.board, king, enemy);
  });
}

function isCheckmate(state) { return isInCheck(state, state.turn) && legalMoves(state).length === 0; }
function isStalemate(state) { return !isInCheck(state, state.turn) && legalMoves(state).length === 0; }

function matchUci(state, uci) {
  const from = parseSquare(uci.slice(0, 2));
  const to = parseSquare(uci.slice(2, 4));
  const promo = uci[4];
  for (const move of legalMoves(state)) {
    if (move.from !== from || move.to !== to) continue;
    if ((move.promotion || undefined) === (promo || undefined)) return move;
    if (!move.promotion && !promo) return move;
  }
  return null;
}
function moveToUci(move) { return squareName(move.from) + squareName(move.to) + (move.promotion || ""); }

function toSAN(state, move) {
  const piece = state.board[move.from];
  if (piece == null) return "";
  const kind = kindOf(piece);
  let san;
  if (move.castle) san = move.castle === "K" ? "O-O" : "O-O-O";
  else if (kind === "p") {
    san = move.capture ? "abcdefgh"[fileOf(move.from)] + "x" + squareName(move.to) : squareName(move.to);
    if (move.promotion) san += "=" + move.promotion.toUpperCase();
  } else {
    const rivals = legalMoves(state).filter((m) => m.to === move.to && m.from !== move.from && state.board[m.from] === piece);
    let disamb = "";
    if (rivals.length > 0) {
      const sameFile = rivals.some((m) => fileOf(m.from) === fileOf(move.from));
      const sameRank = rivals.some((m) => rankOf(m.from) === rankOf(move.from));
      if (!sameFile) disamb = "abcdefgh"[fileOf(move.from)] || "";
      else if (!sameRank) disamb = String(rankOf(move.from) + 1);
      else disamb = squareName(move.from);
    }
    san = kind.toUpperCase() + disamb + (move.capture ? "x" : "") + squareName(move.to);
  }
  const next = applyMove(state, move);
  if (isCheckmate(next)) san += "#";
  else if (isInCheck(next, next.turn)) san += "+";
  return san;
}

function mateDistance(state, attacker, maxPlies) {
  if (isCheckmate(state)) return state.turn === attacker ? null : 0;
  if (maxPlies <= 0) return null;
  const moves = legalMoves(state);
  if (moves.length === 0) return null;
  if (state.turn === attacker) {
    let best = null;
    for (const move of moves) {
      const d = mateDistance(applyMove(state, move), attacker, maxPlies - 1);
      if (d !== null && (best === null || d + 1 < best)) best = d + 1;
    }
    return best;
  }
  let worst = 0;
  for (const move of moves) {
    const d = mateDistance(applyMove(state, move), attacker, maxPlies - 1);
    if (d === null) return null;
    if (d + 1 > worst) worst = d + 1;
  }
  return worst;
}

function chooseDefenderReply(state, attacker, maxPlies) {
  const moves = legalMoves(state);
  let best = null, bestScore = -1;
  for (const move of moves) {
    const d = mateDistance(applyMove(state, move), attacker, maxPlies - 1);
    const score = d === null ? Infinity : d;
    if (score > bestScore) { bestScore = score; best = move; }
  }
  return best;
}

// A defender reply after which the attacker cannot force mate within
// the remaining plies — the concrete refutation of a wrong move.
// King escapes are tried first: when a checking move only *looks*
// like mate, the refutation is almost always the king stepping to
// the one square the attacker left open, and that is the move the
// player needs to see.
function findEscapeReply(state, attacker, maxPlies) {
  const moves = legalMoves(state).slice().sort((a, b) => {
    const ka = kindOf(state.board[a.from]) === "k" ? 0 : 1;
    const kb = kindOf(state.board[b.from]) === "k" ? 0 : 1;
    return ka - kb;
  });
  for (const move of moves) {
    if (mateDistance(applyMove(state, move), attacker, maxPlies - 1) === null) return move;
  }
  return null;
}

function toFEN(state) {
  const rows = [];
  for (let rank = 7; rank >= 0; rank--) {
    let row = "", empty = 0;
    for (let file = 0; file < 8; file++) {
      const piece = state.board[makeSq(file, rank)];
      if (piece == null) empty += 1;
      else { if (empty > 0) row += String(empty); empty = 0; row += piece; }
    }
    if (empty > 0) row += String(empty);
    rows.push(row);
  }
  return [rows.join("/"), state.turn, state.castling === "" ? "-" : state.castling,
    state.ep >= 0 ? squareName(state.ep) : "-", String(state.halfmove), String(state.fullmove)].join(" ");
}
function positionKey(state) { return toFEN(state).split(" ").slice(0, 4).join(" "); }

function insufficientMaterial(state) {
  const minors = [];
  for (let sq = 0; sq < 64; sq++) {
    const piece = state.board[sq];
    if (piece == null) continue;
    const kind = kindOf(piece);
    if (kind === "k") continue;
    if (kind === "p" || kind === "r" || kind === "q") return false;
    minors.push({ kind, squareColor: (fileOf(sq) + rankOf(sq)) % 2 });
  }
  if (minors.length <= 1) return true;
  if (minors.every((m) => m.kind === "b")) return minors.every((m) => m.squareColor === minors[0].squareColor);
  return false;
}

/* ============================================================
   Versus engine — negamax alpha-beta with MVV-LVA ordering,
   piece-square tables and a node budget (ported from engine.ts).
   ============================================================ */
const VALUES = { p: 100, n: 320, b: 330, r: 500, q: 900, k: 0 };
const PST = {
  p: [0,0,0,0,0,0,0,0, 50,50,50,50,50,50,50,50, 10,10,20,30,30,20,10,10, 5,5,10,25,25,10,5,5, 0,0,0,20,20,0,0,0, 5,-5,-10,0,0,-10,-5,5, 5,10,10,-20,-20,10,10,5, 0,0,0,0,0,0,0,0],
  n: [-50,-40,-30,-30,-30,-30,-40,-50, -40,-20,0,0,0,0,-20,-40, -30,0,10,15,15,10,0,-30, -30,5,15,20,20,15,5,-30, -30,0,15,20,20,15,0,-30, -30,5,10,15,15,10,5,-30, -40,-20,0,5,5,0,-20,-40, -50,-40,-30,-30,-30,-30,-40,-50],
  b: [-20,-10,-10,-10,-10,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,10,10,5,0,-10, -10,5,5,10,10,5,5,-10, -10,0,10,10,10,10,0,-10, -10,10,10,10,10,10,10,-10, -10,5,0,0,0,0,5,-10, -20,-10,-10,-10,-10,-10,-10,-20],
  r: [0,0,0,0,0,0,0,0, 5,10,10,10,10,10,10,5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, -5,0,0,0,0,0,0,-5, 0,0,0,5,5,0,0,0],
  q: [-20,-10,-10,-5,-5,-10,-10,-20, -10,0,0,0,0,0,0,-10, -10,0,5,5,5,5,0,-10, -5,0,5,5,5,5,0,-5, 0,0,5,5,5,5,0,-5, -10,5,5,5,5,5,0,-10, -10,0,5,0,0,0,0,-10, -20,-10,-10,-5,-5,-10,-10,-20],
};
const KING_PST = [-30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -30,-40,-40,-50,-50,-40,-40,-30, -20,-30,-30,-40,-40,-30,-30,-20, -10,-20,-20,-20,-20,-20,-20,-10, 20,20,0,0,0,0,20,20, 20,30,10,0,0,10,30,20];

function pstValue(kind, sq, isWhite) {
  const tableRank = isWhite ? 7 - rankOf(sq) : rankOf(sq);
  const idx = tableRank * 8 + fileOf(sq);
  if (kind === "k") return KING_PST[idx] || 0;
  return PST[kind][idx] || 0;
}
function evaluateBoard(state) {
  let score = 0;
  for (let sq = 0; sq < 64; sq++) {
    const piece = state.board[sq];
    if (piece == null) continue;
    const kind = kindOf(piece);
    const isWhite = piece === piece.toUpperCase();
    const value = VALUES[kind] + pstValue(kind, sq, isWhite);
    score += isWhite ? value : -value;
  }
  return score;
}
const MATE_SCORE = 100000;
let aiNodes = 0, aiBudget = 60000, aiStopped = false;
function orderMoves(state, moves) {
  return moves.map((move) => {
    let score = 0;
    if (move.capture) {
      const victim = move.enPassant ? 100 : VALUES[kindOf(state.board[move.to] || "p")];
      const attacker = VALUES[kindOf(state.board[move.from] || "p")];
      score = 10000 + victim * 10 - attacker;
    }
    if (move.promotion) score += 9000 + VALUES[move.promotion];
    return { move, score };
  }).sort((a, b) => b.score - a.score).map((e) => e.move);
}
function search(state, depth, alpha, beta, ply) {
  if (aiStopped) return 0;
  aiNodes += 1;
  if (aiNodes >= aiBudget) { aiStopped = true; return 0; }
  if (state.halfmove >= 100) return 0;
  const moves = legalMoves(state);
  if (moves.length === 0) return isInCheck(state, state.turn) ? -MATE_SCORE + ply : 0;
  if (depth <= 0) {
    const white = evaluateBoard(state);
    return state.turn === "w" ? white : -white;
  }
  let best = -Infinity;
  for (const move of orderMoves(state, moves)) {
    const value = -search(applyMove(state, move), depth - 1, -beta, -alpha, ply + 1);
    if (aiStopped) return 0;
    if (value > best) best = value;
    if (best > alpha) alpha = best;
    if (alpha >= beta) break;
  }
  return best;
}
function rootSearch(state, depth) {
  const moves = orderMoves(state, legalMoves(state));
  let best = null, alpha = -Infinity;
  for (const move of moves) {
    const value = -search(applyMove(state, move), depth - 1, -Infinity, -alpha, 1);
    if (aiStopped) return best;
    if (best === null || value > best.score) best = { move, score: value };
    if (value > alpha) alpha = value;
  }
  return best;
}
function chooseAiMove(state, difficulty) {
  const moves = legalMoves(state);
  if (moves.length === 0) return null;
  if (moves.length === 1) return moves[0];
  if (difficulty === "easy") {
    if (Math.random() < 0.3) return moves[Math.floor(Math.random() * moves.length)];
    aiNodes = 0; aiStopped = false; aiBudget = 4000;
    const scored = orderMoves(state, moves).map((move) => ({
      move, score: -search(applyMove(state, move), 0, -Infinity, Infinity, 1),
    }));
    scored.sort((a, b) => b.score - a.score);
    const top = scored[0];
    if (!top) return moves[0];
    const nearBest = scored.filter((s) => top.score - s.score <= 60);
    return (nearBest[Math.floor(Math.random() * nearBest.length)] || top).move;
  }
  const maxDepth = difficulty === "medium" ? 2 : 3;
  aiBudget = difficulty === "medium" ? 25000 : 90000;
  aiNodes = 0; aiStopped = false;
  let best = null;
  for (let depth = 1; depth <= maxDepth; depth++) {
    const result = rootSearch(state, depth);
    if (result) best = result;
    if (aiStopped) break;
  }
  return best ? best.move : moves[0];
}

/* ============================================================
   Sound — tiny WebAudio effects, no audio files (from sound.ts).
   ============================================================ */
const LS_MUTED = "chess-public-muted";
let audioCtx = null;
let muted = false;
try { muted = window.localStorage.getItem(LS_MUTED) === "1"; } catch (e) { muted = false; }
function isMuted() { return muted; }
function setMuted(value) {
  muted = value;
  try { window.localStorage.setItem(LS_MUTED, value ? "1" : "0"); } catch (e) {}
}
function audio() {
  if (muted) return null;
  try {
    if (!audioCtx) {
      const AC = window.AudioContext || window.webkitAudioContext;
      if (!AC) return null;
      audioCtx = new AC();
    }
    if (audioCtx.state === "suspended") audioCtx.resume();
    return audioCtx;
  } catch (e) { return null; }
}
function tone(ac, freq, dur, type, gainPeak, delay, slideTo) {
  delay = delay || 0;
  const t0 = ac.currentTime + delay;
  const osc = ac.createOscillator();
  const gain = ac.createGain();
  osc.type = type;
  osc.frequency.setValueAtTime(freq, t0);
  if (slideTo) osc.frequency.exponentialRampToValueAtTime(slideTo, t0 + dur);
  gain.gain.setValueAtTime(0, t0);
  gain.gain.linearRampToValueAtTime(gainPeak, t0 + 0.012);
  gain.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
  osc.connect(gain); gain.connect(ac.destination);
  osc.start(t0); osc.stop(t0 + dur + 0.05);
}
function thock(ac, delay) {
  delay = delay || 0;
  const t0 = ac.currentTime + delay;
  const bufferSize = Math.floor(ac.sampleRate * 0.06);
  const buffer = ac.createBuffer(1, bufferSize, ac.sampleRate);
  const data = buffer.getChannelData(0);
  for (let i = 0; i < bufferSize; i++) data[i] = (Math.random() * 2 - 1) * (1 - i / bufferSize);
  const src = ac.createBufferSource();
  src.buffer = buffer;
  const filter = ac.createBiquadFilter();
  filter.type = "lowpass"; filter.frequency.value = 900;
  const gain = ac.createGain();
  gain.gain.setValueAtTime(0.25, t0);
  gain.gain.exponentialRampToValueAtTime(0.0001, t0 + 0.07);
  src.connect(filter); filter.connect(gain); gain.connect(ac.destination);
  src.start(t0);
  tone(ac, 190, 0.09, "sine", 0.18, delay, 120);
}
const sfx = {
  select() { const ac = audio(); if (ac) tone(ac, 620, 0.06, "sine", 0.08); },
  move() { const ac = audio(); if (ac) thock(ac); },
  capture() { const ac = audio(); if (!ac) return; thock(ac); tone(ac, 880, 0.1, "triangle", 0.12, 0.02); tone(ac, 1320, 0.12, "sine", 0.08, 0.05); },
  check() { const ac = audio(); if (!ac) return; thock(ac); tone(ac, 1180, 0.14, "sine", 0.1, 0.03); },
  wrong() { const ac = audio(); if (ac) tone(ac, 240, 0.22, "sine", 0.1, 0, 170); },
  win() {
    const ac = audio(); if (!ac) return;
    [523.25, 659.25, 783.99, 1046.5].forEach((f, i) => tone(ac, f, 0.28, "triangle", 0.12, i * 0.09));
    tone(ac, 1318.5, 0.4, "sine", 0.07, 4 * 0.09);
  },
  lose() { const ac = audio(); if (!ac) return; tone(ac, 392, 0.25, "triangle", 0.09); tone(ac, 329.63, 0.35, "triangle", 0.09, 0.14); },
};

/* ============================================================
   Piece art — all 12 pieces in one illustrated SVG style
   (Staunton silhouettes, gradient + gloss + shadow; PieceArt.tsx).
   ============================================================ */
const SHAPES = {
  k: {
    body: [
      "M 22.5,25 C 22.5,25 27,17.5 25.5,14.5 C 25.5,14.5 24.5,12 22.5,12 C 20.5,12 19.5,14.5 19.5,14.5 C 18,17.5 22.5,25 22.5,25 z",
      "M 12.5,37 C 18,40.5 27,40.5 32.5,37 L 32.5,30 C 32.5,30 41.5,25.5 38.5,19.5 C 34.5,13 25,16 22.5,23.5 L 22.5,27 L 22.5,23.5 C 20,16 10.5,13 6.5,19.5 C 3.5,25.5 12.5,30 12.5,30 L 12.5,37 z",
    ],
    details: ["M 22.5,11.5 L 22.5,5.5", "M 20,7.5 L 25,7.5", "M 12.5,30 C 18,27 27,27 32.5,30", "M 12.5,33.5 C 18,30.5 27,30.5 32.5,33.5", "M 12.5,37 C 18,34 27,34 32.5,37"],
  },
  q: {
    body: [
      "M 9,26 C 17.5,24.5 30,24.5 36,26 L 38.5,13.5 L 31,25 L 30.5,10.5 L 25.5,24.5 L 22.5,10 L 19.5,24.5 L 14.5,10.5 L 14,25 L 6.5,13.5 L 9,26 z",
      "M 9,26 C 9,28 10.5,28 11.5,30 C 12.5,31.5 12.5,30.5 12.5,33.5 C 18,31 27,31 32.5,33.5 C 32.5,30.5 32.5,31.5 33.5,30 C 34.5,28 36,28 36,26 C 27.5,24.5 17.5,24.5 9,26 z",
      "M 12.5,37 C 18,40.5 27,40.5 32.5,37 L 32.5,33.5 C 27,30.5 18,30.5 12.5,33.5 L 12.5,37 z",
    ],
    bodyCircles: [{cx:6,cy:12,r:2},{cx:14,cy:9,r:2},{cx:22.5,cy:8,r:2},{cx:31,cy:9,r:2},{cx:39,cy:12,r:2}],
    details: ["M 11.5,30 C 15,29 30,29 33.5,30", "M 12,33.5 C 18,32.5 27,32.5 33,33.5"],
  },
  r: {
    body: [
      "M 9,39 L 36,39 L 36,36 L 9,36 L 9,39 z",
      "M 12,36 L 12,32 L 33,32 L 33,36 L 12,36 z",
      "M 11,14 L 11,9 L 15,9 L 15,11 L 20,11 L 20,9 L 25,9 L 25,11 L 30,11 L 30,9 L 34,9 L 34,14 z",
      "M 34,14 L 31,17 L 14,17 L 11,14 z",
      "M 31,17 L 31,29.5 L 14,29.5 L 14,17 z",
      "M 31,29.5 L 32.5,32 L 12.5,32 L 14,29.5 z",
    ],
    details: ["M 11,14 L 34,14"],
  },
  b: {
    body: [
      "M 9,36 C 12.39,35.03 19.11,36.43 22.5,34 C 25.89,36.43 32.61,35.03 36,36 C 36,36 37.65,36.54 39,38 C 38.32,38.97 37.35,38.99 36,38.5 C 32.61,37.53 25.89,38.96 22.5,37.5 C 19.11,38.96 12.39,37.53 9,38.5 C 7.65,38.99 6.68,38.97 6,38 C 7.35,36.54 9,36 9,36 z",
      "M 15,32 C 17.5,34.5 27.5,34.5 30,32 C 30.5,30.5 30,30 30,30 C 30,27.5 27.5,26 27.5,26 C 33,24.5 33.5,14.5 22.5,10.5 C 11.5,14.5 12,24.5 17.5,26 C 17.5,26 15,27.5 15,30 C 15,30 14.5,30.5 15,32 z",
      "M 25,8 A 2.5,2.5 0 1,1 20,8 A 2.5,2.5 0 1,1 25,8 z",
    ],
    details: ["M 17.5,26 L 27.5,26", "M 15,30 L 30,30", "M 22.5,15.5 L 22.5,20.5", "M 20,18 L 25,18"],
  },
  n: {
    body: [
      "M 22,10 C 32.5,11 38.5,18 38,39 L 15,39 C 15,30 25,32.5 23,18 z",
      "M 24,18 C 24.38,20.91 18.45,25.37 16,27 C 13,29 13.18,31.34 11,31 C 9.96,30.06 12.41,27.96 11,28 C 10,28 11.19,29.23 10,30 C 9,30 5.997,31 6,26 C 6,24 12,14 12,14 C 12,14 13.89,12.1 14,10.5 C 13.27,9.51 13.5,8.5 13.5,7.5 C 14.5,6.5 16.5,10 16.5,10 L 18.5,10 C 18.5,10 19.28,8.01 21,7 C 22,7 22,10 22,10 z",
    ],
    details: [],
    detailDots: [{cx:9,cy:25.5,r:0.7},{cx:14.8,cy:15.4,r:0.9}],
  },
  p: {
    body: ["M 22.5,9 C 20.29,9 18.5,10.79 18.5,13 C 18.5,13.89 18.79,14.71 19.28,15.38 C 17.33,16.5 16,18.59 16,21 C 16,23.03 16.94,24.84 18.41,26.03 C 15.41,27.09 11,31.58 11,39.5 L 34,39.5 C 34,31.58 29.59,27.09 26.59,26.03 C 28.06,24.84 29,23.03 29,21 C 29,18.59 27.67,16.5 25.72,15.38 C 26.21,14.71 26.5,13.89 26.5,13 C 26.5,10.79 24.71,9 22.5,9 z"],
    details: [],
  },
};
let svgUid = 0;
function pieceSVG(kind, color, lifted) {
  svgUid += 1;
  const uid = "u" + svgUid;
  const gradId = "pg-" + uid, clipId = "pc-" + uid;
  const isWhite = color === "w";
  const shape = SHAPES[kind];
  const edge = isWhite ? "#26354d" : "#090f1a";
  const detail = isWhite ? "#26354d" : "#c9d8ec";
  const stops = isWhite
    ? '<stop offset="0%" stop-color="#ffffff"/><stop offset="55%" stop-color="#e3ebf5"/><stop offset="100%" stop-color="#b4c4da"/>'
    : '<stop offset="0%" stop-color="#637893"/><stop offset="55%" stop-color="#33445e"/><stop offset="100%" stop-color="#131f31"/>';
  const bodyPaths = shape.body.map((d) => '<path d="' + d + '"/>').join("");
  const bodyCircles = (shape.bodyCircles || []).map((c) => '<circle cx="' + c.cx + '" cy="' + c.cy + '" r="' + c.r + '"/>').join("");
  const fillBody = shape.body.map((d) => '<path d="' + d + '" fill="url(#' + gradId + ')"/>').join("");
  const fillCircles = (shape.bodyCircles || []).map((c) => '<circle cx="' + c.cx + '" cy="' + c.cy + '" r="' + c.r + '" fill="url(#' + gradId + ')"/>').join("");
  const detailPaths = shape.details.map((d) => '<path d="' + d + '"/>').join("");
  const detailDots = (shape.detailDots || []).map((c) => '<circle cx="' + c.cx + '" cy="' + c.cy + '" r="' + c.r + '" fill="' + detail + '"/>').join("");
  const filter = lifted ? "drop-shadow(0 8px 10px rgba(0,0,0,0.5))" : "drop-shadow(0 2px 3px rgba(0,0,0,0.4))";
  const transform = lifted ? "transform:scale(1.13) translateY(-4%);" : "";
  return '<svg viewBox="0 0 45 45" aria-hidden="true" style="display:block;width:94%;height:94%;filter:' + filter + ";" + transform + 'transition:transform 120ms ease-out">'
    + '<defs><linearGradient id="' + gradId + '" x1="0" y1="0" x2="0.35" y2="1">' + stops + "</linearGradient>"
    + '<clipPath id="' + clipId + '">' + bodyPaths + bodyCircles + "</clipPath></defs>"
    + '<g stroke="' + edge + '" stroke-width="1.5" stroke-linejoin="round">' + fillBody + fillCircles + "</g>"
    + '<g clip-path="url(#' + clipId + ')"><ellipse cx="16" cy="10" rx="15" ry="9" fill="#ffffff" opacity="' + (isWhite ? 0.55 : 0.28) + '" transform="rotate(-18 16 10)"/>'
    + '<ellipse cx="30" cy="42" rx="16" ry="7" fill="#000000" opacity="' + (isWhite ? 0.1 : 0.25) + '"/></g>'
    + '<g fill="none" stroke="' + detail + '" stroke-width="1.3" stroke-linecap="round" stroke-linejoin="round">' + detailPaths + "</g>"
    + detailDots + "</svg>";
}
function pieceHTML(piece, lifted) {
  return "<span>" + pieceSVG(kindOf(piece), colorOf(piece), lifted) + "</span>";
}

const PIECE_NAMES = { k: "キング", q: "クイーン", r: "ルーク", b: "ビショップ", n: "ナイト", p: "ポーン" };
const LIGHT_SQ = "#cbd5e1", DARK_SQ = "#334155";

/* ============================================================
   Board view — 2D slate board + optional 3D board (Poly Haven
   chess set, CC0). 3D is a pure view layer: same render(opts)
   contract, same tap callback, same glide/burst fields.
   ============================================================ */
const LS_VIEW = "chess-board-view-v1";
let boardViewMode = "2d"; // "2d" | "3d" — shared by quiz + versus toggles, remembered on this device
try { if (window.localStorage.getItem(LS_VIEW) === "3d") boardViewMode = "3d"; } catch (e) {}
const boardViewRegistry = []; // every live board view, kept in sync

const CHESS3D_BASE = "assets/chess/assets/chess3d/";
const CHESS3D_KEYS = ["wK", "wQ", "wR", "wB", "wN", "wP", "bK", "bQ", "bR", "bB", "bN", "bP"];
let chess3dTemplates = null; // { board: Object3D, pieces: { wK: Object3D, ... } }
let chess3dPromise = null;
const chess3dProgressListeners = [];
function loadChess3DTemplates(onProgress) {
  if (typeof onProgress === "function") chess3dProgressListeners.push(onProgress);
  if (chess3dTemplates) return Promise.resolve(chess3dTemplates);
  if (chess3dPromise) return chess3dPromise;
  chess3dPromise = new Promise((resolve, reject) => {
    if (typeof THREE === "undefined" || !THREE.GLTFLoader) { reject(new Error("three unavailable")); return; }
    const loader = new THREE.GLTFLoader();
    const out = { board: null, pieces: {} };
    const files = ["board"].concat(CHESS3D_KEYS);
    let doneCount = 0;
    // One file at a time, up to 3 attempts each. The old loader fired all
    // 13 files in parallel and let a single failure reject the whole set:
    // on the phone (reported: 3D読み込み出来ない) the parallel downloads
    // plus dozens of texture decodes at once were enough for one load to
    // error out, and the 3D board never appeared. Sequential loads with a
    // per-file retry make a flaky single fetch recoverable, and progress
    // callbacks let the board show how far the load has got.
    const loadOne = (name, attemptsLeft) => new Promise((res, rej) => {
      loader.load(CHESS3D_BASE + name + ".glb", (g) => res(g.scene), undefined, (err) => {
        if (attemptsLeft > 1) {
          setTimeout(() => { loadOne(name, attemptsLeft - 1).then(res, rej); }, 600);
        } else rej(err);
      });
    });
    let chain = Promise.resolve();
    for (const name of files) {
      chain = chain.then(() => loadOne(name, 3)).then((scene) => {
        if (name === "board") out.board = scene; else out.pieces[name] = scene;
        doneCount += 1;
        for (const fn of chess3dProgressListeners) { try { fn(doneCount, files.length); } catch (e) {} }
      });
    }
    chain.then(() => { chess3dTemplates = out; resolve(out); }, reject);
  });
  chess3dPromise.catch(() => { chess3dPromise = null; });
  return chess3dPromise;
}
function makeLabelSprite(text) {
  const c = document.createElement("canvas");
  c.width = 128; c.height = 128;
  const ctx = c.getContext("2d");
  ctx.font = "700 84px system-ui, sans-serif";
  ctx.textAlign = "center"; ctx.textBaseline = "middle";
  ctx.shadowColor = "rgba(0,0,0,0.9)"; ctx.shadowBlur = 10;
  ctx.fillStyle = "#f1f5f9";
  ctx.fillText(text, 64, 68);
  const tex = new THREE.CanvasTexture(c);
  const mat = new THREE.SpriteMaterial({ map: tex, transparent: true, depthWrite: false });
  const spr = new THREE.Sprite(mat);
  spr.scale.set(0.026, 0.026, 1);
  return spr;
}

function displayPos(sq, orientation) {
  const file = fileOf(sq), rank = rankOf(sq);
  return orientation === "w" ? { col: file, row: 7 - rank } : { col: 7 - file, row: rank };
}
function createBoardView(wrapEl, onSquareTap) {
  wrapEl.innerHTML = '<div class="board-grid"></div>'
    + '<div class="board3d-wrap" hidden><div class="board3d-loading">3Dモデルを読み込み中…</div></div>';
  const grid = wrapEl.children[0];
  const wrap3d = wrapEl.children[1];
  wrap3d.tabIndex = 0;
  wrap3d.setAttribute("role", "group");
  wrap3d.setAttribute("aria-label", "3D盤面。矢印キーでマスを選び、Enterで駒の選択と移動ができます。ドラッグで回転できます。");
  wrap3d.style.outline = "none";
  const loadingEl = wrap3d.firstChild;
  const cellEls = new Array(64);
  const view = {
    glide: null,
    burst: null,
    mode: boardViewMode,
    lastOpts: null,
    render(opts) {
      view.lastOpts = opts;
      if (view.mode === "3d") render3D(opts); else render2D(opts);
    },
    focusSq: null,
    focus3D() { try { wrap3d.focus({ preventScroll: true }); } catch (e) { wrap3d.focus(); } },
    setViewMode(mode) {
      view.mode = mode;
      boardViewMode = mode;
      try { window.localStorage.setItem(LS_VIEW, mode); } catch (e) {}
      const is3D = mode === "3d";
      grid.style.display = is3D ? "none" : "";
      wrap3d.hidden = !is3D;
      if (is3D) { ensure3D(); if (view.lastOpts) render3D(view.lastOpts); startLoop(); view.focus3D(); }
      else { stopLoop(); if (view.lastOpts) render2D(view.lastOpts); }
    },
  };

  // Keyboard play for the 3D board: arrows move a focus ring in screen
  // terms (player-relative), Enter/Space taps the focused square.
  document.addEventListener("keydown", (e) => {
    if (view.mode !== "3d" || !view.lastOpts || wrap3d.hidden || wrapEl.offsetParent === null) return;
    const t = e.target;
    if (t && (t.tagName === "INPUT" || t.tagName === "TEXTAREA" || t.tagName === "SELECT")) return;
    if (t && t.tagName === "BUTTON" && (e.key === "Enter" || e.key === " ")) return;
    const orientation = view.lastOpts.orientation;
    const toSq = (col, row) => makeSq(orientation === "w" ? col : 7 - col, orientation === "w" ? 7 - row : row);
    if (view.focusSq == null) view.focusSq = toSq(0, 7);
    const pos = displayPos(view.focusSq, orientation);
    let handled = true;
    if (e.key === "ArrowUp") pos.row = Math.max(0, pos.row - 1);
    else if (e.key === "ArrowDown") pos.row = Math.min(7, pos.row + 1);
    else if (e.key === "ArrowLeft") pos.col = Math.max(0, pos.col - 1);
    else if (e.key === "ArrowRight") pos.col = Math.min(7, pos.col + 1);
    else if (e.key === "Enter" || e.key === " ") {
      if (!view.lastOpts.disabled) onSquareTap(view.focusSq);
    } else handled = false;
    if (handled) {
      e.preventDefault();
      view.focusSq = toSq(pos.col, pos.row);
      if (view.lastOpts) view.render(view.lastOpts);
    }
  });

  /* ---------------- 2D rendering (original behaviour) ---------------- */
  function render2D(opts) {
    wrapEl.querySelectorAll(".glide-el").forEach((el) => el.remove());
    const state = opts.state, orientation = opts.orientation;
    const targetBySquare = new Map();
    for (const m of opts.targets || []) targetBySquare.set(m.to, m);
    grid.innerHTML = "";
    let glideEl = null;
    for (let row = 0; row < 8; row++) {
      for (let col = 0; col < 8; col++) {
        const file = orientation === "w" ? col : 7 - col;
        const rank = orientation === "w" ? 7 - row : row;
        const sq = makeSq(file, rank);
        const isLight = (file + rank) % 2 === 1;
        const piece = state.board[sq];
        const target = targetBySquare.get(sq);
        const isSelected = opts.selected === sq;
        const isLast = opts.lastMove && (opts.lastMove.from === sq || opts.lastMove.to === sq);
        const isCheck = opts.checkSquare === sq;
        const isStar = opts.starSquare === sq;
        const hidePiece = view.glide && view.glide.to === sq;
        const btn = document.createElement("button");
        btn.type = "button";
        btn.className = "cell";
        btn.disabled = !!opts.disabled;
        btn.style.backgroundColor = isLight ? LIGHT_SQ : DARK_SQ;
        if (isSelected) btn.style.boxShadow = "inset 0 0 0 3px #38bdf8, inset 0 0 14px rgba(56,189,248,0.55)";
        else if (isStar) btn.style.boxShadow = "inset 0 0 0 3px #fbbf24, inset 0 0 16px rgba(251,191,36,0.6)";
        const labelParts = [squareName(sq)];
        if (piece) labelParts.push((colorOf(piece) === "w" ? "白" : "黒") + "の" + PIECE_NAMES[kindOf(piece)]);
        if (target) labelParts.push("ここへ動かせます");
        btn.setAttribute("aria-label", labelParts.join(" "));
        let html = "";
        if (isLast) html += '<span class="lastmove"></span>';
        if (isCheck) html += '<span class="checkpulse"></span>';
        if (col === 0) html += '<span class="coord rank" style="color:' + (isLight ? "#475569" : "#cbd5e1") + '">' + (rank + 1) + "</span>";
        if (row === 7) html += '<span class="coord file" style="color:' + (isLight ? "#475569" : "#cbd5e1") + '">' + "abcdefgh"[file] + "</span>";
        if (piece && !hidePiece) html += '<span class="piece-holder">' + pieceHTML(piece, isSelected) + "</span>";
        if (target && !target.capture) html += '<span class="dot dot-in"></span>';
        if (target && target.capture) html += '<span class="capring ring-in"></span>';
        if (view.burst && view.burst.sq === sq) html += '<span class="burst-ring-el burst-ring"></span>';
        btn.innerHTML = html;
        btn.addEventListener("click", () => onSquareTap(sq));
        grid.appendChild(btn);
        cellEls[sq] = btn;
      }
    }
    if (view.glide) {
      glideEl = document.createElement("div");
      glideEl.className = "glide-el";
      glideEl.setAttribute("aria-hidden", "true");
      glideEl.innerHTML = pieceHTML(view.glide.piece, true);
      const from = displayPos(view.glide.from, orientation);
      glideEl.style.transform = "translate(" + from.col * 100 + "%, " + from.row * 100 + "%)";
      wrapEl.appendChild(glideEl);
      const to = displayPos(view.glide.to, orientation);
      requestAnimationFrame(() => requestAnimationFrame(() => {
        if (glideEl) glideEl.style.transform = "translate(" + to.col * 100 + "%, " + to.row * 100 + "%)";
      }));
    }
  }

  /* ---------------- 3D rendering ---------------- */
  const SQ3 = 0.05787;              // square size (m) — see chess-set MANIFEST
  const TOP_Y = 0.0176;             // board top surface height (m)
  const EDGE = 0.256;               // label offset inside the board frame
  let g3 = null;                    // three.js context, built lazily
  let glideStart = 0, glideKey = "";
  let burstStart = 0, burstKey = -1;

  function sqWorld(sq) {
    return { x: (fileOf(sq) - 3.5) * SQ3, z: (3.5 - rankOf(sq)) * SQ3 };
  }
  function ensure3D() {
    if (g3) { resize3D(); return; }
    if (typeof THREE === "undefined" || !THREE.GLTFLoader || !THREE.OrbitControls) {
      loadingEl.textContent = "3Dライブラリを読み込めませんでした。2D表示をお使いください。";
      return;
    }
    try {
      const renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true });
      renderer.setPixelRatio(Math.min(window.devicePixelRatio || 1, 1.5));
      renderer.outputEncoding = THREE.sRGBEncoding;
      renderer.toneMapping = THREE.ACESFilmicToneMapping;
      renderer.toneMappingExposure = 1.12;
      renderer.domElement.className = "board3d-canvas";
      wrap3d.appendChild(renderer.domElement);
      const scene = new THREE.Scene();
      const camera = new THREE.PerspectiveCamera(38, 1, 0.01, 10);
      scene.add(new THREE.HemisphereLight(0xffffff, 0x334155, 0.85));
      const key = new THREE.DirectionalLight(0xffffff, 0.95);
      key.position.set(0.35, 0.8, 0.3);
      scene.add(key);
      const fill = new THREE.DirectionalLight(0xbfd9ff, 0.35);
      fill.position.set(-0.5, 0.4, -0.45);
      scene.add(fill);
      const controls = new THREE.OrbitControls(camera, renderer.domElement);
      controls.target.set(0, 0, 0);
      controls.enableDamping = true;
      controls.dampingFactor = 0.08;
      controls.enablePan = false;
      controls.rotateSpeed = 0.55;
      controls.minDistance = 0.38;
      controls.maxDistance = 1.15;
      // Clamp polar angle: camera stays above board level, so the open
      // undersides of the scanned pieces are never visible.
      controls.addEventListener("change", () => { if (g3) g3.dirty = true; });
      controls.minPolarAngle = 0.18;
      controls.maxPolarAngle = 1.32;
      const boardGroup = new THREE.Group(); scene.add(boardGroup);
      const hlGroup = new THREE.Group(); scene.add(hlGroup);
      const labelGroup = new THREE.Group(); scene.add(labelGroup);
      const pieceGroup = new THREE.Group(); scene.add(pieceGroup);
      const hitGroup = new THREE.Group(); scene.add(hitGroup);
      const hitMeshes = [];
      const hitGeo = new THREE.PlaneGeometry(SQ3, SQ3);
      const hitMat = new THREE.MeshBasicMaterial({ transparent: true, opacity: 0, depthWrite: false });
      for (let sq = 0; sq < 64; sq++) {
        const m = new THREE.Mesh(hitGeo, hitMat);
        m.rotation.x = -Math.PI / 2;
        const p = sqWorld(sq);
        m.position.set(p.x, TOP_Y + 0.004, p.z);
        m.userData.sq = sq;
        hitGroup.add(m); hitMeshes.push(m);
      }
      g3 = {
        renderer, scene, camera, controls, boardGroup, hlGroup, labelGroup, pieceGroup,
        hitMeshes, raycaster: new THREE.Raycaster(), dirty: true,
        pieces: new Map(), ready: false, orientation: null, raf: 0, downPos: null,
      };
      // Tap vs drag: only a small, quick pointer movement counts as a tap,
      // so orbiting the camera never moves a piece by accident.
      renderer.domElement.addEventListener("pointerdown", (e) => { g3.downPos = { x: e.clientX, y: e.clientY, t: Date.now() }; });
      renderer.domElement.addEventListener("pointerup", (e) => {
        if (!g3.downPos) return;
        const dx = e.clientX - g3.downPos.x, dy = e.clientY - g3.downPos.y;
        const dt = Date.now() - g3.downPos.t;
        g3.downPos = null;
        if (dx * dx + dy * dy > 64 || dt > 600) return;
        if (!view.lastOpts || view.lastOpts.disabled) return;
        const rect = renderer.domElement.getBoundingClientRect();
        const nx = ((e.clientX - rect.left) / rect.width) * 2 - 1;
        const ny = -((e.clientY - rect.top) / rect.height) * 2 + 1;
        g3.raycaster.setFromCamera({ x: nx, y: ny }, camera);
        const hits = g3.raycaster.intersectObjects(g3.hitMeshes, false);
        if (hits.length > 0) onSquareTap(hits[0].object.userData.sq);
      });
      window.addEventListener("resize", resize3D);
      loadChess3DTemplates((doneCount, totalCount) => {
        if (!g3.ready) loadingEl.textContent = "3Dモデルを読み込み中… (" + doneCount + "/" + totalCount + ")";
      }).then((tpl) => {
        if (!g3) return;
        const boardObj = tpl.board.clone(true);
        boardGroup.add(boardObj);
        g3.templates = tpl;
        g3.ready = true;
        loadingEl.hidden = true;
        resize3D();
        if (view.lastOpts) render3D(view.lastOpts);
      }).catch(() => { loadingEl.textContent = "3Dモデルの読み込みに失敗しました。2D表示をお使いください。"; });
      resize3D();
    } catch (e) {
      loadingEl.textContent = "3D表示を初期化できませんでした。2D表示をお使いください。";
    }
  }
  function resize3D() {
    if (!g3) return;
    const w = wrap3d.clientWidth || wrapEl.clientWidth || 300;
    if (g3.width !== w) { g3.width = w; g3.dirty = true; }
    g3.renderer.setSize(w, w);
    g3.camera.aspect = 1;
    g3.camera.updateProjectionMatrix();
  }
  function setCameraForOrientation(orientation) {
    if (!g3 || g3.orientation === orientation) return;
    g3.orientation = orientation;
    const isW = orientation === "w";
    g3.camera.position.set(0, 0.60, isW ? 0.74 : -0.74);
    const az = isW ? 0 : Math.PI;
    g3.controls.minAzimuthAngle = az - 0.85;
    g3.controls.maxAzimuthAngle = az + 0.85;
    g3.controls.update();
    buildLabels(orientation);
  }
  function buildLabels(orientation) {
    if (!g3) return;
    while (g3.labelGroup.children.length) g3.labelGroup.remove(g3.labelGroup.children[0]);
    const isW = orientation === "w";
    for (let f = 0; f < 8; f++) {
      const spr = makeLabelSprite("abcdefgh"[f]);
      spr.position.set((f - 3.5) * SQ3, TOP_Y + 0.004, isW ? EDGE : -EDGE);
      g3.labelGroup.add(spr);
    }
    for (let r = 0; r < 8; r++) {
      const spr = makeLabelSprite(String(r + 1));
      spr.position.set(isW ? -EDGE : EDGE, TOP_Y + 0.004, (3.5 - r) * SQ3);
      g3.labelGroup.add(spr);
    }
  }
  function flatPlane(size, color, opacity, ring) {
    let geo;
    if (ring) geo = new THREE.RingGeometry(size * 0.36, size * 0.49, 40);
    else if (ring === false) geo = new THREE.CircleGeometry(size * 0.5, 40);
    else geo = new THREE.PlaneGeometry(size, size);
    const mat = new THREE.MeshBasicMaterial({ color, transparent: true, opacity, depthWrite: false, side: THREE.DoubleSide });
    const m = new THREE.Mesh(geo, mat);
    m.rotation.x = -Math.PI / 2;
    return m;
  }
  function render3D(opts) {
    if (!g3) { ensure3D(); if (!g3) return; }
    setCameraForOrientation(opts.orientation);
    resize3D();
    if (!g3.ready) return;
    const state = opts.state;
    // --- pieces: diff the board against live meshes, cloning templates ---
    const seen = new Set();
    for (let sq = 0; sq < 64; sq++) {
      const piece = state.board[sq];
      if (!piece) continue;
      seen.add(sq);
      const keyName = (colorOf(piece) === "w" ? "w" : "b") + kindOf(piece).toUpperCase();
      const cur = g3.pieces.get(sq);
      if (cur && cur.keyName === keyName) continue;
      if (cur) { g3.pieceGroup.remove(cur.obj); g3.pieces.delete(sq); }
      const tpl = g3.templates.pieces[keyName];
      if (!tpl) continue;
      const obj = tpl.clone(true);
      const p = sqWorld(sq);
      obj.position.set(p.x, TOP_Y, p.z);
      if (kindOf(piece) === "n") obj.rotation.y = colorOf(piece) === "w" ? 0 : Math.PI;
      if (opts.selected === sq) obj.position.y = TOP_Y + 0.006;
      g3.pieceGroup.add(obj);
      g3.pieces.set(sq, { keyName, obj });
    }
    for (const [sq, entry] of Array.from(g3.pieces.entries())) {
      if (!seen.has(sq)) { g3.pieceGroup.remove(entry.obj); g3.pieces.delete(sq); }
    }
    // Glide bookkeeping: remember when this glide started.
    const gk = view.glide ? view.glide.from + ">" + view.glide.to : "";
    if (gk !== glideKey) { glideKey = gk; glideStart = performance.now(); }
    if (view.burst) { if (view.burst.sq !== burstKey) { burstKey = view.burst.sq; burstStart = performance.now(); } }
    else burstKey = -1;
    // --- highlights ---
    while (g3.hlGroup.children.length) g3.hlGroup.remove(g3.hlGroup.children[0]);
    g3.checkMesh = null; g3.burstMesh = null;
    const addHl = (sq, mesh, y) => { const p = sqWorld(sq); mesh.position.set(p.x, TOP_Y + y, p.z); g3.hlGroup.add(mesh); };
    if (opts.lastMove) {
      addHl(opts.lastMove.from, flatPlane(SQ3 * 0.98, 0xfacc15, 0.30, null), 0.0016);
      addHl(opts.lastMove.to, flatPlane(SQ3 * 0.98, 0xfacc15, 0.30, null), 0.0016);
    }
    if (opts.checkSquare != null && opts.checkSquare >= 0) {
      g3.checkMesh = flatPlane(SQ3 * 0.98, 0xf43f5e, 0.45, null);
      addHl(opts.checkSquare, g3.checkMesh, 0.0022);
    }
    if (opts.starSquare != null && opts.starSquare >= 0) {
      addHl(opts.starSquare, flatPlane(SQ3 * 0.98, 0xfbbf24, 0.45, null), 0.0024);
    }
    if (opts.selected != null && opts.selected >= 0) {
      addHl(opts.selected, flatPlane(SQ3 * 0.98, 0x38bdf8, 0.35, null), 0.0026);
    }
    for (const m of opts.targets || []) {
      if (m.capture) addHl(m.to, flatPlane(SQ3, 0xf43f5e, 0.9, true), 0.003);
      else addHl(m.to, flatPlane(SQ3 * 0.34, 0x34d399, 0.95, false), 0.003);
    }
    if (view.focusSq != null && view.focusSq >= 0) {
      addHl(view.focusSq, flatPlane(SQ3, 0xffffff, 0.95, true), 0.0036);
    }
    if (view.burst) {
      g3.burstMesh = flatPlane(SQ3, 0xfbbf24, 0.9, true);
      addHl(view.burst.sq, g3.burstMesh, 0.0034);
    }
    drawFrame();
  }
  function drawFrame() {
    if (!g3 || !g3.ready) return;
    // Glide: slide the moved piece from its origin square to its target.
    if (view.glide && view.lastOpts) {
      const entry = g3.pieces.get(view.glide.to);
      if (entry) {
        const t = Math.min(1, (performance.now() - glideStart) / 260);
        const e = 1 - Math.pow(1 - t, 3);
        const a = sqWorld(view.glide.from), b = sqWorld(view.glide.to);
        entry.obj.position.set(a.x + (b.x - a.x) * e, TOP_Y + Math.sin(e * Math.PI) * 0.006, a.z + (b.z - a.z) * e);
      }
    }
    if (g3.checkMesh) g3.checkMesh.material.opacity = 0.32 + 0.22 * (0.5 + 0.5 * Math.sin(performance.now() / 280));
    if (g3.burstMesh && burstKey >= 0) {
      const t = Math.min(1, (performance.now() - burstStart) / 500);
      g3.burstMesh.scale.setScalar(0.6 + t * 0.9);
      g3.burstMesh.material.opacity = 0.9 * (1 - t);
    }
    g3.controls.update();
    g3.renderer.render(g3.scene, g3.camera);
    g3.dirty = false;
  }
  function startLoop() {
    if (!g3 || g3.raf) return;
    const tick = () => {
      g3.raf = requestAnimationFrame(tick);
      if (view.mode !== "3d" || wrap3d.hidden || wrapEl.offsetParent === null) return;
      // Render on demand: only while interacting, animating a glide/burst,
      // or pulsing a check highlight — idle frames cost nothing.
      const animating = view.glide || view.burst || (view.lastOpts && view.lastOpts.checkSquare != null && view.lastOpts.checkSquare >= 0);
      if (wrap3d.clientWidth && g3.width !== wrap3d.clientWidth) resize3D();
      if (g3.dirty || animating) drawFrame();
    };
    g3.raf = requestAnimationFrame(tick);
  }
  function stopLoop() {
    if (g3 && g3.raf) { cancelAnimationFrame(g3.raf); g3.raf = 0; }
  }

  boardViewRegistry.push(view);
  if (view.mode === "3d") view.setViewMode("3d");
  return view;
}

/* 2D / 3D toggle wiring — one shared preference across both modes. */
function refreshViewToggleUI() {
  document.querySelectorAll("[data-view]").forEach((b) => {
    const active = b.getAttribute("data-view") === boardViewMode;
    b.classList.toggle("active", active);
    b.setAttribute("aria-pressed", active ? "true" : "false");
  });
}
function initViewToggle(root, boardView) {
  root.querySelectorAll("[data-view]").forEach((b) => {
    b.addEventListener("click", () => {
      const mode = b.getAttribute("data-view");
      if (mode === boardViewMode && boardView.mode === mode) { if (mode === "3d") boardView.focus3D(); return; }
      for (const v of boardViewRegistry) v.setViewMode(mode);
      refreshViewToggleUI();
      sfx.select();
    });
  });
  refreshViewToggleUI();
}

/* Promotion picker + confetti (fx.tsx). */
function showPromotionPicker(wrapEl, color, onPick, onCancel) {
  hidePromotionPicker(wrapEl);
  const overlay = document.createElement("div");
  overlay.className = "promo-overlay";
  overlay.id = "promoOverlay";
  let buttons = "";
  for (const kind of ["q", "r", "b", "n"]) {
    buttons += '<button type="button" class="promo-btn" data-kind="' + kind + '" aria-label="' + PIECE_NAMES[kind] + 'に昇格">' + pieceSVG(kind, color, false) + "</button>";
  }
  overlay.innerHTML = '<div class="promo-card panel-in"><p style="text-align:center;font-size:14px;font-weight:700;margin:0">何に昇格しますか？</p>'
    + '<div class="promo-grid">' + buttons + "</div>"
    + '<button type="button" id="promoCancel" style="margin-top:12px;width:100%;border:0;background:transparent;padding:8px;font-size:14px;color:var(--dim);cursor:pointer">やめる</button></div>';
  wrapEl.appendChild(overlay);
  overlay.querySelectorAll(".promo-btn").forEach((b) => {
    b.addEventListener("click", () => { const k = b.getAttribute("data-kind"); hidePromotionPicker(wrapEl); onPick(k); });
  });
  overlay.querySelector("#promoCancel").addEventListener("click", () => { hidePromotionPicker(wrapEl); onCancel(); });
}
function hidePromotionPicker(wrapEl) {
  const el = wrapEl.querySelector("#promoOverlay");
  if (el) el.remove();
}
const CONFETTI_COLORS = ["#38bdf8", "#34d399", "#fbbf24", "#fb7185", "#e2e8f0", "#a78bfa"];
function fireConfetti() {
  // Prefer the canvas-confetti burst: the shell page inlines the
  // library and owns the anti-spam / reduced-motion guard in
  // window.celebrateBurst. Fall back to the DOM pieces below whenever
  // the library did not fire.
  if (window.celebrateBurst && window.celebrateBurst()) return;
  const layer = document.getElementById("confettiLayer");
  layer.innerHTML = "";
  for (let i = 0; i < 42; i++) {
    const size = 6 + Math.random() * 7;
    const span = document.createElement("span");
    span.className = "confetti-piece";
    span.style.left = Math.random() * 100 + "%";
    span.style.width = size + "px";
    span.style.height = size * (Math.random() > 0.5 ? 1 : 0.45) + "px";
    span.style.backgroundColor = CONFETTI_COLORS[i % CONFETTI_COLORS.length];
    span.style.animationDelay = Math.random() * 0.25 + "s";
    span.style.animationDuration = 1.5 + Math.random() * 1.1 + "s";
    span.style.borderRadius = Math.random() > 0.5 ? "50%" : "2px";
    layer.appendChild(span);
  }
  window.setTimeout(() => { layer.innerHTML = ""; }, 3200);
}

/* ============================================================
   Animated game holder — history + glide/burst/sound playback
   (useAnimatedGame.ts) and tap-to-move input (useTapMove.ts).
   ============================================================ */
function createGame(initialStates, initialMoves, initialSans, boardView, renderFn) {
  const game = {
    history: initialStates.slice(),
    moves: (initialMoves || []).slice(),
    sans: (initialSans || []).slice(),
    timers: [],
    later(fn, ms) { const t = window.setTimeout(fn, ms); game.timers.push(t); },
    get state() { return game.history[game.history.length - 1]; },
    get lastMove() {
      const m = game.moves[game.moves.length - 1];
      return m ? { from: m.from, to: m.to } : null;
    },
    applyAnimated(move, opts) {
      opts = opts || {};
      const cur = game.state;
      const piece = cur.board[move.from];
      const san = toSAN(cur, move);
      const next = applyMove(cur, move);
      game.history.push(next); game.moves.push(move); game.sans.push(san);
      if (piece) {
        boardView.glide = { piece, from: move.from, to: move.to };
        game.later(() => { boardView.glide = null; renderFn(); }, 300);
      }
      if (!opts.silent) {
        if (move.capture) {
          boardView.burst = { sq: move.to };
          game.later(() => { boardView.burst = null; renderFn(); }, 520);
          sfx.capture();
        } else if (isCheckmate(next) || isInCheck(next, next.turn)) sfx.check();
        else sfx.move();
      }
      renderFn();
      if (opts.onLanded) game.later(() => opts.onLanded(next), 300);
      return next;
    },
    truncate(plies) {
      game.history = game.history.slice(0, plies + 1);
      game.moves = game.moves.slice(0, plies);
      game.sans = game.sans.slice(0, plies);
      boardView.glide = null; boardView.burst = null;
      renderFn();
    },
    resetAll(start) {
      game.history = [start]; game.moves = []; game.sans = [];
      boardView.glide = null; boardView.burst = null;
      renderFn();
    },
  };
  return game;
}

function createTapMove(getState, isEnabled, onMove, onIllegalTap, renderFn) {
  const tap = {
    selected: null,
    promo: null,
    targets: [],
    refresh() {
      if (tap.selected === null || !isEnabled()) { tap.targets = []; return; }
      tap.targets = legalMoves(getState()).filter((m) => m.from === tap.selected);
    },
    clearSelection() { tap.selected = null; tap.promo = null; tap.targets = []; },
    handleTap(sq) {
      if (!isEnabled() || tap.promo) return;
      const state = getState();
      const piece = state.board[sq];
      tap.refresh();
      if (tap.selected !== null) {
        const candidates = tap.targets.filter((m) => m.to === sq);
        if (candidates.length > 0) {
          if (candidates[0].promotion) { tap.promo = { moves: candidates }; sfx.select(); renderFn(); return; }
          tap.clearSelection();
          onMove(candidates[0]);
          return;
        }
        if (sq === tap.selected) { tap.selected = null; tap.targets = []; renderFn(); return; }
        if (piece && colorOf(piece) === state.turn) { tap.selected = sq; sfx.select(); tap.refresh(); renderFn(); return; }
        onIllegalTap();
        return;
      }
      if (piece && colorOf(piece) === state.turn) { tap.selected = sq; sfx.select(); tap.refresh(); renderFn(); }
    },
    choosePromo(kind) {
      if (!tap.promo) return;
      const move = tap.promo.moves.find((m) => m.promotion === kind) || tap.promo.moves[0];
      tap.clearSelection();
      if (move) onMove(move);
    },
    cancelPromo() { tap.promo = null; renderFn(); },
  };
  return tap;
}
/* ============================================================
   Puzzle catalog — the unified set (all quizzes merged into
   this one app).
   #1: verified built-in (Opera Mate), python-chess verified.
   #2: back-rank deflection — python-chess 1.x verified at build
       time: exactly one key move (Qd8+), no mate in 1, Black's
       only legal reply Rxd8, then Rxd8#.
   #3: smothered mate — python-chess verified at build time:
       exactly one key move (Qg8+), only legal reply Rxg8,
       then Nf7# (king smothered by its own rook and pawns).
   #4: daily puzzle 2026-10-26 (queen-and-rook mate;
       python-chess verified: only key move Qf7+, only reply
       Kh8, then Rh6#).
   #5: daily puzzle 2026-10-27 (forced block; python-chess
       verified: only key move Bf6+, only reply Qg7, then Qxg7#).
   #4/#5 texts are faithful Japanese renderings of the English
   originals; FEN, solution and theme are verbatim.
   Added 2026-10-29 (20 puzzles, catalog now 25; every one
   python-chess verified: unique key move, and a unique mating
   move against every legal reply):
   #6/#7: daily puzzles 2026-10-28 / 2026-10-29.
   #8–#13: from the verified candidate pool (unique solutions
       re-verified with python-chess).
   #14–#25: Lichess puzzles (PuzzleIds TwqrG, sQ6sx, vwEUQ,
       5USup, xtq4M, vwFfB, vwDtu, osM21, vwFiW, sQ578, TwpDp,
       1RxcE; ratings 849–1474).
   FEN and solution lines for #6–#25 are verbatim.
   ============================================================ */
const PUZZLES = [
  {
    id: "opera-mate-2",
    title: "第1問 — 2手で詰み",
    intro: "白の手番。2手で黒を詰ませる手があります。駒をタップして、自分で動かして解いてみましょう。",
    source: "パリ・オペラ座、1858年（Opera Mate）の最終局面",
    theme: "deflection（守りの駒を逸らす）",
    fen: "4kb1r/p2n1ppp/4q3/4p1B1/4P3/1Q6/PPP2PPP/2KR4 w k - 1 16",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンを使う手です。",
      "クイーンを犠牲にする（捨てる）手です。取らせることで何が変わるか、考えてみましょう。",
      "初手は Qb8+ — クイーンを b8 に置いてチェック。d7 のナイトに取らせる手です。",
    ],
    solutionUci: ["b3b8", "d7b8", "d1d8"],
    keyLine: "A sacrifice can pull a defender away from its job.",
    explanation: [
      "初手は 1. Qb8+! — クイーンの犠牲です。黒の応手は 1... Nxb8 しかありません（キングは逃げられず、他の駒では取れません）。",
      "ポイントは d7 のナイトの「二役」です。このナイトは、詰みのマス d8 を守る番人でありながら、b8 で駒を取れる唯一の駒でもありました。クイーンを差し出すことで、ナイトは守りのポストを離れざるを得なくなります（deflection（逸らし）という手筋です）。",
      "守りの外れた d8 に 2. Rd8# とルークが入って詰み。d8 のマスは g5 のビショップが守っていて、黒のキングにもクイーンにも止められません。",
    ],
  },
  {
    id: "backrank-decoy-2",
    title: "第2問 — 2手で詰み",
    intro: "白の手番。黒のキングは自分のポーンに囲まれて、身動きが取れません。2手で詰ませてみましょう。",
    source: "バックランク（最終段）の詰みを題材にした作題局面（python-chess で一意解を検証済み）",
    theme: "おとりの犠牲とバックランク",
    fen: "r5k1/5ppp/8/8/8/8/3Q4/3R2K1 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "最終段（8段目）に目をつけましょう。黒のキングは f7・g7・h7 のポーンに囲まれて逃げ場がありません。",
      "クイーンを犠牲にする手です。a8 のルークに取らせることで、最終段の守りを崩します。",
      "初手は Qd8+ — クイーンを d8 に置いてチェック。黒はルークで取るしかありません。",
    ],
    solutionUci: ["d2d8", "a8d8", "d1d8"],
    keyLine: "A decoy sacrifice can pull the last defender off the back rank.",
    explanation: [
      "初手は 1. Qd8+! — 最終段へのクイーンの犠牲です。キングはポーンに囲まれて逃げられず、合駒もできないので、黒の応手は 1... Rxd8 しかありません。",
      "ポイントは「守りの要」を引きはがすことです。a8 のルークは最終段を守る要でしたが、クイーンを取るために d8 へ出てきてしまいました。",
      "そこへ 2. Rxd8# — もう1本のルークが最終段に残ります。d8 のルークは f8 と h8 を押さえ、キングは自分のポーンに囲まれたまま詰みです（バックランクメイト）。",
    ],
  },
  {
    id: "smothered-2",
    title: "第3問 — 2手で詰み",
    intro: "白の手番。黒のキングは角っこで自分の駒に囲まれています。2手で詰ませてみましょう。",
    source: "窒息詰み（スモザードメイト）を題材にした作題局面（python-chess で一意解を検証済み）",
    theme: "窒息詰み（スモザードメイト）",
    fen: "r6k/6pp/7N/8/8/1Q6/8/6K1 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "最後はナイトが詰ませます。ナイトのチェックは合駒ができず、キングが自分の駒に囲まれていると逃げ場がありません。",
      "クイーンを犠牲にする手です。a8 のルークを g8 のマスに引き寄せると、キングの逃げ場がふさがります。",
      "初手は Qg8+ — クイーンを g8 に置いてチェック。h6 のナイトが守っているので、キングは取れません。",
    ],
    solutionUci: ["b3g8", "a8g8", "h6f7"],
    keyLine: "A knight can mate a king that is trapped by its own pieces.",
    explanation: [
      "初手は 1. Qg8+! — クイーンの犠牲です。g8 は h6 のナイトが守っているのでキングは取れず、黒の応手は 1... Rxg8 しかありません。",
      "ポイントは、そのルークがキングの逃げ場を埋めてしまうことです。h8 のキングは g8 の自分のルーク、g7・h7 の自分のポーンに四方を囲まれます。",
      "そこへ 2. Nf7# — ナイトのチェックは合駒ができず、キングは自分の駒に窒息させられたまま詰みです（窒息詰み／スモザードメイト）。",
    ],
  },
  {
    id: "2026-10-26-mate2-queen-rook",
    title: "第4問 — 2手で詰み",
    intro: "白の手番。黒のキングの逃げ場を数えてみましょう。2手で詰ませてみましょう。",
    source: "毎日のクイズ 2026-10-26 出題分（python-chess で検証済み）",
    theme: "クイーンとルークの詰み",
    fen: "8/6k1/1K3R2/8/8/7n/Q7/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "黒のキングを見ましょう。どこへ逃げられますか？",
      "クイーンのチェックで、キングを角へ追い込む手です。",
      "初手は Qf7+ — クイーンを f7 に置いてチェック。キングの逃げ場は1つだけになります。あとはルークで扉を閉めましょう。",
    ],
    solutionUci: ["a2f7", "g7h8", "f6h6"],
    keyLine: "A queen check can push the king into a corner, and then the rook closes the door.",
    explanation: [
      "初手は 1. Qf7+! — クイーンのチェックで黒のキングを角へ追い込みます。キングの応手は 1... Kh8 しかありません（クイーンを取る手は f6 のルークが守っていてできません）。",
      "ポイントは逃げ場の数です。f7 のクイーンは g8 と g7 を押さえているので、キングは h8 の角に押し込まれます。",
      "そこへ 2. Rh6# — ルークが h ファイルから詰ませます。h6 のルークは h7・h8 を押さえ、g8・g7 はクイーンが守っていて、キングは身動きできません。",
    ],
  },
  {
    id: "2026-10-27-mate2-bishop-block",
    title: "第5問 — 2手で詰み",
    intro: "白の手番。黒のキングには安全なマスがほとんどありません。2手で詰ませてみましょう。",
    source: "毎日のクイズ 2026-10-27 出題分（python-chess で検証済み：初手は唯一手、応手は強制、詰み手も唯一）",
    theme: "合駒の強制とそらし",
    fen: "6qk/8/6Q1/2K5/7B/8/8/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "黒のキングを見ましょう。安全なマスがほとんどありません。",
      "ビショップのチェックで、黒のクイーンに割り込ませる（合駒させる）手です。",
      "初手は Bf6+ — ビショップを f6 に置いてチェック。黒はクイーンを g7 に置いて受けるしかありません。その合駒を取る手が詰みです。",
    ],
    solutionUci: ["h4f6", "g8g7", "g6g7"],
    keyLine: "A check can force a defender to block — and then the block itself becomes the target.",
    explanation: [
      "初手は 1. Bf6+! — ビショップのチェックです。黒のキングは逃げ場がなく、応手は 1... Qg7 とクイーンで受けるしかありません。",
      "ポイントは、受けに来た駒そのものが的になることです。g7 に出てきたクイーンは、キングのそばで白のクイーンの射程に入ります。",
      "そこへ 2. Qxg7# — クイーンがその合駒を取って詰み。g7 のクイーンは f6 のビショップが守っているので、黒のキングは取れません。逃げ場の g8・h7 もクイーンが押さえています。",
    ],
  },
  {
    id: "2026-10-28-mate2-remove-guard",
    title: "第6問 — 2手で詰み",
    intro: "白の手番。詰ませたいマスを守っている駒に目をつけましょう。2手で詰ませてみましょう。",
    source: "毎日のクイズ 2026-10-28 出題分（python-chess で検証済み）",
    theme: "守りの駒の除去",
    fen: "8/7k/5Q2/6n1/8/3KR3/8/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "詰ませたいマスは h3 です。でも、そのマスを守っている黒の駒がいます。",
      "その守りの駒を取り除く手です。守りが消えれば、ルークの入る場所が開きます。",
      "初手は Qxg5 — クイーンが g5 のナイトを取ります。キングは h8 へ逃げるしかありません。あとはルークで詰ませましょう。",
    ],
    solutionUci: ["f6g5", "h7h8", "e3h3"],
    keyLine: "Take away the piece that guards the mating square.",
    explanation: [
      "初手は 1. Qxg5! — 詰みのマス h3 を守っていた g5 のナイトを、クイーンが取り除きます。守りが消えたあと、黒のキングの応手は 1... Kh8 しかありません（g5 のクイーンが周りの逃げ場を押さえています）。",
      "ポイントは「守りの駒の除去」です。詰ませたいマスを守る駒さえ消えれば、チェックをかけなくても詰みの形ができあがります。",
      "そこへ 2. Rh3# — ルークが h ファイルから詰ませます。h3 にはもう守りがなく、キングは角に閉じ込められたまま詰みです。",
    ],
  },
  {
    id: "2026-10-29-mate2-corner-bishop",
    title: "第7問 — 2手で詰み",
    intro: "白の手番。黒のキングは盤の端にいます。隅まで追い込んでみましょう。2手で詰ませてみましょう。",
    source: "毎日のクイズ 2026-10-29 出題分（python-chess で検証済み）",
    theme: "隅への追い込み",
    fen: "8/8/8/1Q6/1BK2n2/8/6R1/1k6 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ビショップのチェックから始めましょう。",
      "キングを a1 の隅へ追い込む手です。隅に追い込めば、逃げ場はほとんどなくなります。",
      "初手は Ba3+ — ビショップを a3 に置いてチェック。キングは a1 へ逃げるしかありません。あとはクイーンで扉を閉めましょう。",
    ],
    solutionUci: ["b4a3", "b1a1", "b5b2"],
    keyLine: "Push the king into the corner, then close the door.",
    explanation: [
      "初手は 1. Ba3+! — ビショップのチェックで黒のキングを a1 の隅へ追い込みます。キングの応手は 1... Ka1 しかありません。",
      "ポイントは隅の狭さです。a1 のキングが逃げられるマスはわずかで、その全部をクイーン1枚で押さえられます。",
      "そこへ 2. Qb2# — クイーンが b2 で詰ませます。b2 のクイーンは a3 のビショップが守っているので、キングは取れません。",
    ],
  },
  {
    id: "pool-mate2-queen-rook-net",
    title: "第8問 — 2手で詰み",
    intro: "白の手番。クイーンとルークの連携で詰ませます。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "クイーンとルークの連携",
    fen: "1rQB4/8/3k4/5R2/8/8/8/5K2 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンのチェックから始めましょう。",
      "キングを盤の中央寄りへ追い出す手です。追い出した先で、ルークの利きとクイーンの利きが重なります。",
      "初手は Qc7+ — クイーンを c7 に置いてチェック。キングは e6 へ逃げるしかありません。あとはルークで詰ませましょう。",
    ],
    solutionUci: ["c8c7", "d6e6", "f5e5"],
    keyLine: "Drive the king onto the square where your queen and rook cross.",
    explanation: [
      "初手は 1. Qc7+! — クイーンのチェックで黒のキングを e6 へ追い出します。キングの応手は 1... Ke6 しかありません。",
      "ポイントは、クイーンとルークの利きが交わるマスへキングを誘い出すことです。e6 はその交点で、周りの逃げ場も2枚の利きに覆われています。",
      "そこへ 2. Re5# — ルークが e5 で詰ませます。e5 のルークは c7 のクイーンが守っているので、キングは取れません。",
    ],
  },
  {
    id: "pool-mate2-bishop-queen-corner",
    title: "第9問 — 2手で詰み",
    intro: "白の手番。黒のキングは盤の端に寄っています。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "隅のキングへの詰み",
    fen: "8/8/k7/7K/1Q3R2/7B/3q4/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ビショップのチェックから始めましょう。",
      "キングを a7 へ追い込む手です。詰ませるマスは、ビショップが守っているマスです。",
      "初手は Bc8+ — ビショップを c8 に置いてチェック。キングは a7 へ逃げるしかありません。あとはクイーンで詰ませましょう。",
    ],
    solutionUci: ["h3c8", "a6a7", "b4b7"],
    keyLine: "Check with the bishop, and the queen mates on the square the bishop guards.",
    explanation: [
      "初手は 1. Bc8+! — ビショップのチェックで a6 のキングを a7 へ追い込みます。キングの応手は 1... Ka7 しかありません。",
      "ポイントは、ビショップが詰ませるマスそのものを守っていることです。ビショップはチェックをかけながら、クイーンの行き先 b7 もカバーしています。",
      "そこへ 2. Qb7# — クイーンが b7 で詰ませます。b7 のクイーンは c8 のビショップが守っているので、キングは取れません。",
    ],
  },
  {
    id: "pool-mate2-capture-queen",
    title: "第10問 — 2手で詰み",
    intro: "白の手番。黒には強いクイーンがいますが、それがかえって弱点になります。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "強い駒の除去",
    fen: "5K2/1Q6/8/8/1B6/R7/q7/5k2 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "まず黒のいちばん強い駒に目をつけましょう。",
      "ルークで黒のクイーンを取る手です。取ったあと、キングの逃げ場は1つだけになります。",
      "初手は Rxa2 — ルークが a2 の黒クイーンを取ります。キングは g1 へ逃げるしかありません。あとはクイーンで詰ませましょう。",
    ],
    solutionUci: ["a3a2", "f1g1", "b7g2"],
    keyLine: "Sometimes the fastest mate starts by capturing the opponent's strongest piece.",
    explanation: [
      "初手は 1. Rxa2! — ルークが黒のクイーンを取ります。チェックではありませんが、黒のキングの応手は 1... Kg1 しかありません（他のマスは白の駒の利きに覆われています）。",
      "ポイントは、相手の最強の駒を取り除くことで盤全体が静かになることです。反撃の手がなくなり、詰みの形だけが残ります。",
      "そこへ 2. Qg2# — クイーンが g2 で詰ませます。g2 のクイーンは a2 のルークが同じ2段目から守っているので、キングは取れません。",
    ],
  },
  {
    id: "pool-mate2-bishop-finish",
    title: "第11問 — 2手で詰み",
    intro: "白の手番。最後に詰ませるのは、静かに待っているビショップです。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "ビショップの詰み",
    fen: "8/8/2B5/6n1/8/2Q5/8/2K3k1 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンのチェックで、キングを追い込みましょう。",
      "キングを f1 へ追い込む手です。詰ませるビショップの対角線が、キングの逃げ場を1つ押さえています。",
      "初手は Qg3+ — クイーンを g3 に置いてチェック。キングは f1 へ逃げるしかありません。あとはビショップで詰ませましょう。",
    ],
    solutionUci: ["c3g3", "g1f1", "c6b5"],
    keyLine: "The queen herds the king, and the quiet bishop delivers the mate.",
    explanation: [
      "初手は 1. Qg3+! — クイーンのチェックで黒のキングを f1 へ追い込みます。キングの応手は 1... Kf1 しかありません。",
      "ポイントは役割分担です。クイーンがキングを追い込み、残りの逃げ場を押さえるあいだ、ビショップは静かに詰みの一手を待っています。",
      "そこへ 2. Bb5# — ビショップが詰ませます。ビショップの対角線が e2 を押さえ、残りの逃げ場はクイーンがカバーしているので、キングは身動きできません。",
    ],
  },
  {
    id: "pool-mate2-knight-support",
    title: "第12問 — 2手で詰み",
    intro: "白の手番。盤の中央でも、守りがあればクイーンは詰ませられます。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "ナイトに守られたクイーンの詰み",
    fen: "8/8/1Q6/1p1k4/3N4/1n2K3/8/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンのチェックから始めましょう。",
      "キングを中央の e5 へ追い出す手です。中央は開けていますが、クイーンを守る駒がいます。",
      "初手は Qc6+ — クイーンを c6 に置いてチェック。キングは e5 へ逃げるしかありません。あとはクイーンをもう一歩進めましょう。",
    ],
    solutionUci: ["b6c6", "d5e5", "c6e6"],
    keyLine: "A queen can mate in the center when a knight stands guard over her.",
    explanation: [
      "初手は 1. Qc6+! — クイーンのチェックで黒のキングを中央の e5 へ追い出します。キングの応手は 1... Ke5 しかありません。",
      "ポイントはナイトの守りです。中央は逃げ場が多い場所ですが、クイーンを守る駒さえいれば、キングの目の前でも詰ませられます。",
      "そこへ 2. Qe6# — クイーンが e6 で詰ませます。e6 のクイーンは d4 のナイトが守っているので、キングは目の前でも取れません。",
    ],
  },
  {
    id: "pool-mate2-pawn-capture",
    title: "第13問 — 2手で詰み",
    intro: "白の手番。駒を取りながらチェックできる手があります。2手で詰ませてみましょう。",
    source: "検証済み候補プールより（python-chess で一意解を検証済み）",
    theme: "ポーンを取りながらのチェック",
    fen: "6K1/8/3nRB2/4p3/6Q1/8/7k/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ポーンを取りながらチェックできる駒を探しましょう。",
      "ビショップでポーンを取るチェックです。キングは隅へ逃げるしかなくなります。",
      "初手は Bxe5+ — ビショップが e5 のポーンを取りながらチェック。キングは h1 へ逃げるしかありません。あとはルークで詰ませましょう。",
    ],
    solutionUci: ["f6e5", "h2h1", "e6h6"],
    keyLine: "Capture with check, and the king runs out of corners.",
    explanation: [
      "初手は 1. Bxe5+! — ビショップがポーンを取りながらチェックします。黒のキングの応手は 1... Kh1 と隅へ逃げるしかありません。",
      "ポイントは「取りながらチェック」の速さです。相手に逃げ場を選ぶ余裕を与えず、隅へ一直線に追い込めます。",
      "そこへ 2. Rh6# — ルークが h ファイルから詰ませます。h1 のキングは隅に閉じ込められ、逃げ場がありません。",
    ],
  },
  {
    id: "lichess-twqrg",
    title: "第14問 — 2手で詰み",
    intro: "白の手番。最終段の詰みが見えますが、黒にも受ける駒があります。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: TwqrG、Rating 849、python-chess で検証済み）",
    theme: "合駒を取るバックランク",
    fen: "6k1/pr3ppp/4pn2/8/3R4/1P3P2/P2K1PPP/2r5 w - - 0 25",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "最終段（8段目）に目をつけましょう。ルークのチェックです。",
      "黒はナイトで合駒してきます。その合駒をどうしますか？",
      "初手は Rd8+ — ルークを d8 に置いてチェック。黒はナイトを e8 に置いて受けるしかありません。その合駒を取る手が詰みです。",
    ],
    solutionUci: ["d4d8", "f6e8", "d8e8"],
    keyLine: "If the block can be captured, the back rank falls.",
    explanation: [
      "初手は 1. Rd8+! — ルークのチェックです。キングは逃げられず、黒の応手は 1... Ne8 とナイトで合駒するしかありません。",
      "ポイントは、その合駒が取れることです。守りに来た駒が取られてしまえば、合駒は詰みを遅らせるだけで止められません。",
      "そこへ 2. Rxe8# — ルークが合駒を取って詰み。最終段が崩れるバックランクメイトです。",
    ],
  },
  {
    id: "lichess-sq6sx",
    title: "第15問 — 2手で詰み",
    intro: "白の手番。隅へのクイーンのチェックが決め手です。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: sQ6sx、Rating 958、python-chess で検証済み）",
    theme: "合駒を取る詰み",
    fen: "2r1k3/1p2pb2/pq1pP2Q/7p/5P2/2Nr4/1PP5/2KB4 w - - 0 31",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンを隅まで進めるチェックを探しましょう。",
      "黒はビショップで合駒してきます。その合駒を取る手が詰みです。",
      "初手は Qh8+ — クイーンを h8 に置いてチェック。黒はビショップを g8 に置いて受けるしかありません。その合駒を取りましょう。",
    ],
    solutionUci: ["h6h8", "f7g8", "h8g8"],
    keyLine: "A check in the corner forces a block — then take the block with mate.",
    explanation: [
      "初手は 1. Qh8+! — 隅へのクイーンのチェックです。キングは動けず、黒の応手は 1... Bg8 とビショップで合駒するしかありません。",
      "ポイントは、合駒のマスそのものがクイーンの射程にあることです。受けに来たビショップは、キングの逃げ場をふさぎながら取られる運命にあります。",
      "そこへ 2. Qxg8# — クイーンがその合駒を取って詰みです。",
    ],
  },
  {
    id: "lichess-vweuq",
    title: "第16問 — 2手で詰み",
    intro: "白の手番。黒のキングはポーンの盾の後ろにいます。その盾を崩しましょう。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: vwEUQ、Rating 994、python-chess で検証済み）",
    theme: "ポーンの盾を崩すチェック",
    fen: "1r1q1r1k/2p1np1B/4p1p1/p1bbP3/3n1P2/P1N4Q/5RPP/R1B4K w - - 0 23",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "キングの前にあるポーンを取りながらチェックできる駒を探しましょう。",
      "ビショップでポーンを取るチェックです。キングがどちらへ逃げても、詰ませる手は同じです。",
      "初手は Bxg6+ — ビショップが g6 のポーンを取りながらチェック。キングは g7 でも g8 でも逃げられますが、どちらでも同じ手で詰みます。",
    ],
    solutionUci: ["h7g6", "h8g7", "h3h7"],
    keyLine: "Break the pawn shield with check, and every escape leads to the same mate.",
    explanation: [
      "初手は 1. Bxg6+! — ビショップがキングの前のポーンを取りながらチェックします。キングは g7 へも g8 へも逃げられますが、どちらを選んでも結末は同じです。",
      "ポイントは、逃げ場が2つあっても詰みの手が1つで足りることです。h7 のマスは、どちらの逃げ場からも止められません。",
      "そこへ 2. Qh7# — クイーンが h7 で詰ませます。キングが g7 でも g8 でも、この一手で詰みです。",
    ],
  },
  {
    id: "lichess-5usup",
    title: "第17問 — 2手で詰み",
    intro: "白の手番。ナイトのチェックとルークの詰み、2つの駒の連携です。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: 5USup、Rating 1066、python-chess で検証済み）",
    theme: "ナイトのチェックとルークの詰み",
    fen: "4rk2/1p3ppp/p1p5/3nN3/8/1P5P/1P3PP1/4R1K1 w - - 3 26",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ナイトのチェックから始めましょう。ナイトのチェックは合駒ができません。",
      "キングを g8 へ追い込む手です。追い込んだ先の最終段に、ルークが入ります。",
      "初手は Nd7+ — ナイトを d7 に置いてチェック。キングは g8 へ逃げるしかありません。あとはルークで詰ませましょう。",
    ],
    solutionUci: ["e5d7", "f8g8", "e1e8"],
    keyLine: "The knight's check pushes the king to the corner, and the rook finishes on the back rank.",
    explanation: [
      "初手は 1. Nd7+! — ナイトのチェックで黒のキングを g8 へ追い込みます。キングの応手は 1... Kg8 しかありません。",
      "ポイントは、ナイトがキングを追い出す役、ルークが詰ませる役という分担です。g8 のキングは最終段から逃げられません。",
      "そこへ 2. Rxe8# — ルークが e8 のルークを取りながら詰み。バックランクメイトです。",
    ],
  },
  {
    id: "lichess-xtq4m",
    title: "第18問 — 2手で詰み",
    intro: "白の手番。ポーンを取りながらのクイーンのチェックが決め手です。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: xtq4M、Rating 1067、python-chess で検証済み）",
    theme: "ポーンを取りながらのチェック",
    fen: "r2q1rk1/ppp2p2/3p1n1P/4bPp1/2P3Q1/5R1K/PP4P1/R1B5 w - - 4 26",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ポーンを取りながらチェックできるクイーンの手を探しましょう。",
      "キングがどちらへ逃げても、詰ませる手は同じです。",
      "初手は Qxg5+ — クイーンが g5 のポーンを取りながらチェック。キングは h7 でも h8 でも逃げられますが、どちらでも同じ手で詰みます。",
    ],
    solutionUci: ["g4g5", "g8h7", "g5g7"],
    keyLine: "Take the pawn with check, and the same queen move mates on both squares.",
    explanation: [
      "初手は 1. Qxg5+! — クイーンがポーンを取りながらチェックします。キングは h7 へも h8 へも逃げられますが、どちらを選んでも結末は同じです。",
      "ポイントは、逃げ場が2つあっても詰みの手が1つで足りることです。g7 のマスは、どちらの逃げ場からも止められません。",
      "そこへ 2. Qg7# — クイーンが g7 で詰ませます。キングが h7 でも h8 でも、この一手で詰みです。",
    ],
  },
  {
    id: "lichess-vwffb",
    title: "第19問 — 2手で詰み",
    intro: "白の手番。ルークの通り道をふさいでいるのは、相手のポーンです。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: vwFfB、Rating 1119、python-chess で検証済み）",
    theme: "ナイトの犠牲でファイルを開く",
    fen: "4r2k/b5pp/p1p2p2/5P2/1p3N2/1B3R2/PP4KP/4r3 w - - 2 32",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ナイトを捨てるチェックがあります。",
      "ナイトの犠牲で、ポーンに取らせる手です。ポーンが動くと、ルークのファイルが開きます。",
      "初手は Ng6+ — ナイトを g6 に置いてチェック。黒はポーンで取るしかありません。取ったあと、開いたファイルにルークが入ります。",
    ],
    solutionUci: ["f4g6", "h7g6", "f3h3"],
    keyLine: "Sacrifice the knight to tear open the file your rook needs.",
    explanation: [
      "初手は 1. Ng6+! — ナイトを捨てるチェックです。黒の応手は 1... hxg6 とポーンで取るしかありません。",
      "ポイントは、そのポーンが h ファイルの扉だったことです。ポーンが g6 へ動いたことで、ルークの通り道が開きました。",
      "そこへ 2. Rh3# — ルークが開いた h ファイルから詰ませます。",
    ],
  },
  {
    id: "lichess-vwdtu",
    title: "第20問 — 2手で詰み",
    intro: "白の手番。端のルークのチェックで、キングを追い出しましょう。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: vwDtu、Rating 1228、python-chess で検証済み）",
    theme: "ルークのチェックで追い出す",
    fen: "1r3rk1/5p2/2pb1np1/p2p1q2/8/P1N1P2R/1PP1K3/R1B4Q w - - 0 28",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ルークを端まで進めるチェックを探しましょう。",
      "キングを g7 へ追い出す手です。追い出した先には、クイーンが待ち構えています。",
      "初手は Rh8+ — ルークを h8 に置いてチェック。キングは g7 へ逃げるしかありません。あとはクイーンで詰ませましょう。",
    ],
    solutionUci: ["h3h8", "g8g7", "h1h6"],
    keyLine: "A rook check at the edge drives the king out, where the queen is waiting.",
    explanation: [
      "初手は 1. Rh8+! — 端のルークのチェックで黒のキングを g7 へ追い出します。キングの応手は 1... Kg7 しかありません。",
      "ポイントは、キングを「安全そうな場所」から引き出すことです。g7 は開けたマスですが、そこはクイーンの射程のど真ん中でした。",
      "そこへ 2. Qh6# — クイーンが h6 で詰ませます。追い出されたキングは、逃げ場をすべて押さえられています。",
    ],
  },
  {
    id: "lichess-osm21",
    title: "第21問 — 2手で詰み",
    intro: "白の手番。キングが動けない局面です。ナイトのチェックが決め手になります。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: osM21、Rating 1289、python-chess で検証済み）",
    theme: "ナイトのチェックと合駒取り",
    fen: "r1bq3k/pppp1rpN/8/4p3/4P3/7Q/PPPPnbPP/RNB4K w - - 0 13",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ナイトのチェックから始めましょう。ナイトが動くと、クイーンの利きも開きます。",
      "黒はビショップで合駒してきます。その合駒を取る手が詰みです。",
      "初手は Nf6+ — ナイトを f6 に置いてチェック。キングは動けず、黒はビショップを h4 に置いて受けるしかありません。その合駒をクイーンで取りましょう。",
    ],
    solutionUci: ["h7f6", "f2h4", "h3h4"],
    keyLine: "The knight's check forces a block, and the block becomes the target.",
    explanation: [
      "初手は 1. Nf6+! — ナイトのチェックです。h7 のナイトが動いたことでクイーンの利きも開き、黒のキングは動けません。応手は 1... Bh4 とビショップで受けるしかありません。",
      "ポイントは、受けに来た合駒そのものが的になることです。h4 のビショップは、キングを守るどころかクイーンの射程に飛び込んできました。",
      "そこへ 2. Qxh4# — クイーンがその合駒を取って詰み。チェックは解けず、キングは逃げ場をすべて押さえられています。",
    ],
  },
  {
    id: "lichess-vwfiw",
    title: "第22問 — 2手で詰み",
    intro: "白の手番。クイーンを捨てる手が、最終段への扉を開きます。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: vwFiW、Rating 1299、python-chess で検証済み）",
    theme: "クイーンの犠牲とバックランク",
    fen: "3Q1rk1/1R4pp/1p5q/p1r1b3/8/1P4PP/P4P2/3R2K1 w - - 2 30",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "最終段（8段目）に目をつけましょう。でも、いまのままではキングが逃げてしまいます。",
      "クイーンを犠牲にして、キングを最終段へ引き出す手です。もう1本のルークが、キングの逃げ場を押さえています。",
      "初手は Qxf8+ — クイーンが f8 のルークを取りながらチェック。キングはクイーンを取るしかありません。あとは残ったルークで詰ませましょう。",
    ],
    solutionUci: ["d8f8", "g8f8", "d1d8"],
    keyLine: "Give up the queen to drag the king onto the back rank.",
    explanation: [
      "初手は 1. Qxf8+! — クイーンの犠牲です。黒の応手は 1... Kxf8 とキングが取るしかありません。",
      "ポイントは、キングを最終段へ引き出すことです。f8 に出てきたキングは、もう1本のルーク（b7）が逃げ場の e7 を押さえているため、身動きが取れません。",
      "そこへ 2. Rd8# — ルークが最終段で詰ませます。バックランクメイトです。",
    ],
  },
  {
    id: "lichess-sq578",
    title: "第23問 — 2手で詰み",
    intro: "白の手番。最終段へのチェックに、黒は最強の駒で受けてきます。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: sQ578、Rating 1380、python-chess で検証済み）",
    theme: "合駒を取るバックランク",
    fen: "6k1/pb1R1rpp/1pq5/2p5/2B2P2/2P3P1/P6P/5K2 w - - 0 25",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "最終段（8段目）へのルークのチェックから始めましょう。",
      "黒はクイーンで合駒してきます。でも、キングの逃げ場はすでに押さえられています。",
      "初手は Rd8+ — ルークを d8 に置いてチェック。黒はクイーンを e8 に置いて受けるしかありません。その合駒を取る手が詰みです。",
    ],
    solutionUci: ["d7d8", "c6e8", "d8e8"],
    keyLine: "Even the queen cannot block the back rank when every flight square is covered.",
    explanation: [
      "初手は 1. Rd8+! — ルークのチェックです。キングは逃げられず、黒の応手は 1... Qe8 とクイーンで合駒するしかありません。",
      "ポイントは、合駒の前に逃げ場が消えていることです。キングの逃げ場 f7 は c4 のビショップが押さえていて、合駒しても詰みは止まりません。",
      "そこへ 2. Rxe8# — ルークが合駒のクイーンを取って詰み。バックランクメイトです。",
    ],
  },
  {
    id: "lichess-twpdp",
    title: "第24問 — 2手で詰み",
    intro: "白の手番。キングに届かない場所から、ナイトがチェックをかけます。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: TwpDp、Rating 1393、python-chess で検証済み）",
    theme: "ナイトのチェック",
    fen: "r7/p5pk/3q2Np/2pb4/2PpQ3/3P3P/P5P1/5RK1 w - - 7 28",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "ナイトのチェックから始めましょう。ナイトは、キングが取れないマスからチェックできます。",
      "キングがどちらへ逃げても、詰ませる手は同じです。",
      "初手は Nf8+ — ナイトを f8 に置いてチェック。キングは g8 でも h8 でも逃げられますが、どちらでも同じ手で詰みます。",
    ],
    solutionUci: ["g6f8", "h7g8", "e4h7"],
    keyLine: "The knight checks from a square the king cannot reach, and the queen closes in.",
    explanation: [
      "初手は 1. Nf8+! — ナイトのチェックです。キングは g8 へも h8 へも逃げられますが、どちらを選んでも結末は同じです。",
      "ポイントは、ナイトがキングの手の届かないマスからチェックしていることです。追い払うことも取られることもなく、クイーンの詰みを支え続けます。",
      "そこへ 2. Qh7# — クイーンが h7 で詰ませます。キングが g8 でも h8 でも、この一手で詰みです。",
    ],
  },
  {
    id: "lichess-1rxce",
    title: "第25問 — 2手で詰み",
    intro: "白の手番。チェック、合駒、取り返して詰み — 覚えておきたい基本の型です。2手で詰ませてみましょう。",
    source: "Lichess パズル（PuzzleId: 1RxcE、Rating 1474、python-chess で検証済み）",
    theme: "合駒を取る詰み",
    fen: "7k/p1q3bp/2ppQ1p1/5r2/P4p2/2BnP3/6KP/R4R2 w - - 0 27",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "クイーンのチェックから始めましょう。",
      "黒はルークで合駒してきます。その合駒を取る手が詰みです。",
      "初手は Qe8+ — クイーンを e8 に置いてチェック。黒はルークを f8 に置いて受けるしかありません。その合駒を取りましょう。",
    ],
    solutionUci: ["e6e8", "f5f8", "e8f8"],
    keyLine: "Check, block, capture — a mating pattern worth memorizing.",
    explanation: [
      "初手は 1. Qe8+! — クイーンのチェックです。キングは動けず、黒の応手は 1... Rf8 とルークで合駒するしかありません。",
      "ポイントは「チェック→合駒→取る」の流れです。合駒は時間を稼ぐ手ですが、その駒を取れる位置にいれば、チェックはそのまま詰みに変わります。",
      "そこへ 2. Qxf8# — クイーンがその合駒を取って詰み。この型は実戦でもよく現れる、覚えておきたい詰みのパターンです。",
    ],
  },
  {
    id: "2026-10-30-mate2-knight-guard",
    title: "第26問 — 2手で詰み",
    intro: "白の手番。黒のクイーンを取るチェックから、ナイトに守られたクイーンで詰ませよう。",
    source: "毎日のクイズ 2026-10-30 出題分（python-chess で検証済み）",
    theme: "ナイトに守られたクイーンの詰み",
    fen: "8/3Q4/k1qN4/8/3K4/8/8/8 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [
      "まずチェックから考えてみよう。黒のクイーンが取れる手はないかな？",
      "ナイトが b7 と b5、2つのマスを両方とも守っていることに注目しよう。",
      "初手は Qxc6+。クイーンで黒のクイーンを取るチェックだよ。",
    ],
    solutionUci: ["d7c6", "a6a7", "c6b7"],
    keyLine: "One knight can guard two mate squares at the same time.",
    explanation: [
      "初手は 1.Qxc6+。黒のクイーンを取りながらチェックをかける手で、これが唯一の詰ませ方です。",
      "ポイントはナイトです。d6のナイトが b7 と b5 の両方を守っているので、黒キングが上に逃げても下に逃げても、クイーンの詰みを守れます。",
      "代表線は 1...Ka7 2.Qb7#。もし 1...Ka5 と下に逃げても 2.Qb5# で、どちらの応手でも同じナイトに守られたクイーンの詰みになります。",
    ],
  },
  {
    id: "2026-11-02-mate2-rook-two-mates",
    title: "第27問 — 2手で詰み",
    intro: "白の手番。クイーンのチェックで黒キングを盤の端へ追い込む2手詰めです。キングの行き先によって、ルークの詰み方が変わります。",
    source: "毎週のクイズ 2026-11-02 出題分（python-chess で検証済み）",
    theme: "クイーンのチェックとルークの詰み分け",
    fen: "8/8/8/Q3pbK1/B7/4R3/8/1k6 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: ["まずクイーンでチェックして、黒キングの逃げ場を絞ろう。", "クイーンは a5 から b4 へ。キングの行き先によって、ルークの詰み方が変わります。", "初手は 1.Qb4+。Ka2・Ka1 なら Ra3#、Kc1 なら Re1# です。"],
    solutionUci: ["a5b4", "b1a2", "e3a3"],
    keyLine: "Drive the king with a queen check, then let the rook pick its mating square.",
    explanation: ["初手は 1.Qb4+。クイーンが b ファイルと対角線からチェックをかけ、黒キングの逃げ場は a2・c1・a1 の3つだけになります。", "キングが a2 または a1 に逃げたら 2.Ra3#。ルークはクイーンと a4 のビショップに守られ、キングの逃げ場をすべてふさぎます。", "キングが c1 に逃げた場合だけ詰み方が変わり、2.Re1# です。b4 のクイーンが e1 への対角線でルークを守ります。どの応手でも同じ初手から詰む、詰み分けがポイントの問題です。"]
  },
  {
    id: "2026-11-09-mate2-split-mates",
    title: "第28問 — 2手で詰み",
    intro: "白の手番。ルークのチェックで黒キングを左右に振り分けよう。キングの行き先によって、詰ませる駒が変わります。",
    source: "毎日のクイズ 2026-11-09 出題分（python-chess で検証済み）",
    theme: "ルークのチェックと詰み手の振り分け",
    fen: "B7/r7/4K3/8/8/1R6/1Q6/4k3 w - - 0 1",
    playerColor: "w",
    mateIn: 2,
    hints: [ "まずルークでチェックをかけよう。黒キングの逃げ道は左右の2つだけです。", "キングが右の f1 に逃げたらクイーン、左の d1 に逃げたらビショップが詰ませます。a8 のビショップがどちらの詰みも支えています。", "初手は Re3+。ルークを e3 に進めてチェックです。" ],
    solutionUci: ["b3e3", "e1f1", "b2g2"],
    keyLine: "The rook check splits the king: the queen mates on one side, the bishop on the other.",
    explanation: [ "初手は 1.Re3+。ルークを e3 に進めるチェックが、2手で詰ませられる唯一の初手です。黒キングの応手は Kf1 と Kd1 の2つだけで、どちらでも詰みますが、詰ませる駒が変わります。", "本線は 1...Kf1 に対して 2.Qg2#。クイーンが g2 に出て詰みです。クイーンは a8 のビショップに守られているのでキングに取れず、周りの逃げマスもルークとクイーンが押さえています。", "もう一方の応手 1...Kd1 に対しては 2.Bf3#。今度は a8 のビショップ自身が f3 に出て詰ませます。このビショップは e3 のルークに守られています。同じチェックから、キングの行き先で詰み手が分かれるのがポイントです。" ],
  },
  {
    id: "lichess-cjiep",
    title: "第29問 — 2手で詰み",
    intro: "白の手番。黒キングは8段目に閉じ込められています。クイーンを思い切って使う初手がカギです。",
    source: "Lichess パズル（PuzzleId: cjIeP、Rating 814、python-chess で検証済み）",
    theme: "クイーンの犠牲とバックランク",
    fen: "4rn1k/p5pp/1p1p4/4qQ2/3p4/2P4P/PP4PN/5R1K w - - 0 31",
    playerColor: "w",
    mateIn: 2,
    hints: ["黒キングの逃げ道はどこにもありません。8段目に注目。", "クイーンで黒のルークを引きつけると、守りが崩れます。", "初手は Qxf8+。ルークに取らせるのが狙いです。"],
    solutionUci: ["f5f8", "e8f8", "f1f8"],
    keyLine: "Sacrifice the queen to drag the rook away, then mate on the back rank.",
    explanation: ["初手 Qxf8+ はクイーンの犠牲。黒ルークに取ることを強制して、8段目の守りを崩します。", "黒の応手は Rxf8 のみ。ルークが f8 に引きずり出されることで、今度は白ルークの通り道が開きます。", "2.Rxf8# でバックランクメイト。黒キングは自分のポーンに囲まれて逃げ場がありません。"]
  },
  {
    id: "lichess-cjhmt",
    title: "第30問 — 2手で詰み",
    intro: "白の手番。クイーンとルークで黒キングの周りを取り囲んでいます。キングの近くまでクイーンを寄せる初手を探してください。",
    source: "Lichess パズル（PuzzleId: cjHmt、Rating 826、python-chess で検証済み）",
    theme: "クイーンの侵入",
    fen: "3r2k1/1R4p1/1p1q3p/4p2Q/1P2p3/2P4P/1P3PPK/r7 w - - 0 31",
    playerColor: "w",
    mateIn: 2,
    hints: ["クイーンがキングのそばに入り込むチェックがあります。", "g7 のポーンは、横のルークに支えられて詰みの的になります。", "初手は Qf7+。次に Qxg7# が待っています。"],
    solutionUci: ["h5f7", "g8h8", "f7g7"],
    keyLine: "Step the queen right up to the king — the rook guards the mating square.",
    explanation: ["初手 Qf7+ でクイーンが黒キングの鼻先まで侵入します。キングはクイーンを取ることができません。", "黒キングの応手は Kh8 と Kh7 の2通りだけですが、どちらでも結末は同じです。", "2.Qxg7#。g7 を取る詰み手は b7 のルークが横から支えているため、キングに取られません。"]
  },
  {
    id: "lichess-9knqa",
    title: "第31問 — 2手で詰み",
    intro: "白の手番。ルークとキングだけの終盤です。黒キングは盤の端に追い詰められています。",
    source: "Lichess パズル（PuzzleId: 9KnQa、Rating 871、python-chess で検証済み）",
    theme: "ルークエンディングの詰み（合駒を取る）",
    fen: "8/8/5Kpk/5p2/6r1/6R1/8/8 w - - 5 66",
    playerColor: "w",
    mateIn: 2,
    hints: ["チェックはキングのいるファイルから。端のキングに注目。", "黒ルークが合駒をしてきますが、その合駒自体が的になります。", "初手は Rh3+。合駒のルークをそのまま取ります。"],
    solutionUci: ["g3h3", "g4h4", "h3h4"],
    keyLine: "Check down the file — when the rook blocks, just take it.",
    explanation: ["初手 Rh3+ は h ファイルからのチェック。黒キングは h6 でポーンに囲まれ、逃げ道がありません。", "黒の唯一の応手は Rh4 の合駒。しかし合駒したルークは白ルークの目の前に立っただけです。", "2.Rxh4#。合駒を取って詰み。白キングが f6 から逃げ道を塞いでいることも効いています。"]
  },
  {
    id: "lichess-md8ge",
    title: "第32問 — 2手で詰み",
    intro: "白の手番。黒キングは h7 の隅にいます。クイーンとナイトとルークがキング側に集まっています。",
    source: "Lichess パズル（PuzzleId: Md8gE、Rating 877、python-chess で検証済み）",
    theme: "クイーンの詰み（隅への追い込み）",
    fen: "2r2q2/p3pNrk/1p4p1/6Qp/8/5R1P/PP4P1/7K w - - 3 37",
    playerColor: "w",
    mateIn: 2,
    hints: ["クイーンがキングの隣のマスに飛び込むチェックがあります。", "黒キングが逃げた先には、もう1つの詰みが待っています。", "初手は Qh6+。逃げたキングを Qh8# で仕留めます。"],
    solutionUci: ["g5h6", "h7g8", "h6h8"],
    keyLine: "Drive the king out of the corner, then mate on the square he left.",
    explanation: ["初手 Qh6+ でクイーンがキングの隣に飛び込みます。h6 はナイトが f7 から守っていて、キングは取れません。", "黒キングの応手は Kg8 のみ。隅から追い出されたキングは、空いた h8 が弱点になります。", "2.Qh8#。クイーンが隅のマスに入って詰み。f7 のナイトとルークが逃げ道を塞いでいます。"]
  },
  {
    id: "lichess-fkzal",
    title: "第33問 — 2手で詰み",
    intro: "白の手番。黒キングの前のポーンが1つだけ甘くなっています。そこを突く初手がカギです。",
    source: "Lichess パズル（PuzzleId: FKzAl、Rating 946、python-chess で検証済み）",
    theme: "ポーンの盾を崩す",
    fen: "r3r1k1/ppp2ppp/1nnb1q2/5N1Q/1P6/N2P3R/6K1/8 w - - 4 26",
    playerColor: "w",
    mateIn: 2,
    hints: ["黒キングの前の h7 ポーンは、後ろのルークに守られています。取ること自体はできます。", "キングが逃げたあと、クイーンが隅まで届きます。", "初手は Qxh7+。次に Qh8# です。"],
    solutionUci: ["h5h7", "g8f8", "h7h8"],
    keyLine: "Take the pawn in front of the king — the rook behind makes it safe.",
    explanation: ["初手 Qxh7+ はキングの盾のポーンを取るチェック。h7 は h3 のルークが後ろから守っているため、黒キングはクイーンを取れません。", "黒キングの応手は Kf8 のみ。中央寄りに逃げても、8段目の端が空いています。", "2.Qh8#。クイーンが隅に入って詰み。ナイト f5 が g7 の逃げ道を塞いでいます。"]
  },
  {
    id: "lichess-nes2s",
    title: "第34問 — 2手で詰み",
    intro: "白の手番。白クイーンの前に黒ビショップが立っています。思い切って取る手から始まります。",
    source: "Lichess パズル（PuzzleId: nES2s、Rating 952、python-chess で検証済み）",
    theme: "ビショップを取りながらの詰み",
    fen: "4k2r/2Qb1ppp/p3p1n1/8/2P5/qPb5/P4PPP/3R2K1 w k - 0 20",
    playerColor: "w",
    mateIn: 2,
    hints: ["クイーンの目の前のビショップは、取るための駒です。", "黒キングが逃げる先は1つだけ。その先に詰みが待っています。", "初手は Qxd7+。次に Qd8# です。"],
    solutionUci: ["c7d7", "e8f8", "d7d8"],
    keyLine: "Capture the bishop with check, then slide the queen home.",
    explanation: ["初手 Qxd7+ はビショップを取りながらのチェック。d7 は d1 のルークが後ろから支えています。", "黒キングの応手は Kf8 のみ。e ファイルも d ファイルも白に押さえられています。", "2.Qd8#。クイーンが8段目に滑り込んで詰み。ルークの支えが最後まで効いています。"]
  },
  {
    id: "lichess-byg4u",
    title: "第35問 — 2手で詰み",
    intro: "白の手番。黒キングと黒クイーンが8段目に並んでいます。ビショップの思い切った一手がカギです。",
    source: "Lichess パズル（PuzzleId: bYg4u、Rating 1106、python-chess で検証済み）",
    theme: "ビショップのチェック（そらし）",
    fen: "3Qqk2/1p3ppp/p1p5/6Bn/8/2P4P/P4PP1/6K1 w - - 2 21",
    playerColor: "w",
    mateIn: 2,
    hints: ["ビショップが黒クイーンの前に飛び込むチェックがあります。", "キングが逃げると、守りの要だったクイーンが取られます。", "初手は Be7+。次に Qxe8# です。"],
    solutionUci: ["g5e7", "f8g8", "d8e8"],
    keyLine: "The bishop check drives the king away — and the queen behind it is lost.",
    explanation: ["初手 Be7+ はビショップを黒クイーンの前に差し出すチェック。キングは取ることができず、逃げるしかありません。", "黒キングの応手は Kg8 のみ。キングがどいたことで、e8 のクイーンを守る壁が無くなります。", "2.Qxe8#。クイーンを取って詰み。ビショップが e7 から逃げ道を塞いでいます。"]
  },
  {
    id: "lichess-cjhos",
    title: "第36問 — 2手で詰み",
    intro: "白の手番。黒キングの前の h7 が狙い目です。ビショップを差し出す初手から、黒の応手で詰み手が変わります。",
    source: "Lichess パズル（PuzzleId: cjHoS、Rating 1125、python-chess で検証済み）",
    theme: "ビショップの犠牲（2通りの詰み分け）",
    fen: "r3rbk1/pb3pp1/1pqp1n2/2p2BN1/3P4/2P4P/PPQ2P1N/4RRK1 w - - 1 20",
    playerColor: "w",
    mateIn: 2,
    hints: ["h7 へのビショップの犠牲が初手です。キングは取ることができません。", "キングが逃げればナイト、ナイトが取ればクイーンが詰ませます。", "初手は Bh7+。応手ごとに仕留める駒が変わります。"],
    solutionUci: ["f5h7", "g8h8", "g5f7"],
    keyLine: "Sacrifice the bishop on h7 — knight or queen mates, depending on the reply.",
    explanation: ["初手 Bh7+ はビショップの犠牲。h7 はクイーンが c2 から守っていて、黒キングは取れません。", "黒の応手は2通り。Kh8 と逃げれば 2.Nxf7#、ナイトが取れば（Nxh7）2.Qxh7# と、どちらでも詰みます。", "詰み手が応手で変わる読み分けがポイント。犠牲の裏側まで読めていれば完璧です。"]
  },
  {
    id: "lichess-neuyh",
    title: "第37問 — 2手で詰み",
    intro: "白の手番。ルークが h ファイルを狙っています。黒クイーンの合駒を逆手に取る詰みです。",
    source: "Lichess パズル（PuzzleId: nEUYh、Rating 1186、python-chess で検証済み）",
    theme: "ルークのチェックと合駒取り",
    fen: "r1b2r1k/p7/2p1p1R1/1p2P3/8/4q3/PPP2P2/1K4R1 w - - 0 26",
    playerColor: "w",
    mateIn: 2,
    hints: ["もう1本のルークを h ファイルに呼び寄せるチェックがあります。", "黒はクイーンで合駒するしかありません。そのクイーンが的になります。", "初手は Rh1+。合駒のクイーンをルークで取ります。"],
    solutionUci: ["g1h1", "e3h6", "h1h6"],
    keyLine: "Double the rooks on the open file — the blocking queen gets captured with mate.",
    explanation: ["初手 Rh1+ で2本目のルークが h ファイルに加わり、チェック。黒キングは h8 に閉じ込められています。", "黒の応手はクイーンの合駒のみで、Qh6 と Qh3 の2通り。どちらでも合駒したクイーンが取られます。", "2.Rhxh6#（Qh3 の場合は Rxh3#）。h6 のルークはもう1本のルークに守られていて、キングは取れません。"]
  },
  {
    id: "lichess-cjg6t",
    title: "第38問 — 2手で詰み",
    intro: "白の手番。クイーンのチェックで黒キングを盤の中央へ引きずり出すと、意外な駒が詰ませます。",
    source: "Lichess パズル（PuzzleId: cjG6t、Rating 1283、python-chess で検証済み）",
    theme: "クイーンのチェックとナイトの詰み",
    fen: "r3q1k1/p3b1p1/1p1npnN1/2pp1p1Q/P4R2/1P1PP3/2P3PP/4R1K1 w - - 0 29",
    playerColor: "w",
    mateIn: 2,
    hints: ["クイーンが隅まで入るチェックがあります。キングは取ることができません。", "キングが前に出てきたところを、ナイトが仕留めます。", "初手は Qh8+。詰ませるのはナイトの Ne5# です。"],
    solutionUci: ["h5h8", "g8f7", "g6e5"],
    keyLine: "The queen check drags the king out — and the knight delivers mate.",
    explanation: ["初手 Qh8+ はクイーンが隅まで入るチェック。h8 は g6 のナイトが守っているため、黒キングは取れません。", "黒キングの応手は Kf7 のみ。キングが前に引きずり出され、味方の駒に囲まれた場所で止まります。", "2.Ne5#。ナイトが中央から詰ませます。キングの逃げ道はクイーンとルークと自軍の駒で全て塞がれています。"]
  },
  {
    id: "lichess-qwvzs",
    title: "第39問 — 2手で詰み",
    intro: "白の手番。2つのナイトが黒キングの近くで待機しています。取る手が同時に別の駒のラインを開きます。",
    source: "Lichess パズル（PuzzleId: QWVZs、Rating 1340、python-chess で検証済み）",
    theme: "ダブルチェックとナイトの詰み",
    fen: "rn1q1r2/pbp3pk/1p2pb1p/3pN3/3PN3/3B4/PPP2PPP/R3K2R w KQ - 0 13",
    playerColor: "w",
    mateIn: 2,
    hints: ["ナイトで取る手が、後ろのビショップのラインも開けるダブルチェックです。", "キングが隅に逃げたあと、もう1つのナイトが跳びます。", "初手は Nxf6+。詰ませるのは Ng6# です。"],
    solutionUci: ["e4f6", "h7h8", "e5g6"],
    keyLine: "A double check drives the king to the corner — the second knight mates.",
    explanation: ["初手 Nxf6+ はビショップを取りながらのダブルチェック。跳んだナイトと、後ろで開いたビショップのラインが同時にキングを狙います。", "ダブルチェックにはキングが動くしかありません。黒キングの応手は Kh8 のみで、隅に追い込まれます。", "2.Ng6#。もう1つのナイトが跳んで詰み。f6 のナイトが逃げ道の g8 を見張っています。"]
  },
  {
    id: "lichess-mdarn",
    title: "第40問 — 2手で詰み",
    intro: "白の手番。黒キングの前のポーンにルークを差し出す、大胆な犠牲から始まります。",
    source: "Lichess パズル（PuzzleId: MdARN、Rating 1478、python-chess で検証済み）",
    theme: "ルークの犠牲（アナスタシアメイト型）",
    fen: "4rr1k/bp1nNppp/p1p5/4P3/1PP5/P4KP1/1B4P1/R6R w - - 1 25",
    playerColor: "w",
    mateIn: 2,
    hints: ["ルークをキングの前のポーンにぶつける犠牲が初手です。", "キングが取ると、もう1本のルークの通り道が開きます。", "初手は Rxh7+。仕上げは Rh1# です。"],
    solutionUci: ["h1h7", "h8h7", "a1h1"],
    keyLine: "Sacrifice a rook to drag the king out — the other rook mates down the file.",
    explanation: ["初手 Rxh7+ はルークの犠牲。黒キングは取るしかなく、自分の陣地の外へ引きずり出されます。", "Kxh7 で h ファイルが開通。キングの周りは自軍の駒とポーンで塞がれています。", "2.Rh1#。残ったルークが開いたファイルを下りて詰み。ナイト e7 が逃げ道の g8 と g6 を塞ぐ、アナスタシアメイトの形です。"]
  },
];

/* ---------- localStorage helpers ---------- */
const LS_QUIZ = "chess-public-quiz-progress-v1";
const LS_VERSUS = "chess-public-versus-v1";
function loadJSON(key, fallback) {
  try {
    const raw = window.localStorage.getItem(key);
    if (!raw) return fallback;
    const parsed = JSON.parse(raw);
    return parsed == null ? fallback : parsed;
  } catch (e) { return fallback; }
}
function saveJSON(key, value) {
  try { window.localStorage.setItem(key, JSON.stringify(value)); } catch (e) {}
}

/* "1. Qb8+ Nxb8 2. Rd8#" style line, honouring the FEN's move number. */
function formatSans(sans, firstTurn, startNo) {
  const parts = [];
  sans.forEach((san, i) => {
    const isWhiteMove = (i % 2 === 0) === (firstTurn === "w");
    const moveNo = startNo + Math.floor((i + (firstTurn === "b" ? 1 : 0)) / 2);
    if (isWhiteMove) parts.push(moveNo + ". " + san);
    else if (i === 0) parts.push(moveNo + "... " + san);
    else parts.push(san);
  });
  return parts.join(" ");
}
function esc(s) {
  return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;");
}

/* ============================================================
   English gloss + live commentary. Difficult chess/English
   words get one sparse Japanese gloss in parentheses — basic
   words never do. The commentary is one short English sentence
   per move in versus mode, so chess English is learned in
   context while playing.
   ============================================================ */
const GLOSSES = [
  ["sacrifices", "犠牲"], ["sacrifice", "犠牲"], ["deflection", "そらし"],
  ["undefended", "守られていない"], ["stalemate", "手詰まり"], ["hanging", "守られていない"],
  ["pinned", "釘付けにされた"], ["forks", "両取り"], ["fork", "両取り"],
  ["decoy", "おとり"], ["pin", "釘付け"],
];
function glossify(text) {
  let out = String(text);
  for (const pair of GLOSSES) {
    const re = new RegExp("\\b(" + pair[0] + ")\\b(?!\\s*\\()", "i");
    out = out.replace(re, "$1 (" + pair[1] + ")");
  }
  return out;
}
/* The one memorable English key sentence for a solved puzzle:
   the puzzle's own keyLine, else the explanation's first
   sentence when it is short enough to be memorable. */
function keyLineFor(puzzle) {
  if (puzzle.keyLine) return glossify(puzzle.keyLine);
  const first = (puzzle.explanation[0] || "").trim();
  const m = first.match(/^[^.!?]+[.!?]/);
  if (!m) return null;
  const sentence = m[0].trim();
  if (sentence.length > 140 || sentence.split(/\s+/).length > 22) return null;
  if (sentence.length < 12) return null;
  return glossify(sentence);
}

const KIND_NAMES_EN = { k: "king", q: "queen", r: "rook", b: "bishop", n: "knight", p: "pawn" };
const CVAL = { k: 10000, q: 900, r: 500, b: 330, n: 320, p: 100 };
function pieceAttacksSquare(state, from, to) {
  const piece = state.board[from];
  if (!piece || from === to) return false;
  const kind = kindOf(piece);
  const df = fileOf(to) - fileOf(from), dr = rankOf(to) - rankOf(from);
  const adf = Math.abs(df), adr = Math.abs(dr);
  if (kind === "p") {
    const dir = colorOf(piece) === "w" ? 1 : -1;
    return dr === dir && adf === 1;
  }
  if (kind === "n") return (adf === 1 && adr === 2) || (adf === 2 && adr === 1);
  if (kind === "k") return Math.max(adf, adr) === 1;
  const straight = df === 0 || dr === 0;
  const diagonal = adf === adr && adf > 0;
  if (kind === "b" && !diagonal) return false;
  if (kind === "r" && !straight) return false;
  if (kind === "q" && !straight && !diagonal) return false;
  const stepF = Math.sign(df), stepR = Math.sign(dr);
  let f = fileOf(from) + stepF, r = rankOf(from) + stepR;
  while (f !== fileOf(to) || r !== rankOf(to)) {
    if (state.board[makeSq(f, r)] != null) return false;
    f += stepF; r += stepR;
  }
  return true;
}
function attackersOf(state, sq, byColor) {
  const out = [];
  for (let s = 0; s < 64; s++) {
    if (s === sq) continue;
    const p = state.board[s];
    if (p != null && colorOf(p) === byColor && pieceAttacksSquare(state, s, sq)) out.push(s);
  }
  return out;
}
function isHanging(state, sq) {
  const piece = state.board[sq];
  if (!piece) return false;
  const owner = colorOf(piece);
  if (kindOf(piece) === "k") return false;
  const attacked = attackersOf(state, sq, opponent(owner)).length > 0;
  const defended = attackersOf(state, sq, owner).length > 0;
  return attacked && !defended;
}
function attackedEnemies(state, move, mover) {
  const out = [];
  for (let s = 0; s < 64; s++) {
    const p = state.board[s];
    if (p == null || colorOf(p) === mover) continue;
    if (pieceAttacksSquare(state, move.to, s)) out.push({ sq: s, kind: kindOf(p) });
  }
  return out.sort((a, b) => CVAL[b.kind] - CVAL[a.kind]);
}
function pinnedVictim(state, move, mover) {
  const piece = state.board[move.to];
  if (!piece) return null;
  const kind = kindOf(piece);
  if (kind !== "b" && kind !== "r" && kind !== "q") return null;
  const defender = opponent(mover);
  const kingSq = findKing(state.board, defender);
  if (kingSq < 0) return null;
  for (let s = 0; s < 64; s++) {
    const p = state.board[s];
    if (p == null || colorOf(p) !== defender || kindOf(p) === "k") continue;
    const line = [move.to, s, kingSq];
    const files = line.map(fileOf), ranks = line.map(rankOf);
    const sameFile = files[0] === files[1] && files[1] === files[2];
    const sameRank = ranks[0] === ranks[1] && ranks[1] === ranks[2];
    const sameDiag =
      Math.abs(files[0] - files[1]) === Math.abs(ranks[0] - ranks[1]) &&
      Math.abs(files[1] - files[2]) === Math.abs(ranks[1] - ranks[2]) &&
      Math.sign(files[1] - files[0]) === Math.sign(files[2] - files[1]) &&
      Math.sign(ranks[1] - ranks[0]) === Math.sign(ranks[2] - ranks[1]);
    if (!sameFile && !sameRank && !sameDiag) continue;
    if (sameDiag && kind === "r") continue;
    if ((sameFile || sameRank) && kind === "b") continue;
    const between = (a, b, c) => (a < b && b < c) || (a > b && b > c);
    const onSegment = sameFile ? between(ranks[0], ranks[1], ranks[2]) : between(files[0], files[1], files[2]);
    if (!onSegment) continue;
    let clear = true;
    for (const pair of [[move.to, s], [s, kingSq]]) {
      const sf = Math.sign(fileOf(pair[1]) - fileOf(pair[0]));
      const sr = Math.sign(rankOf(pair[1]) - rankOf(pair[0]));
      let f = fileOf(pair[0]) + sf, r = rankOf(pair[0]) + sr;
      while (f !== fileOf(pair[1]) || r !== rankOf(pair[1])) {
        if (state.board[makeSq(f, r)] != null) clear = false;
        f += sf; r += sr;
      }
    }
    if (clear) return { kind: kindOf(p) };
  }
  return null;
}
function commentaryForMove(prev, move, next, player) {
  const mover = prev.turn;
  const isPlayer = mover === player;
  const moverName = mover === "w" ? "White" : "Black";
  const enemyName = mover === "w" ? "Black" : "White";
  const movedPiece = prev.board[move.from];
  const movedKind = movedPiece ? kindOf(movedPiece) : "p";
  const movedName = KIND_NAMES_EN[movedKind];
  const say = (line) => glossify(line);
  if (isCheckmate(next)) {
    return say(isPlayer ? "Checkmate — that move ends the game, and you win." : "Checkmate — that move ends the game.");
  }
  if (isStalemate(next)) return say("That move makes a stalemate — the game is a draw.");
  if (move.promotion) {
    const newName = KIND_NAMES_EN[move.promotion];
    return say(isPlayer ? "You promoted your pawn to a " + newName + "." : moverName + " promoted a pawn to a " + newName + ".");
  }
  if (move.castle) {
    return say(isPlayer ? "You castled — your king is safer now." : moverName + " castled — the king is safer now.");
  }
  const givesCheck = isInCheck(next, next.turn);
  if (move.capture) {
    const captured = move.enPassant ? "p" : (prev.board[move.to] ? kindOf(prev.board[move.to]) : "p");
    const capturedName = KIND_NAMES_EN[captured];
    if (givesCheck) {
      return say(isPlayer
        ? "You took " + enemyName + "'s " + capturedName + " and give check."
        : moverName + " took your " + capturedName + " and gives check — be careful.");
    }
    return say(isPlayer
      ? "You took " + enemyName + "'s " + capturedName + "."
      : moverName + " took your " + capturedName + ".");
  }
  if (givesCheck) {
    return say(isPlayer
      ? "You give check — the enemy king must move."
      : moverName + " gives check — your king must move or block.");
  }
  const targets = attackedEnemies(next, move, mover).filter((t) => t.kind !== "k");
  if (targets.length >= 2) {
    return say(isPlayer
      ? "Your " + movedName + " forks two pieces at the same time."
      : moverName + "'s " + movedName + " forks two of your pieces — be careful.");
  }
  const pinned = pinnedVictim(next, move, mover);
  if (pinned) {
    const pinnedName = KIND_NAMES_EN[pinned.kind];
    return say(isPlayer
      ? "Your " + movedName + " pins " + enemyName + "'s " + pinnedName + " to the king."
      : moverName + "'s " + movedName + " pins your " + pinnedName + " to your king.");
  }
  if (isHanging(next, move.to)) {
    return say(isPlayer
      ? "Your " + movedName + " is hanging — it can be taken for free."
      : moverName + "'s " + movedName + " is hanging — you can take it for free.");
  }
  if (targets.length === 1) {
    const victimName = KIND_NAMES_EN[targets[0].kind];
    return say(isPlayer
      ? "You attack " + enemyName + "'s " + victimName + "."
      : moverName + " attacks your " + victimName + " — be careful.");
  }
  if (!isPlayer) {
    for (let s = 0; s < 64; s++) {
      const p = next.board[s];
      if (p == null || colorOf(p) !== player || kindOf(p) === "k") continue;
      if (isHanging(next, s) && CVAL[kindOf(p)] >= CVAL.n) {
        return say("Your " + KIND_NAMES_EN[kindOf(p)] + " is undefended — it can be taken for free.");
      }
    }
  }
  if (isPlayer) {
    for (let s = 0; s < 64; s++) {
      const p = next.board[s];
      if (p == null || colorOf(p) === player || kindOf(p) === "k") continue;
      if (isHanging(next, s) && CVAL[kindOf(p)] >= CVAL.n && attackersOf(next, s, player).length > 0) {
        return say(enemyName + "'s " + KIND_NAMES_EN[kindOf(p)] + " is undefended — you can take it.");
      }
    }
  }
  if (movedKind === "p") {
    const f = fileOf(move.to), r = rankOf(move.to);
    if ((f === 3 || f === 4) && (r === 3 || r === 4)) {
      return say(isPlayer ? "You take the center with your pawn." : moverName + " takes the center with a pawn.");
    }
  }
  if ((movedKind === "n" || movedKind === "b") && prev.fullmove <= 10) {
    return say(isPlayer ? "You bring your " + movedName + " out." : moverName + " brings a " + movedName + " out.");
  }
  return say(isPlayer
    ? "You move your " + movedName + " to " + squareName(move.to) + "."
    : moverName + " moves the " + movedName + " to " + squareName(move.to) + ".");
}
const START_COMMENTARY = "The game is ready — White moves first.";

/* ============================================================
   QUIZ mode
   ============================================================ */
const quizRoot = document.getElementById("quizView");
let quizProgress = loadJSON(LS_QUIZ, {});
let currentPuzzleId = PUZZLES[PUZZLES.length - 1].id;
let solver = null; // active PuzzleSolver state

function getProgress(id) {
  return quizProgress[id] || { attempts: 0, hintsUsed: 0, solved: false };
}
function setProgress(id, patch) {
  quizProgress[id] = Object.assign(getProgress(id), patch);
  saveJSON(LS_QUIZ, quizProgress);
}

function startMessage(puzzle) {
  const side = puzzle.playerColor === "w" ? "白" : "黒";
  return side + "の手番です。自分の駒をタップすると、動けるマスが光ります。" + puzzle.mateIn + "手で詰ませてみましょう。";
}

function renderPuzzleChips() {
  const row = document.getElementById("puzzleChipRow");
  if (!row) return;
  const chips = PUZZLES.map((p, i) => {
    const active = p.id === currentPuzzleId;
    const isLatest = i === PUZZLES.length - 1;
    const solvedMark = getProgress(p.id).solved ? " ✓" : "";
    return '<button type="button" class="puzzle-chip' + (active ? " active" : "") + '" data-puzzle="' + p.id + '" aria-pressed="' + active + '">第' + (i + 1) + "問" + (isLatest && PUZZLES.length > 1 ? "・最新" : "") + solvedMark + "</button>";
  }).join("");
  row.innerHTML = '<span style="font-size:12px;font-weight:700;color:var(--dim)">問題：</span>' + chips;
  row.querySelectorAll("[data-puzzle]").forEach((b) => {
    b.addEventListener("click", () => {
      if (b.getAttribute("data-puzzle") === currentPuzzleId) return;
      currentPuzzleId = b.getAttribute("data-puzzle");
      renderPuzzleChips();
      buildSolver(document.getElementById("solverRoot"), PUZZLES.find((p) => p.id === currentPuzzleId));
    });
  });
}
function buildQuiz() {
  quizRoot.innerHTML =
    '<div class="chip-row" style="margin-bottom:16px" role="group" aria-label="問題の選択" id="puzzleChipRow"></div>'
    + '<div id="solverRoot"></div>';
  renderPuzzleChips();
  buildSolver(document.getElementById("solverRoot"), PUZZLES.find((p) => p.id === currentPuzzleId));
}

function buildSolver(root, puzzle) {
  const initial = parseFEN(puzzle.fen);
  const opponentName = puzzle.playerColor === "w" ? "黒" : "白";
  const totalPlies = puzzle.mateIn * 2 - 1;
  const st = {
    phase: "play", // play | wrong | solved
    message: startMessage(puzzle),
    undoToPly: 0,
    shakeKey: 0,
    hintsShown: getProgress(puzzle.id).hintsUsed || 0,
    answerShown: false,
    blackThinking: false,
  };
  root.innerHTML =
    '<div class="chip-row">'
    + '<span class="chip accent">' + esc(puzzle.title) + "</span>"
    + (puzzle.theme ? '<span class="chip dim">テーマ：' + esc(puzzle.theme) + "</span>" : "")
    + '<span class="chip solved" id="solvedChip" hidden>解けました</span>'
    + '<span style="font-size:12px;color:var(--dim)" id="statLine"></span>'
    + "</div>"
    + '<p style="margin-top:12px;font-size:15px;line-height:1.7">' + esc(puzzle.intro) + "</p>"
    + '<div class="board-tools"><span class="board-tools-label">盤面表示</span><div class="seg-group view-seg" role="group" aria-label="盤面表示切替"><button type="button" class="seg-btn small" data-view="2d" aria-pressed="true">2D</button><button type="button" class="seg-btn small" data-view="3d" aria-pressed="false">3D</button></div><span style="font-size:11px;color:var(--dim)">3Dはドラッグで回転・ピンチで拡大</span></div>'
    + '<div id="qBoardOuter" style="position:relative;margin-top:16px"><div class="board-wrap" id="qBoard"></div></div>'
    + '<div class="msg" id="qMsg" aria-live="polite"></div>'
    + '<p id="qSans" style="margin-top:12px;font-size:14px;color:var(--dim)" aria-label="指し手"></p>'
    + '<div class="btn-grid">'
    + '<button type="button" class="btn" id="qTakeback">一手戻す</button>'
    + '<button type="button" class="btn" id="qReset">リセット</button>'
    + '<button type="button" class="btn" id="qHint">ヒント</button>'
    + '<button type="button" class="btn" id="qAnswer">答えを見る</button>'
    + "</div>"
    + '<ul id="qHints" style="list-style:none;margin:16px 0 0;padding:0;display:grid;gap:8px"></ul>'
    + '<p style="margin-top:20px;font-size:13px;line-height:1.7;color:var(--dim)">指す前の3点チェック：① 相手の狙いは何か　② ぶら下がっている駒（タダで取られる駒）はないか　③ その手で何を失うか</p>'
    + '<div id="qExplain"></div>';

  const wrapEl = root.querySelector("#qBoard");
  const outerEl = root.querySelector("#qBoardOuter");
  const msgEl = root.querySelector("#qMsg");
  const sansEl = root.querySelector("#qSans");
  const statEl = root.querySelector("#statLine");
  const solvedChip = root.querySelector("#solvedChip");
  const hintsEl = root.querySelector("#qHints");
  const explainEl = root.querySelector("#qExplain");
  const takebackBtn = root.querySelector("#qTakeback");
  const hintBtn = root.querySelector("#qHint");
  const answerBtn = root.querySelector("#qAnswer");

  let tap, game;
  function render() {
    const prog = getProgress(puzzle.id);
    const solvedNow = st.phase === "solved" || prog.solved;
    solvedChip.hidden = !solvedNow;
    statEl.textContent = "挑戦回数 " + prog.attempts + " 回 ・ ヒント " + st.hintsShown + "/" + puzzle.hints.length;
    const checkSquare = isInCheck(game.state, game.state.turn) ? findKing(game.state.board, game.state.turn) : -1;
    boardView.render({
      state: game.state,
      orientation: puzzle.playerColor,
      selected: tap.selected,
      targets: tap.targets,
      lastMove: game.lastMove,
      checkSquare: checkSquare >= 0 ? checkSquare : null,
      starSquare: st.phase === "solved" && game.lastMove ? game.lastMove.to : null,
      disabled: st.phase !== "play" || st.blackThinking,
    });
    if (st.shakeKey > 0) {
      wrapEl.classList.remove("board-shake");
      void wrapEl.offsetWidth;
      wrapEl.classList.add("board-shake");
    }
    msgEl.className = "msg" + (st.phase === "solved" ? " solved" : st.phase === "wrong" ? " wrong" : "");
    msgEl.innerHTML = st.phase === "solved" ? '<span class="pop-in" style="font-weight:700">' + esc(st.message) + "</span>" : esc(st.message);
    sansEl.textContent = game.sans.length > 0 ? formatSans(game.sans, initial.turn, initial.fullmove) : "";
    takebackBtn.disabled = st.phase !== "wrong";
    takebackBtn.classList.toggle("primary", st.phase === "wrong");
    hintBtn.disabled = st.hintsShown >= puzzle.hints.length;
    hintBtn.textContent = "ヒント" + (st.hintsShown > 0 ? "（" + st.hintsShown + "/" + puzzle.hints.length + "）" : "");
    answerBtn.disabled = st.answerShown;
    hintsEl.innerHTML = puzzle.hints.slice(0, st.hintsShown).map((h, i) =>
      '<li class="hint-item panel-in"><b>ヒント' + (i + 1) + "：</b>" + esc(h) + "</li>").join("");
    if (tap.promo) {
      const movingPiece = game.state.board[(tap.promo.moves[0] || {}).from];
      if (movingPiece) {
        showPromotionPicker(outerEl, game.state.turn, (k) => tap.choosePromo(k), () => tap.cancelPromo());
      }
    } else {
      hidePromotionPicker(outerEl);
    }
    if (st.phase === "solved" || st.answerShown) {
      let state = initial;
      const sans = [];
      for (const uci of puzzle.solutionUci) {
        const mv = matchUci(state, uci);
        if (!mv) break;
        sans.push(toSAN(state, mv));
        state = applyMove(state, mv);
      }
      const line = formatSans(sans, initial.turn, initial.fullmove);
      explainEl.innerHTML =
        '<section class="panel panel-in" style="margin-top:20px">'
        + '<h2 class="font-display" style="font-size:18px;font-weight:700;margin:0">' + (st.phase === "solved" ? "解説 — なぜ詰むのか" : "答えと解説") + "</h2>"
        + (solvedNow && keyLineFor(puzzle) ? '<div class="keyline"><p class="keyline-label">KEY SENTENCE</p><p class="keyline-text">' + esc(keyLineFor(puzzle)) + "</p></div>" : "")
        + '<p style="margin-top:12px;font-size:16px;font-weight:700;letter-spacing:0.02em;color:var(--accent)">' + esc(line) + "</p>"
        + puzzle.explanation.map((para) => '<p style="margin-top:12px;font-size:15px;line-height:1.75">' + esc(para) + "</p>").join("")
        + (puzzle.source ? '<p style="margin-top:16px;font-size:12px;line-height:1.7;color:var(--dim)">出典：' + esc(puzzle.source) + "</p>" : "")
        + (st.phase === "solved" ? '<button type="button" class="btn primary" id="qAgain" style="margin-top:16px">もう一度解く</button>' : "")
        + "</section>";
      const again = explainEl.querySelector("#qAgain");
      if (again) again.addEventListener("click", reset);
    } else {
      explainEl.innerHTML = "";
    }
  }

  const boardView = createBoardView(wrapEl, (sq) => { tap.handleTap(sq); });
  initViewToggle(root, boardView);
  game = createGame([initial], [], [], boardView, render);
  function handleMove(move) {
    const cur = game.state;
    const plyBefore = game.moves.length;
    if (plyBefore === 0) setProgress(puzzle.id, { attempts: getProgress(puzzle.id).attempts + 1 });
    const next = applyMove(cur, move);
    if (isCheckmate(next)) {
      game.applyAnimated(move, { silent: true, onLanded: () => { sfx.win(); fireConfetti(); } });
      sfx.check();
      st.phase = "solved";
      st.message = "詰みです！ お見事、正解です。下に解説が出ています。";
      setProgress(puzzle.id, { solved: true });
      render();
      refreshQuizChips();
      return;
    }
    const remaining = totalPlies - (plyBefore + 1);
    const stillForcesMate = remaining > 0 && mateDistance(next, puzzle.playerColor, remaining) !== null;
    if (stillForcesMate) {
      game.applyAnimated(move);
      st.blackThinking = true;
      st.message = "いい手です！ " + opponentName + "の応手は…";
      render();
      game.later(() => {
        const reply = chooseDefenderReply(next, puzzle.playerColor, remaining);
        st.blackThinking = false;
        if (reply) {
          game.applyAnimated(reply);
          const movesLeft = remaining / 2;
          st.message = movesLeft <= 1
            ? opponentName + "はその手で受けるしかありませんでした。あと1手 — どこに置くと詰みになりますか？"
            : opponentName + "は受けてきました。あと" + movesLeft + "手で詰みです — 次の一手を考えてみましょう。";
        }
        render();
      }, 560);
      return;
    }
    game.applyAnimated(move, { silent: true });
    sfx.wrong();
    st.undoToPly = plyBefore;
    st.shakeKey += 1;
    st.phase = "wrong";
    // A wrong move that still gives check *looks* like mate on the
    // board: the defender's king sits highlighted in check and most
    // of its flight squares are covered, so the one open escape is
    // easy to miss (第11問: 1.Qe1+ looks like mate in 1, but the king
    // still has Kh2 — the h2 square is uncovered). Leaving the king
    // frozen in check teaches nothing, so name the escaping reply
    // and play it on the board — the same way a correct move plays
    // the defender's reply — before asking for a takeback. The
    // timer re-checks the position, so a takeback or reset pressed
    // while it is pending simply cancels the replay.
    const escape = isInCheck(next, next.turn) ? findEscapeReply(next, puzzle.playerColor, remaining) : null;
    if (escape) {
      const escapeSan = toSAN(next, escape);
      const escapeSq = squareName(escape.to);
      st.message = "チェックですが、詰みではありません。" + opponentName + "には " + escapeSan + " という逃げ手が残っています（行き先は " + escapeSq + "）。その手を盤面で再生します。";
      render();
      game.later(() => {
        if (st.phase !== "wrong" || game.moves.length !== plyBefore + 1 || !wrapEl.isConnected) return;
        game.applyAnimated(escape);
        st.message = opponentName + "は " + escapeSan + " と " + escapeSq + " へ逃げました。チェックが外れたので、"
          + (plyBefore === 0 ? "これも1手詰みではありません。" : "これでは詰みになりません。")
          + "一手戻して、まず " + escapeSq + " への逃げ道をふさぐ手がないか考えてみましょう。";
        render();
      }, 950);
      return;
    }
    st.message = plyBefore === 0
      ? "その手は合法ですが、" + puzzle.mateIn + "手で詰む手順にはなっていません。一手戻して、もう一度考えてみましょう。"
      : "惜しい！ その手では詰みになりません。一手戻してもう一度どうぞ。";
    render();
  }
  tap = createTapMove(
    () => game.state,
    () => st.phase === "play" && !st.blackThinking,
    handleMove,
    () => { st.shakeKey += 1; sfx.wrong(); render(); },
    render
  );
  function reset() {
    game.resetAll(initial);
    st.phase = "play";
    st.blackThinking = false;
    st.message = startMessage(puzzle);
    tap.clearSelection();
    render();
  }
  takebackBtn.addEventListener("click", () => {
    if (st.phase !== "wrong") return;
    game.truncate(st.undoToPly);
    st.phase = "play";
    st.message = st.undoToPly === 0 ? startMessage(puzzle) : "一手戻しました。落ち着いて、詰み筋をもう一度考えてみましょう。";
    tap.clearSelection();
    render();
  });
  root.querySelector("#qReset").addEventListener("click", reset);
  hintBtn.addEventListener("click", () => {
    const level = Math.min(puzzle.hints.length, st.hintsShown + 1);
    if (level === st.hintsShown) return;
    st.hintsShown = level;
    setProgress(puzzle.id, { hintsUsed: Math.max(getProgress(puzzle.id).hintsUsed, level) });
    sfx.select();
    render();
  });
  answerBtn.addEventListener("click", () => { st.answerShown = true; render(); });
  solver = { render };
  render();
}
function refreshQuizChips() { renderPuzzleChips(); }

/* ============================================================
   VERSUS mode — full game vs the built-in engine, saved in
   localStorage so a visitor can resume.
   ============================================================ */
const versusRoot = document.getElementById("versusView");
const START_FEN = "rnbqkbnr/pppppppp/8/8/8/8/PPPPPPPP/RNBQKBNR w KQkq - 0 1";
let versus = null;

function evaluateEnd(history, player) {
  const state = history[history.length - 1];
  if (isCheckmate(state)) {
    const winner = state.turn === "w" ? "b" : "w";
    return winner === player
      ? { over: true, text: "チェックメイト！ あなたの勝ちです。", playerWon: true }
      : { over: true, text: "チェックメイト。コンピュータの勝ちです。", playerWon: false };
  }
  if (isStalemate(state)) return { over: true, text: "ステイルメイト（行き詰まり）で引き分けです。", playerWon: false };
  if (insufficientMaterial(state)) return { over: true, text: "詰ませられる駒が足りず、引き分けです。", playerWon: false };
  if (state.halfmove >= 100) return { over: true, text: "50手ルールで引き分けです。", playerWon: false };
  const key = positionKey(state);
  const repeats = history.filter((s) => positionKey(s) === key).length;
  if (repeats >= 3) return { over: true, text: "同じ局面が3回現れたため、引き分けです。", playerWon: false };
  return { over: false, text: "", playerWon: false };
}

function buildVersus() {
  const savedGame = loadJSON(LS_VERSUS, null);
  let restored = null;
  if (savedGame && savedGame.v === 1 && Array.isArray(savedGame.fens) && savedGame.fens.length > 0) restored = savedGame;
  const startState = parseFEN(START_FEN);
  let states = [startState], moves = [], sans = [];
  let player = "w", difficulty = "medium";
  if (restored) {
    player = restored.player === "b" ? "b" : "w";
    difficulty = ["easy", "medium", "hard"].includes(restored.difficulty) ? restored.difficulty : "medium";
    try {
      states = restored.fens.map((fen) => parseFEN(fen));
      sans = Array.isArray(restored.sans) ? restored.sans : [];
      moves = [];
      for (let i = 0; i < (restored.ucis || []).length; i++) {
        const prev = states[i], uci = restored.ucis[i];
        if (!prev || !uci) break;
        const mv = matchUci(prev, uci);
        if (!mv) break;
        moves.push(mv);
      }
    } catch (e) { states = [startState]; moves = []; sans = []; }
  }
  versus = { player, difficulty, thinking: false, shakeKey: 0, aiTimer: null };

  versusRoot.innerHTML =
    '<div style="display:grid;grid-template-columns:1fr 1fr;gap:8px">'
    + '<div class="seg-group" role="group" aria-label="手番の選択">'
    + '<button type="button" class="seg-btn small" id="vWhite">白で対戦</button>'
    + '<button type="button" class="seg-btn small" id="vBlack">黒で対戦</button>'
    + "</div>"
    + '<div class="seg-group" role="group" aria-label="強さの選択">'
    + '<button type="button" class="seg-btn small" data-diff="easy">かんたん</button>'
    + '<button type="button" class="seg-btn small" data-diff="medium">ふつう</button>'
    + '<button type="button" class="seg-btn small" data-diff="hard">つよい</button>'
    + "</div></div>"
    + '<p style="margin-top:8px;font-size:12px;color:var(--dim)">手番や強さを変えると、対局は最初からになります。</p>'
    + '<div class="board-tools"><span class="board-tools-label">盤面表示</span><div class="seg-group view-seg" role="group" aria-label="盤面表示切替"><button type="button" class="seg-btn small" data-view="2d" aria-pressed="true">2D</button><button type="button" class="seg-btn small" data-view="3d" aria-pressed="false">3D</button></div><span style="font-size:11px;color:var(--dim)">3Dはドラッグで回転・ピンチで拡大</span></div>'
    + '<div id="vBoardOuter" style="position:relative;margin-top:12px"><div class="board-wrap" id="vBoard"></div></div>'
    + '<div class="msg bold" id="vStatus" aria-live="polite" style="min-height:0"></div>'
    + '<div class="commentary" aria-label="実況コメント"><p class="commentary-label">COMMENTARY</p><p class="commentary-text" id="vCommentary" aria-live="polite"></p></div>'
    + '<div class="btn-grid">'
    + '<button type="button" class="btn" id="vNew">最初から（新規対局）</button>'
    + '<button type="button" class="btn" id="vUndo">待った（1手分戻す）</button>'
    + "</div>"
    + '<div class="movelist" id="vMoves" aria-label="棋譜" hidden><div class="movelist-grid" id="vMovesGrid"></div></div>';

  const wrapEl = versusRoot.querySelector("#vBoard");
  const outerEl = versusRoot.querySelector("#vBoardOuter");
  const statusEl = versusRoot.querySelector("#vStatus");
  const commentaryEl = versusRoot.querySelector("#vCommentary");
  const movesBox = versusRoot.querySelector("#vMoves");
  const movesGrid = versusRoot.querySelector("#vMovesGrid");
  const undoBtn = versusRoot.querySelector("#vUndo");

  let tap, game;
  function persist() {
    saveJSON(LS_VERSUS, {
      v: 1,
      player: versus.player,
      difficulty: versus.difficulty,
      fens: game.history.map((s) => toFEN(s)),
      sans: game.sans,
      ucis: game.moves.map((m) => moveToUci(m)),
    });
  }
  let persistTimer = null;
  function schedulePersist() {
    if (persistTimer) window.clearTimeout(persistTimer);
    persistTimer = window.setTimeout(persist, 450);
  }
  function render() {
    versusRoot.querySelector("#vWhite").classList.toggle("active", versus.player === "w");
    versusRoot.querySelector("#vBlack").classList.toggle("active", versus.player === "b");
    versusRoot.querySelectorAll("[data-diff]").forEach((b) =>
      b.classList.toggle("active", b.getAttribute("data-diff") === versus.difficulty));
    const end = evaluateEnd(game.history, versus.player);
    const checkSquare = isInCheck(game.state, game.state.turn) ? findKing(game.state.board, game.state.turn) : -1;
    boardView.render({
      state: game.state,
      orientation: versus.player,
      selected: tap.selected,
      targets: tap.targets,
      lastMove: game.lastMove,
      checkSquare: checkSquare >= 0 ? checkSquare : null,
      starSquare: end.over && game.lastMove ? game.lastMove.to : null,
      disabled: end.over || game.state.turn !== versus.player || versus.thinking,
    });
    if (versus.shakeKey > 0) {
      wrapEl.classList.remove("board-shake");
      void wrapEl.offsetWidth;
      wrapEl.classList.add("board-shake");
    }
    const statusText = end.over ? end.text
      : versus.thinking ? "コンピュータが考え中…"
      : game.state.turn === versus.player
        ? (isInCheck(game.state, versus.player) ? "チェックされています！ あなたの手番です。" : "あなたの手番です。")
        : "コンピュータの手番です。";
    statusEl.className = "msg bold" + (end.over && end.playerWon ? " solved" : "");
    statusEl.style.minHeight = "0";
    statusEl.innerHTML = end.over ? '<span class="pop-in">' + esc(statusText) + "</span>" : esc(statusText);
    if (commentaryEl) {
      let commentaryText = START_COMMENTARY;
      if (game.moves.length > 0) {
        const li = game.moves.length - 1;
        const prevS = game.history[li], lastMv = game.moves[li], nextS = game.history[li + 1];
        if (prevS && lastMv && nextS) commentaryText = commentaryForMove(prevS, lastMv, nextS, versus.player);
      }
      if (commentaryEl.textContent !== commentaryText) {
        commentaryEl.textContent = commentaryText;
        commentaryEl.classList.remove("panel-in");
        void commentaryEl.offsetWidth;
        commentaryEl.classList.add("panel-in");
      }
    }
    undoBtn.disabled = versus.thinking || game.moves.length === 0;
    if (game.sans.length > 0) {
      movesBox.hidden = false;
      let rows = "";
      for (let i = 0; i < Math.ceil(game.sans.length / 2); i++) {
        rows += '<span style="color:var(--dim)">' + (i + 1) + '.</span><span style="font-weight:600">' + esc(game.sans[i * 2] || "") + '</span><span style="font-weight:600">' + esc(game.sans[i * 2 + 1] || "") + "</span>";
      }
      movesGrid.innerHTML = rows;
      movesBox.scrollTop = movesBox.scrollHeight;
    } else {
      movesBox.hidden = true;
      movesGrid.innerHTML = "";
    }
    if (tap.promo) {
      const movingPiece = game.state.board[(tap.promo.moves[0] || {}).from];
      if (movingPiece) showPromotionPicker(outerEl, game.state.turn, (k) => tap.choosePromo(k), () => tap.cancelPromo());
    } else {
      hidePromotionPicker(outerEl);
    }
  }
  function maybeAiMove() {
    const end = evaluateEnd(game.history, versus.player);
    if (end.over || game.state.turn === versus.player) return;
    versus.thinking = true;
    render();
    versus.aiTimer = window.setTimeout(() => {
      const mv = chooseAiMove(game.state, versus.difficulty);
      versus.thinking = false;
      if (!mv) { render(); return; }
      const next = applyMove(game.state, mv);
      const nextEnd = evaluateEnd(game.history.concat([next]), versus.player);
      game.applyAnimated(mv, {
        onLanded: () => { if (nextEnd.over && !nextEnd.playerWon && isCheckmate(next)) sfx.lose(); },
      });
      schedulePersist();
    }, 480);
  }
  const boardView = createBoardView(wrapEl, (sq) => { tap.handleTap(sq); });
  initViewToggle(versusRoot, boardView);
  game = createGame(states, moves, sans, boardView, render);
  function handlePlayerMove(move) {
    const next = applyMove(game.state, move);
    const nextEnd = evaluateEnd(game.history.concat([next]), versus.player);
    game.applyAnimated(move, {
      onLanded: () => {
        if (nextEnd.over && nextEnd.playerWon) { sfx.win(); fireConfetti(); }
        maybeAiMove();
      },
    });
    schedulePersist();
  }
  tap = createTapMove(
    () => game.state,
    () => {
      const end = evaluateEnd(game.history, versus.player);
      return !end.over && game.state.turn === versus.player && !versus.thinking;
    },
    handlePlayerMove,
    () => { versus.shakeKey += 1; sfx.wrong(); render(); },
    render
  );
  function newGame(nextPlayer, nextDifficulty) {
    if (versus.aiTimer) window.clearTimeout(versus.aiTimer);
    versus.player = nextPlayer;
    versus.difficulty = nextDifficulty;
    versus.thinking = false;
    tap.clearSelection();
    game.resetAll(startState);
    try { window.localStorage.removeItem(LS_VERSUS); } catch (e) {}
    sfx.select();
    render();
    maybeAiMove();
    schedulePersist();
  }
  versusRoot.querySelector("#vWhite").addEventListener("click", () => newGame("w", versus.difficulty));
  versusRoot.querySelector("#vBlack").addEventListener("click", () => newGame("b", versus.difficulty));
  versusRoot.querySelectorAll("[data-diff]").forEach((b) =>
    b.addEventListener("click", () => newGame(versus.player, b.getAttribute("data-diff"))));
  versusRoot.querySelector("#vNew").addEventListener("click", () => newGame(versus.player, versus.difficulty));
  undoBtn.addEventListener("click", () => {
    if (versus.thinking || game.moves.length === 0) return;
    const plies = game.moves.length;
    const steps = game.state.turn === versus.player ? Math.min(2, plies) : 1;
    game.truncate(plies - steps);
    tap.clearSelection();
    sfx.select();
    render();
    schedulePersist();
  });
  versus.render = render;
  render();
  maybeAiMove();
}

/* ============================================================
   App shell — mode switcher + mute toggle.
   ============================================================ */
const modeQuizBtn = document.getElementById("modeQuiz");
const modeVersusBtn = document.getElementById("modeVersus");
const muteBtn = document.getElementById("muteBtn");
function syncMuteBtn() {
  muteBtn.textContent = muted ? "音 OFF" : "音 ON";
  muteBtn.setAttribute("aria-label", muted ? "サウンドをオンにする" : "サウンドをオフにする");
  muteBtn.setAttribute("aria-pressed", muted ? "true" : "false");
}
muteBtn.addEventListener("click", () => { setMuted(!muted); syncMuteBtn(); if (!muted) sfx.select(); });
syncMuteBtn();

let versusBuilt = false;
function setMode(mode) {
  const isQuiz = mode === "quiz";
  modeQuizBtn.classList.toggle("active", isQuiz);
  modeVersusBtn.classList.toggle("active", !isQuiz);
  modeQuizBtn.setAttribute("aria-pressed", isQuiz ? "true" : "false");
  modeVersusBtn.setAttribute("aria-pressed", !isQuiz ? "true" : "false");
  document.getElementById("quizView").hidden = !isQuiz;
  document.getElementById("versusView").hidden = isQuiz;
  if (!isQuiz && !versusBuilt) { versusBuilt = true; buildVersus(); }
  else if (!isQuiz && versus && versus.render) versus.render();
  else if (isQuiz && solver && solver.render) solver.render();
}
modeQuizBtn.addEventListener("click", () => setMode("quiz"));
modeVersusBtn.addEventListener("click", () => setMode("versus"));

buildQuiz();
setMode("quiz");
