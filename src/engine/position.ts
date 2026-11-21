// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/core/position.cc (FR-2.1..FR-2.6)

import {
  CanonicalSnapshot,
  Color,
  DEFAULT_BOARD_SIZE,
  KoRule,
  NULL_MOVE,
  oppositeColor,
  PASS_MOVE,
  ProofContext,
} from './types';

export { NULL_MOVE, PASS_MOVE };

export function coordFromRowCol(
  row: number,
  col: number,
  size: number = DEFAULT_BOARD_SIZE
): number {
  return row * size + col;
}

export function rowOf(coord: number, size: number = DEFAULT_BOARD_SIZE): number {
  return Math.floor(coord / size);
}

export function colOf(coord: number, size: number = DEFAULT_BOARD_SIZE): number {
  return coord % size;
}

export function coordToSgf(
  coord: number,
  size: number = DEFAULT_BOARD_SIZE
): string {
  if (coord === PASS_MOVE) return 'pass';
  if (coord < 0 || coord >= size * size) return 'null';
  const r = rowOf(coord, size);
  const c = colOf(coord, size);
  return String.fromCharCode(97 + c) + String.fromCharCode(97 + r);
}

export function coordToHumanLabel(
  coord: number,
  size: number = DEFAULT_BOARD_SIZE
): string {
  if (coord === PASS_MOVE) return 'PASS (虚手)';
  if (coord < 0 || coord >= size * size) return '—';
  const r = rowOf(coord, size);
  const c = colOf(coord, size);
  const letters = 'ABCDEFGHJKLMNOPQRST'; // Standard Go skips 'I'
  const colChar = letters[c] || '?';
  const rowNum = size - r;
  return `${colChar}${rowNum} (${coordToSgf(coord, size)})`;
}

export function sgfToCoord(
  sgf: string,
  size: number = DEFAULT_BOARD_SIZE
): number {
  const clean = sgf.trim().toLowerCase();
  if (clean === '' || clean === 'pass' || clean === 'tt') return PASS_MOVE;
  if (clean.length < 2) return NULL_MOVE;
  const c = clean.charCodeAt(0) - 97;
  const r = clean.charCodeAt(1) - 97;
  if (r < 0 || r >= size || c < 0 || c >= size) return NULL_MOVE;
  return coordFromRowCol(r, c, size);
}

// Deterministic 64-bit SplitMix64 hash for Zobrist keys
function deterministicKey(seed: number): bigint {
  let z = BigInt(seed) + 0x9e3779b97f4a7c15n;
  z = ((z ^ (z >> 30n)) * 0xbf58476d1ce4e5b9n) & 0xffffffffffffffffn;
  z = ((z ^ (z >> 27n)) * 0x94d049bb133111ebn) & 0xffffffffffffffffn;
  return (z ^ (z >> 31n)) & 0xffffffffffffffffn;
}

const ZOBRIST_BLACK: bigint[] = [];
const ZOBRIST_WHITE: bigint[] = [];
const ZOBRIST_KO: bigint[] = [];
for (let i = 0; i < 361; i++) {
  ZOBRIST_BLACK.push(deterministicKey(1000 + i));
  ZOBRIST_WHITE.push(deterministicKey(2000 + i));
  ZOBRIST_KO.push(deterministicKey(3000 + i));
}
const ZOBRIST_WHITE_TO_PLAY = deterministicKey(9999);

// Precomputed neighbor lookup tables per board size to eliminate hot-loop allocations
const ORTHO_TABLES = new Map<number, number[][]>();
const DIAG_TABLES = new Map<number, number[][]>();

function getOrthoTable(size: number): number[][] {
  let tbl = ORTHO_TABLES.get(size);
  if (!tbl) {
    tbl = new Array(size * size);
    for (let r = 0; r < size; r++) {
      for (let c = 0; c < size; c++) {
        const nb: number[] = [];
        if (r > 0) nb.push((r - 1) * size + c);
        if (r + 1 < size) nb.push((r + 1) * size + c);
        if (c > 0) nb.push(r * size + (c - 1));
        if (c + 1 < size) nb.push(r * size + (c + 1));
        tbl[r * size + c] = nb;
      }
    }
    ORTHO_TABLES.set(size, tbl);
  }
  return tbl;
}

function getDiagTable(size: number): number[][] {
  let tbl = DIAG_TABLES.get(size);
  if (!tbl) {
    tbl = new Array(size * size);
    for (let r = 0; r < size; r++) {
      for (let c = 0; c < size; c++) {
        const diag: number[] = [];
        if (r > 0 && c > 0) diag.push((r - 1) * size + (c - 1));
        if (r > 0 && c + 1 < size) diag.push((r - 1) * size + (c + 1));
        if (r + 1 < size && c > 0) diag.push((r + 1) * size + (c - 1));
        if (r + 1 < size && c + 1 < size) diag.push((r + 1) * size + (c + 1));
        tbl[r * size + c] = diag;
      }
    }
    DIAG_TABLES.set(size, tbl);
  }
  return tbl;
}

export interface ChainFloodResult {
  stones: Set<number>;
  liberties: Set<number>;
}

export class GoPosition {
  public readonly boardSize: number;
  public readonly grid: Uint8Array;
  public toPlay: Color;
  public koPoint: number;
  public consecutivePasses: number;
  public survivingTargetTokensMask: number;
  public context: ProofContext;
  public historySnapshots: CanonicalSnapshot[];
  public immortalWallSet: Set<number>;
  public originBlackCoords: number[] = [];
  public originWhiteCoords: number[] = [];
  public originToPlay: Color = Color.Black;
  public playedMoveTrace: number[] = [];

  private readonly orthoTable: number[][];
  private readonly diagTable: number[][];
  private boardZobrist: bigint = 0n;
  private cachedZobristHex: string | null = null;

  private readonly bfsStamp: Uint32Array;
  private readonly libStamp: Uint32Array;
  private readonly bfsQueue: Int32Array;
  private stampCounter = 1;

  constructor(
    context: ProofContext,
    boardSize: number = DEFAULT_BOARD_SIZE,
    immortalWallCoords: number[] = []
  ) {
    const numPts = boardSize * boardSize;
    this.boardSize = boardSize;
    this.grid = new Uint8Array(numPts);
    this.toPlay = Color.Black;
    this.koPoint = NULL_MOVE;
    this.consecutivePasses = 0;
    this.context = context;
    this.survivingTargetTokensMask =
      (1 << Math.min(context.initialTokens.length, 30)) - 1;
    this.historySnapshots = [];
    this.immortalWallSet = new Set(immortalWallCoords);
    this.orthoTable = getOrthoTable(boardSize);
    this.diagTable = getDiagTable(boardSize);
    this.bfsStamp = new Uint32Array(numPts);
    this.libStamp = new Uint32Array(numPts);
    this.bfsQueue = new Int32Array(numPts);
  }

  private nextStamp(): number {
    this.stampCounter = (this.stampCounter + 1) >>> 0;
    if (this.stampCounter === 0) {
      this.bfsStamp.fill(0);
      this.libStamp.fill(0);
      this.stampCounter = 1;
    }
    return this.stampCounter;
  }

  public clone(): GoPosition {
    const copy = new GoPosition(this.context, this.boardSize);
    copy.grid.set(this.grid);
    copy.toPlay = this.toPlay;
    copy.koPoint = this.koPoint;
    copy.consecutivePasses = this.consecutivePasses;
    copy.survivingTargetTokensMask = this.survivingTargetTokensMask;
    copy.historySnapshots = this.historySnapshots.slice();
    copy.immortalWallSet = this.immortalWallSet;
    copy.originBlackCoords = this.originBlackCoords;
    copy.originWhiteCoords = this.originWhiteCoords;
    copy.originToPlay = this.originToPlay;
    copy.playedMoveTrace = this.playedMoveTrace.slice();
    copy.boardZobrist = this.boardZobrist;
    copy.cachedZobristHex = this.cachedZobristHex;
    return copy;
  }

  public isCaptureFreeMonotonicHistory(): boolean {
    const n = this.historySnapshots.length;
    if (n <= 1) return true;
    const currCount =
      this.historySnapshots[n - 1].blackCoords.length +
      this.historySnapshots[n - 1].whiteCoords.length;
    for (let i = 0; i < n - 1; i++) {
      const pastCount =
        this.historySnapshots[i].blackCoords.length +
        this.historySnapshots[i].whiteCoords.length;
      if (pastCount >= currCount) return false;
    }
    return true;
  }

  /**
   * True iff placing one stone without capturing strictly exceeds every historical
   * snapshot's total stone count, guaranteeing zero SSK/PSK superko collision even after passes.
   */
  public canNonCaptureExceedAllPastStoneCounts(): boolean {
    const n = this.historySnapshots.length;
    if (n <= 1) return true;
    const currCount =
      this.historySnapshots[n - 1].blackCoords.length +
      this.historySnapshots[n - 1].whiteCoords.length;
    for (let i = 0; i < n - 1; i++) {
      const pastCount =
        this.historySnapshots[i].blackCoords.length +
        this.historySnapshots[i].whiteCoords.length;
      if (pastCount > currCount) return false;
    }
    return true;
  }

  /**
   * Computes an exact canonical digest of the SSK/PSK HistorySet so search caches
   * (such as nodeFrontierCache) never conflate states with distinct superko histories.
   */
  public computeCanonicalHistoryKey(): string {
    if (this.context.koRule === KoRule.SimpleKoOnly) {
      return `simple:${this.koPoint}`;
    }
    const items = this.historySnapshots.map((s) =>
      this.context.koRule === KoRule.SituationalSuperko
        ? `${s.toPlay}:${s.blackCoords.join(',')}/${s.whiteCoords.join(',')}`
        : `${s.blackCoords.join(',')}/${s.whiteCoords.join(',')}`
    );
    items.sort();
    return items.join('|');
  }

  public setupInitialStones(
    blackCoords: number[],
    whiteCoords: number[],
    firstToPlay: Color
  ): void {
    this.grid.fill(Color.Empty);
    this.boardZobrist = 0n;
    for (const c of blackCoords) {
      if (c >= 0 && c < this.grid.length && this.grid[c] === Color.Empty) {
        this.grid[c] = Color.Black;
        this.boardZobrist ^= ZOBRIST_BLACK[c];
      }
    }
    for (const c of whiteCoords) {
      if (c >= 0 && c < this.grid.length) {
        if (this.grid[c] === Color.Black) this.boardZobrist ^= ZOBRIST_BLACK[c];
        if (this.grid[c] !== Color.White) {
          this.grid[c] = Color.White;
          this.boardZobrist ^= ZOBRIST_WHITE[c];
        }
      }
    }
    this.toPlay = firstToPlay;
    this.koPoint = NULL_MOVE;
    this.consecutivePasses = 0;
    this.cachedZobristHex = null;
    this.survivingTargetTokensMask = 0;
    this.context.initialTokens.forEach((tok, idx) => {
      if (this.grid[tok.initialCoord] === tok.stoneColor) {
        this.survivingTargetTokensMask |= 1 << idx;
      }
    });
    this.originBlackCoords = this.getBlackCoords();
    this.originWhiteCoords = this.getWhiteCoords();
    this.originToPlay = firstToPlay;
    this.playedMoveTrace = [];
    this.historySnapshots = [this.currentCanonicalSnapshot()];
  }

  public stoneAt(coord: number): Color {
    if (coord < 0 || coord >= this.grid.length) return Color.Empty;
    return this.grid[coord] as Color;
  }

  public isAtDoublePass(): boolean {
    return this.consecutivePasses >= 2;
  }

  public computeZobristHex(): string {
    if (this.cachedZobristHex !== null) return this.cachedZobristHex;
    let h = this.boardZobrist;
    if (this.toPlay === Color.White) h ^= ZOBRIST_WHITE_TO_PLAY;
    if (this.koPoint >= 0 && this.koPoint < 361) h ^= ZOBRIST_KO[this.koPoint];
    this.cachedZobristHex = h.toString(16).padStart(16, '0');
    return this.cachedZobristHex;
  }

  public getBlackCoords(): number[] {
    const out: number[] = [];
    for (let i = 0; i < this.grid.length; i++) {
      if (this.grid[i] === Color.Black) out.push(i);
    }
    return out;
  }

  public getWhiteCoords(): number[] {
    const out: number[] = [];
    for (let i = 0; i < this.grid.length; i++) {
      if (this.grid[i] === Color.White) out.push(i);
    }
    return out;
  }

  public currentCanonicalSnapshot(): CanonicalSnapshot {
    const blackCoords: number[] = [];
    const whiteCoords: number[] = [];
    const g = this.grid;
    for (let i = 0; i < g.length; i++) {
      const v = g[i];
      if (v === Color.Black) blackCoords.push(i);
      else if (v === Color.White) whiteCoords.push(i);
    }
    return {
      blackCoords,
      whiteCoords,
      toPlay: this.toPlay,
      zobristHex: this.computeZobristHex(),
    };
  }

  public static snapshotsMatch(
    a: CanonicalSnapshot,
    b: CanonicalSnapshot,
    rule: KoRule
  ): boolean {
    if (rule === KoRule.SituationalSuperko && a.toPlay !== b.toPlay) {
      return false;
    }
    if (a.blackCoords.length !== b.blackCoords.length) return false;
    if (a.whiteCoords.length !== b.whiteCoords.length) return false;
    for (let i = 0; i < a.blackCoords.length; i++) {
      if (a.blackCoords[i] !== b.blackCoords[i]) return false;
    }
    for (let i = 0; i < a.whiteCoords.length; i++) {
      if (a.whiteCoords[i] !== b.whiteCoords[i]) return false;
    }
    return true;
  }

  public hasIdenticalHistorySet(other: GoPosition): boolean {
    if (this.historySnapshots.length !== other.historySnapshots.length) {
      return false;
    }
    for (const snapA of this.historySnapshots) {
      const found = other.historySnapshots.some((snapB) =>
        GoPosition.snapshotsMatch(snapA, snapB, this.context.koRule)
      );
      if (!found) return false;
    }
    return true;
  }

  public orthogonalNeighbors(coord: number): number[] {
    return this.orthoTable[coord] ?? [];
  }

  public diagonalNeighbors(coord: number): number[] {
    return this.diagTable[coord] ?? [];
  }

  /**
   * Zero-allocation liberty count check using typed stamp buffers.
   * Returns true iff the chain at `startCoord` has >= `minLibs` liberties.
   */
  public chainHasAtLeastLiberties(startCoord: number, minLibs: number): boolean {
    const color = this.grid[startCoord];
    if (color === Color.Empty) return false;
    const stamp = this.nextStamp();
    this.bfsStamp[startCoord] = stamp;
    this.bfsQueue[0] = startCoord;
    let head = 0;
    let tail = 1;
    let libs = 0;

    while (head < tail) {
      const cur = this.bfsQueue[head++];
      const nbs = this.orthoTable[cur];
      for (let i = 0; i < nbs.length; i++) {
        const nb = nbs[i];
        const nbCol = this.grid[nb];
        if (nbCol === Color.Empty) {
          if (this.libStamp[nb] !== stamp) {
            this.libStamp[nb] = stamp;
            libs++;
            if (libs >= minLibs) return true;
          }
        } else if (nbCol === color && this.bfsStamp[nb] !== stamp) {
          this.bfsStamp[nb] = stamp;
          this.bfsQueue[tail++] = nb;
        }
      }
    }
    return libs >= minLibs;
  }

  public floodFillChain(startCoord: number): ChainFloodResult {
    const stones = new Set<number>();
    const liberties = new Set<number>();
    const color = this.grid[startCoord] as Color;
    if (!color) return { stones, liberties };

    const stamp = this.nextStamp();
    this.bfsStamp[startCoord] = stamp;
    this.bfsQueue[0] = startCoord;
    stones.add(startCoord);
    let head = 0;
    let tail = 1;

    while (head < tail) {
      const cur = this.bfsQueue[head++];
      const nbs = this.orthoTable[cur];
      for (let i = 0; i < nbs.length; i++) {
        const nb = nbs[i];
        const nbColor = this.grid[nb];
        if (nbColor === Color.Empty) {
          liberties.add(nb);
        } else if (nbColor === color && this.bfsStamp[nb] !== stamp) {
          this.bfsStamp[nb] = stamp;
          stones.add(nb);
          this.bfsQueue[tail++] = nb;
        }
      }
    }
    return { stones, liberties };
  }

  public playMove(move: number): {
    legal: boolean;
    capturedCoords: number[];
    isKoCapture: boolean;
  } {
    if (this.consecutivePasses >= 2) {
      return { legal: false, capturedCoords: [], isKoCapture: false };
    }

    if (move === PASS_MOVE) {
      this.koPoint = NULL_MOVE;
      this.consecutivePasses += 1;
      this.toPlay = oppositeColor(this.toPlay);
      this.cachedZobristHex = null;
      this.playedMoveTrace.push(PASS_MOVE);
      this.historySnapshots.push(this.currentCanonicalSnapshot());
      return { legal: true, capturedCoords: [], isKoCapture: false };
    }

    if (
      move < 0 ||
      move >= this.grid.length ||
      this.grid[move] !== Color.Empty ||
      move === this.koPoint
    ) {
      return { legal: false, capturedCoords: [], isKoCapture: false };
    }

    const prevKo = this.koPoint;
    const prevPasses = this.consecutivePasses;
    const prevTokens = this.survivingTargetTokensMask;
    const prevBoardZobrist = this.boardZobrist;

    const us = this.toPlay;
    const them = oppositeColor(us);
    this.grid[move] = us;
    this.boardZobrist ^=
      us === Color.Black ? ZOBRIST_BLACK[move] : ZOBRIST_WHITE[move];

    const capturedCoords: number[] = [];
    let capturedSeen: Set<number> | null = null;
    const nbs = this.orthoTable[move];

    for (let i = 0; i < nbs.length; i++) {
      const nb = nbs[i];
      if (
        this.grid[nb] === them &&
        (capturedSeen === null || !capturedSeen.has(nb))
      ) {
        if (!this.chainHasAtLeastLiberties(nb, 1)) {
          const enemyChain = this.floodFillChain(nb);
          let isImmortal = false;
          for (const s of enemyChain.stones) {
            if (this.immortalWallSet.has(s)) {
              isImmortal = true;
              break;
            }
          }
          if (!isImmortal) {
            if (capturedSeen === null) capturedSeen = new Set<number>();
            for (const s of enemyChain.stones) {
              capturedSeen.add(s);
              capturedCoords.push(s);
            }
          }
        }
      }
    }

    if (capturedCoords.length > 0) {
      const themKeys = them === Color.Black ? ZOBRIST_BLACK : ZOBRIST_WHITE;
      for (let i = 0; i < capturedCoords.length; i++) {
        const cap = capturedCoords[i];
        this.grid[cap] = Color.Empty;
        this.boardZobrist ^= themKeys[cap];
        for (let idx = 0; idx < this.context.initialTokens.length; idx++) {
          if (this.context.initialTokens[idx].initialCoord === cap) {
            this.survivingTargetTokensMask &= ~(1 << idx);
          }
        }
      }
    }

    let isKoCapture = false;
    let nextKo = NULL_MOVE;

    if (capturedCoords.length === 1) {
      const ourChain = this.floodFillChain(move);
      if (ourChain.liberties.size === 0) {
        let ourIsImmortal = false;
        for (const s of ourChain.stones) {
          if (this.immortalWallSet.has(s)) {
            ourIsImmortal = true;
            break;
          }
        }
        if (!ourIsImmortal) {
          this.grid[move] = Color.Empty;
          this.grid[capturedCoords[0]] = them;
          this.boardZobrist = prevBoardZobrist;
          this.survivingTargetTokensMask = prevTokens;
          return { legal: false, capturedCoords: [], isKoCapture: false };
        }
      } else if (ourChain.stones.size === 1 && ourChain.liberties.size === 1) {
        nextKo = capturedCoords[0];
        isKoCapture = true;
      }
    } else if (!this.chainHasAtLeastLiberties(move, 1)) {
      const ourChain = this.floodFillChain(move);
      let ourIsImmortal = false;
      for (const s of ourChain.stones) {
        if (this.immortalWallSet.has(s)) {
          ourIsImmortal = true;
          break;
        }
      }
      if (!ourIsImmortal) {
        this.grid[move] = Color.Empty;
        for (let i = 0; i < capturedCoords.length; i++) {
          this.grid[capturedCoords[i]] = them;
        }
        this.boardZobrist = prevBoardZobrist;
        this.survivingTargetTokensMask = prevTokens;
        return { legal: false, capturedCoords: [], isKoCapture: false };
      }
    }

    this.koPoint = nextKo;
    this.consecutivePasses = 0;
    this.toPlay = them;
    this.cachedZobristHex = null;

    const nextSnap = this.currentCanonicalSnapshot();

    // FR-2.2: Check SSK / PSK against full canonical history snapshots
    if (this.context.koRule !== KoRule.SimpleKoOnly) {
      let violatesSuperko = false;
      for (let i = 0; i < this.historySnapshots.length; i++) {
        if (
          GoPosition.snapshotsMatch(
            this.historySnapshots[i],
            nextSnap,
            this.context.koRule
          )
        ) {
          violatesSuperko = true;
          break;
        }
      }
      if (violatesSuperko) {
        this.grid[move] = Color.Empty;
        for (let i = 0; i < capturedCoords.length; i++) {
          this.grid[capturedCoords[i]] = them;
        }
        this.koPoint = prevKo;
        this.consecutivePasses = prevPasses;
        this.toPlay = us;
        this.boardZobrist = prevBoardZobrist;
        this.cachedZobristHex = null;
        this.survivingTargetTokensMask = prevTokens;
        return { legal: false, capturedCoords: [], isKoCapture: false };
      }
    }

    this.playedMoveTrace.push(move);
    this.historySnapshots.push(nextSnap);
    return { legal: true, capturedCoords, isKoCapture };
  }

  public isLegalMove(
    move: number,
    canExceedPastCounts?: boolean
  ): boolean {
    if (this.consecutivePasses >= 2) return false;
    if (move === PASS_MOVE) return true;
    if (
      move < 0 ||
      move >= this.grid.length ||
      this.grid[move] !== Color.Empty ||
      move === this.koPoint
    ) {
      return false;
    }

    const nbs = this.orthoTable[move];
    let hasEmptyNb = false;
    for (let i = 0; i < nbs.length; i++) {
      if (this.grid[nbs[i]] === Color.Empty) {
        hasEmptyNb = true;
        break;
      }
    }

    const nonCapSafe =
      canExceedPastCounts ?? this.canNonCaptureExceedAllPastStoneCounts();
    if (nonCapSafe && hasEmptyNb) {
      const them = oppositeColor(this.toPlay);
      let mightCapture = false;
      for (let i = 0; i < nbs.length; i++) {
        const n = nbs[i];
        if (this.grid[n] === them && !this.immortalWallSet.has(n)) {
          if (!this.chainHasAtLeastLiberties(n, 2)) {
            mightCapture = true;
            break;
          }
        }
      }
      if (!mightCapture) return true;
    }

    // Fast non-suicide check before cloning for SSK
    if (!hasEmptyNb) {
      const us = this.toPlay;
      const them = oppositeColor(us);
      let connectsAliveFriendly = false;
      let capturesEnemy = false;
      for (let i = 0; i < nbs.length; i++) {
        const n = nbs[i];
        if (this.grid[n] === us) {
          if (this.chainHasAtLeastLiberties(n, 2)) {
            connectsAliveFriendly = true;
            break;
          }
        } else if (this.grid[n] === them && !this.immortalWallSet.has(n)) {
          if (!this.chainHasAtLeastLiberties(n, 2)) {
            capturesEnemy = true;
            break;
          }
        }
      }
      if (!connectsAliveFriendly && !capturesEnemy) {
        return false;
      }
      if (nonCapSafe && connectsAliveFriendly && !capturesEnemy) {
        return true;
      }
    }

    const scratch = this.clone();
    return scratch.playMove(move).legal;
  }

  public generateLegalMoves(regionCoords?: number[] | null): number[] {
    if (this.consecutivePasses >= 2) return [];
    const nonCapSafe = this.canNonCaptureExceedAllPastStoneCounts();
    const legal: number[] = [];

    if (regionCoords !== undefined && regionCoords !== null) {
      for (let i = 0; i < regionCoords.length; i++) {
        const c = regionCoords[i];
        if (this.grid[c] === Color.Empty && c !== this.koPoint) {
          if (this.isLegalMove(c, nonCapSafe)) legal.push(c);
        }
      }
    } else {
      for (let c = 0; c < this.grid.length; c++) {
        if (this.grid[c] === Color.Empty && c !== this.koPoint) {
          if (this.isLegalMove(c, nonCapSafe)) legal.push(c);
        }
      }
    }
    legal.push(PASS_MOVE);
    return legal;
  }
}
