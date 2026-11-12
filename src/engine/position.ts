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

// Deterministic 64-bit FNV-1a / SplitMix style hash for Zobrist keys
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

  constructor(
    context: ProofContext,
    boardSize: number = DEFAULT_BOARD_SIZE,
    immortalWallCoords: number[] = []
  ) {
    this.boardSize = boardSize;
    this.grid = new Uint8Array(boardSize * boardSize);
    this.toPlay = Color.Black;
    this.koPoint = NULL_MOVE;
    this.consecutivePasses = 0;
    this.context = context;
    this.survivingTargetTokensMask =
      (1 << Math.min(context.initialTokens.length, 30)) - 1;
    this.historySnapshots = [];
    this.immortalWallSet = new Set(immortalWallCoords);
  }

  public clone(): GoPosition {
    const copy = new GoPosition(this.context, this.boardSize);
    copy.grid.set(this.grid);
    copy.toPlay = this.toPlay;
    copy.koPoint = this.koPoint;
    copy.consecutivePasses = this.consecutivePasses;
    copy.survivingTargetTokensMask = this.survivingTargetTokensMask;
    // CanonicalSnapshot objects and immortalWallSet are never mutated after creation
    copy.historySnapshots = this.historySnapshots.slice();
    copy.immortalWallSet = this.immortalWallSet;
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

  public setupInitialStones(
    blackCoords: number[],
    whiteCoords: number[],
    firstToPlay: Color
  ): void {
    this.grid.fill(Color.Empty);
    for (const c of blackCoords) {
      if (c >= 0 && c < this.grid.length) this.grid[c] = Color.Black;
    }
    for (const c of whiteCoords) {
      if (c >= 0 && c < this.grid.length) this.grid[c] = Color.White;
    }
    this.toPlay = firstToPlay;
    this.koPoint = NULL_MOVE;
    this.consecutivePasses = 0;
    this.survivingTargetTokensMask = 0;
    this.context.initialTokens.forEach((tok, idx) => {
      if (this.grid[tok.initialCoord] === tok.stoneColor) {
        this.survivingTargetTokensMask |= 1 << idx;
      }
    });
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
    let h = 0n;
    for (let i = 0; i < this.grid.length; i++) {
      if (this.grid[i] === Color.Black) h ^= ZOBRIST_BLACK[i];
      else if (this.grid[i] === Color.White) h ^= ZOBRIST_WHITE[i];
    }
    if (this.toPlay === Color.White) h ^= ZOBRIST_WHITE_TO_PLAY;
    if (this.koPoint >= 0 && this.koPoint < 361) h ^= ZOBRIST_KO[this.koPoint];
    return h.toString(16).padStart(16, '0');
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
    return {
      blackCoords: this.getBlackCoords(),
      whiteCoords: this.getWhiteCoords(),
      toPlay: this.toPlay,
      zobristHex: this.computeZobristHex(),
    };
  }

  public static snapshotsMatch(
    a: CanonicalSnapshot,
    b: CanonicalSnapshot,
    rule: KoRule
  ): boolean {
    if (a.blackCoords.length !== b.blackCoords.length) return false;
    if (a.whiteCoords.length !== b.whiteCoords.length) return false;
    for (let i = 0; i < a.blackCoords.length; i++) {
      if (a.blackCoords[i] !== b.blackCoords[i]) return false;
    }
    for (let i = 0; i < a.whiteCoords.length; i++) {
      if (a.whiteCoords[i] !== b.whiteCoords[i]) return false;
    }
    if (rule === KoRule.SituationalSuperko) {
      return a.toPlay === b.toPlay;
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
    const r = rowOf(coord, this.boardSize);
    const c = colOf(coord, this.boardSize);
    const nb: number[] = [];
    if (r > 0) nb.push(coordFromRowCol(r - 1, c, this.boardSize));
    if (r + 1 < this.boardSize) nb.push(coordFromRowCol(r + 1, c, this.boardSize));
    if (c > 0) nb.push(coordFromRowCol(r, c - 1, this.boardSize));
    if (c + 1 < this.boardSize) nb.push(coordFromRowCol(r, c + 1, this.boardSize));
    return nb;
  }

  public diagonalNeighbors(coord: number): number[] {
    const r = rowOf(coord, this.boardSize);
    const c = colOf(coord, this.boardSize);
    const diag: number[] = [];
    if (r > 0 && c > 0) diag.push(coordFromRowCol(r - 1, c - 1, this.boardSize));
    if (r > 0 && c + 1 < this.boardSize)
      diag.push(coordFromRowCol(r - 1, c + 1, this.boardSize));
    if (r + 1 < this.boardSize && c > 0)
      diag.push(coordFromRowCol(r + 1, c - 1, this.boardSize));
    if (r + 1 < this.boardSize && c + 1 < this.boardSize)
      diag.push(coordFromRowCol(r + 1, c + 1, this.boardSize));
    return diag;
  }

  public floodFillChain(startCoord: number): ChainFloodResult {
    const stones = new Set<number>();
    const liberties = new Set<number>();
    const color = this.stoneAt(startCoord);
    if (color === Color.Empty) return { stones, liberties };

    const queue: number[] = [startCoord];
    stones.add(startCoord);

    while (queue.length > 0) {
      const cur = queue.shift()!;
      for (const nb of this.orthogonalNeighbors(cur)) {
        const nbColor = this.stoneAt(nb);
        if (nbColor === Color.Empty) {
          liberties.add(nb);
        } else if (nbColor === color && !stones.has(nb)) {
          stones.add(nb);
          queue.push(nb);
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
    if (this.isAtDoublePass()) {
      return { legal: false, capturedCoords: [], isKoCapture: false };
    }

    if (move === PASS_MOVE) {
      this.koPoint = NULL_MOVE;
      this.consecutivePasses += 1;
      this.toPlay = oppositeColor(this.toPlay);
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

    const prevGrid = new Uint8Array(this.grid);
    const prevKo = this.koPoint;
    const prevPasses = this.consecutivePasses;
    const prevTokens = this.survivingTargetTokensMask;

    const us = this.toPlay;
    const them = oppositeColor(us);
    this.grid[move] = us;

    const capturedSet = new Set<number>();
    for (const nb of this.orthogonalNeighbors(move)) {
      if (this.grid[nb] === them && !capturedSet.has(nb)) {
        const enemyChain = this.floodFillChain(nb);
        // Immortal outer boundary stones cannot be captured in local problem zone
        const isImmortal = Array.from(enemyChain.stones).some((s) =>
          this.immortalWallSet.has(s)
        );
        if (enemyChain.liberties.size === 0 && !isImmortal) {
          for (const s of enemyChain.stones) capturedSet.add(s);
        }
      }
    }

    const capturedCoords = Array.from(capturedSet);
    for (const cap of capturedCoords) {
      this.grid[cap] = Color.Empty;
      // FR-2.6: Permanently remove captured crucial_stone target tokens
      this.context.initialTokens.forEach((tok, idx) => {
        if (tok.initialCoord === cap) {
          this.survivingTargetTokensMask &= ~(1 << idx);
        }
      });
    }

    const ourChain = this.floodFillChain(move);
    const ourIsImmortal = Array.from(ourChain.stones).some((s) =>
      this.immortalWallSet.has(s)
    );
    if (ourChain.liberties.size === 0 && !ourIsImmortal) {
      // Suicide is forbidden (FR-2.1, C-2)
      this.grid.set(prevGrid);
      this.survivingTargetTokensMask = prevTokens;
      return { legal: false, capturedCoords: [], isKoCapture: false };
    }

    let nextKo = NULL_MOVE;
    let isKoCapture = false;
    if (
      capturedCoords.length === 1 &&
      ourChain.stones.size === 1 &&
      ourChain.liberties.size === 1
    ) {
      nextKo = capturedCoords[0];
      isKoCapture = true;
    }

    this.koPoint = nextKo;
    this.consecutivePasses = 0;
    this.toPlay = them;

    // FR-2.2: Check SSK / PSK against full canonical history snapshots
    if (this.context.koRule !== KoRule.SimpleKoOnly) {
      const nextSnap = this.currentCanonicalSnapshot();
      const violatesSuperko = this.historySnapshots.some((past) =>
        GoPosition.snapshotsMatch(past, nextSnap, this.context.koRule)
      );
      if (violatesSuperko) {
        this.grid.set(prevGrid);
        this.koPoint = prevKo;
        this.consecutivePasses = prevPasses;
        this.toPlay = us;
        this.survivingTargetTokensMask = prevTokens;
        return { legal: false, capturedCoords: [], isKoCapture: false };
      }
    }

    this.historySnapshots.push(this.currentCanonicalSnapshot());
    return { legal: true, capturedCoords, isKoCapture };
  }

  public isLegalMove(move: number, knownMonotonicHistory?: boolean): boolean {
    if (this.isAtDoublePass()) return false;
    if (move === PASS_MOVE) return true;
    if (
      move < 0 ||
      move >= this.grid.length ||
      this.grid[move] !== Color.Empty ||
      move === this.koPoint
    ) {
      return false;
    }

    // Fast path: if `move` has an empty orthogonal neighbor (guaranteed >=1 liberty, no suicide),
    // puts no adjacent enemy stone into 0-liberty capture, and history is strictly monotonic,
    // then neither suicide nor Superko can trigger.
    const monotonic =
      knownMonotonicHistory ?? this.isCaptureFreeMonotonicHistory();
    if (monotonic) {
      const nbs = this.orthogonalNeighbors(move);
      const hasEmptyNb = nbs.some((n) => this.grid[n] === Color.Empty);
      if (hasEmptyNb) {
        const them = oppositeColor(this.toPlay);
        let mightCapture = false;
        for (const n of nbs) {
          if (this.grid[n] === them && !this.immortalWallSet.has(n)) {
            if (this.floodFillChain(n).liberties.size <= 1) {
              mightCapture = true;
              break;
            }
          }
        }
        if (!mightCapture) return true;
      }
    }

    const scratch = this.clone();
    return scratch.playMove(move).legal;
  }

  public generateLegalMoves(regionCoords?: number[]): number[] {
    if (this.isAtDoublePass()) return [];
    const candidates =
      regionCoords && regionCoords.length > 0
        ? regionCoords
        : Array.from({ length: this.grid.length }, (_, i) => i);

    const monotonic = this.isCaptureFreeMonotonicHistory();
    const legal: number[] = [];
    for (const c of candidates) {
      if (this.grid[c] === Color.Empty && c !== this.koPoint) {
        if (this.isLegalMove(c, monotonic)) legal.push(c);
      }
    }
    legal.push(PASS_MOVE);
    return legal;
  }
}
