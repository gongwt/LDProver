// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/rz/relevance_zone.cc (FR-5.1..FR-5.7)

import { GoPosition, PASS_MOVE } from './position';

// FR-5.1: Type-isolated masks (no implicit conversion allowed)
export class ProblemSearchMask {
  public readonly coords: ReadonlySet<number>;
  constructor(coords: Iterable<number> = []) {
    this.coords = new Set(coords);
  }
}

export class NNAttentionMask {
  public readonly coords: ReadonlySet<number>;
  constructor(coords: Iterable<number> = []) {
    this.coords = new Set(coords);
  }
}

function createLockedEmptySet(): ReadonlySet<number> {
  const s = new Set<number>();
  const throwImmutable = (): never => {
    throw new TypeError('ProofCertificateRZ.EMPTY is immutable');
  };
  Object.defineProperty(s, 'add', { value: throwImmutable });
  Object.defineProperty(s, 'delete', { value: throwImmutable });
  Object.defineProperty(s, 'clear', { value: throwImmutable });
  return Object.freeze(s);
}

export class ProofCertificateRZ {
  private static readonly LOCKED_EMPTY_SET: ReadonlySet<number> =
    createLockedEmptySet();
  public static readonly EMPTY: ProofCertificateRZ = Object.freeze(
    new ProofCertificateRZ()
  ) as ProofCertificateRZ;

  private readonly bits: ReadonlySet<number>;

  constructor(coords?: Iterable<number>) {
    if (coords === undefined) {
      this.bits = ProofCertificateRZ.LOCKED_EMPTY_SET;
    } else {
      const s = new Set<number>(coords);
      this.bits = s.size === 0 ? ProofCertificateRZ.LOCKED_EMPTY_SET : s;
    }
  }

  public has(coord: number): boolean {
    return this.bits.has(coord);
  }

  public get size(): number {
    return this.bits.size;
  }

  public toArray(): number[] {
    if (this.bits.size === 0) return [];
    return Array.from(this.bits).sort((a, b) => a - b);
  }

  public unionWith(other: ProofCertificateRZ): ProofCertificateRZ {
    if (this.bits.size === 0 && other.bits.size === 0) {
      return ProofCertificateRZ.EMPTY;
    }
    const merged = new Set<number>(this.bits);
    for (const c of other.bits) merged.add(c);
    return new ProofCertificateRZ(merged);
  }
}

export class RelevanceZoneEngine {
  // FR-5.2 (A) & FR-5.3 (B'): Single witness move influence closure
  public computeSingleWitnessRZ(
    parentPos: GoPosition,
    witnessMove: number,
    childRz: ProofCertificateRZ
  ): ProofCertificateRZ {
    const rz = new Set<number>(childRz.toArray());

    if (witnessMove >= 0 && witnessMove < parentPos.grid.length) {
      rz.add(witnessMove);
      for (const nb of parentPos.orthogonalNeighbors(witnessMove)) {
        if (rz.has(nb) || parentPos.stoneAt(nb) !== 0) {
          const { stones, liberties } = parentPos.floodFillChain(nb);
          const intersects =
            nb === witnessMove || Array.from(stones).some((s) => rz.has(s));
          if (intersects) {
            for (const s of stones) rz.add(s);
            for (const l of liberties) rz.add(l);
          }
        }
      }
    }

    // Expand chains intersecting current RZ with their immediate liberties
    for (const coord of Array.from(rz)) {
      if (
         parentPos.stoneAt(coord) !== 0 &&
        !parentPos.immortalWallSet.has(coord)
      ) {
        const { stones, liberties } = parentPos.floodFillChain(coord);
        for (const s of stones) rz.add(s);
        for (const l of liberties) rz.add(l);
      }
    }

    return new ProofCertificateRZ(rz);
  }

  // FR-5.2 (B) & FR-5.3 (A'): Opponent all-moves union + triple safety closure
  public computeAllChildrenUnionRZ(
    parentPos: GoPosition,
    childrenRzs: ProofCertificateRZ[]
  ): ProofCertificateRZ {
    const unionSet = new Set<number>();
    for (const crz of childrenRzs) {
      for (const c of crz.toArray()) unionSet.add(c);
    }

    const closed = new Set<number>(unionSet);
    for (const coord of Array.from(unionSet)) {
      if (
        parentPos.stoneAt(coord) !== 0 &&
        !parentPos.immortalWallSet.has(coord)
      ) {
        const { stones, liberties } = parentPos.floodFillChain(coord);
        for (const s of stones) closed.add(s);
        for (const l of liberties) closed.add(l);
      }
      for (const nb of parentPos.orthogonalNeighbors(coord)) {
        if (
          parentPos.stoneAt(nb) !== 0 &&
          !parentPos.immortalWallSet.has(nb)
        ) {
          const { stones, liberties } = parentPos.floodFillChain(nb);
          if (liberties.size <= 2) {
            for (const s of stones) closed.add(s);
            for (const l of liberties) closed.add(l);
          }
        }
      }
    }

    if (parentPos.koPoint >= 0) {
      closed.add(parentPos.koPoint);
    }

    return new ProofCertificateRZ(closed);
  }

  // FR-5.5: Candidate filter only. Must be followed by QueryState + HistorySet
  // replay verification before generating an OutsideRZRevalidated Pruned* node.
  public isOutsideRZCandidate(
    move: number,
    certRz: ProofCertificateRZ
  ): boolean {
    if (move === PASS_MOVE) return false;
    return !certRz.has(move);
  }
}
