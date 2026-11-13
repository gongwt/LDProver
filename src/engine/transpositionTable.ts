// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/tt/transposition_table.cc (FR-6.1..FR-6.9)

import { GoPosition } from './position';
import { ProofCertificateRZ } from './relevanceZone';
import {
  CanonicalSnapshot,
  Color,
  KoRule,
  NULL_MOVE,
  ProofContext,
  ProofOutcome,
} from './types';

export interface BoardTTEntry {
  zobristHex: string;
  proofContextId: string;
  blackCoords: number[];
  whiteCoords: number[];
  toPlay: Color;
  koPoint: number;
  consecutivePasses: number;
  survivingTokensMask: number;
  historySnapshots: CanonicalSnapshot[];
  sourceMonotonicHistory: boolean;
  hasCaptureInSubtree: boolean;
  pn: number;
  dn: number;
  outcome: ProofOutcome;
  isKoDependent: boolean;
  proofClosureAvailable: boolean;
  proofDagNodeId: number;
  proofRz: ProofCertificateRZ;
  disproofRz: ProofCertificateRZ;
}

export interface RadixPatternRecord {
  proofContextId: string;
  toPlay: Color;
  koPoint: number;
  consecutivePasses: number;
  survivingTokensMask: number;
  historySnapshots: CanonicalSnapshot[];
  storedRz: ProofCertificateRZ;
  zoneCoords: number[];
  storedZoneColors: Color[];
  sourceMonotonicHistory: boolean;
  hasCaptureInSubtree: boolean;
  pn: number;
  dn: number;
  outcome: ProofOutcome;
  proofDagNodeId: number;
  proofClosureAvailable: boolean;
  ghiFlag: boolean;
  lastTouchSeq: number;
}

export type PatternHitGrade = 'MISS' | 'HEURISTIC_ONLY' | 'PROOF_REUSABLE';

export class TranspositionStore {
  private boardBuckets = new Map<string, BoardTTEntry[]>();
  private patternRecords: RadixPatternRecord[] = [];
  private touchSeq = 0;

  public boardHits = 0;
  public patternHits = 0;
  public patternProofReusableHits = 0;
  public ghiRejectedCount = 0;

  // FR-6.2: Clear both tables at the start of every problem
  public clearAll(): void {
    this.boardBuckets.clear();
    this.patternRecords = [];
    this.touchSeq = 0;
    this.boardHits = 0;
    this.patternHits = 0;
    this.patternProofReusableHits = 0;
    this.ghiRejectedCount = 0;
  }

  // FR-6.1: BoardTT lookup with SSK-sound transposition equivalence & GHI revalidation
  public lookupBoardTT(
    pos: GoPosition,
    context: ProofContext,
    revalidateSubtreeFn?: (dagNodeId: number, outcome: ProofOutcome) => boolean
  ): BoardTTEntry | null {
    const zHex = pos.computeZobristHex();
    const bucket = this.boardBuckets.get(zHex);
    if (!bucket) return null;

    const qBlack = pos.getBlackCoords();
    const qWhite = pos.getWhiteCoords();
    const queryMonotonic = pos.isCaptureFreeMonotonicHistory();

    for (const entry of bucket) {
      if (
        entry.proofContextId !== context.contextId ||
        entry.toPlay !== pos.toPlay ||
        entry.koPoint !== pos.koPoint ||
        entry.consecutivePasses !== pos.consecutivePasses ||
        entry.survivingTokensMask !== pos.survivingTargetTokensMask
      ) {
        continue;
      }

      if (
        entry.blackCoords.length !== qBlack.length ||
        entry.whiteCoords.length !== qWhite.length
      ) {
        continue;
      }
      let coordsMatch = true;
      for (let i = 0; i < qBlack.length; i++) {
        if (entry.blackCoords[i] !== qBlack[i]) {
          coordsMatch = false;
          break;
        }
      }
      if (!coordsMatch) continue;
      for (let i = 0; i < qWhite.length; i++) {
        if (entry.whiteCoords[i] !== qWhite[i]) {
          coordsMatch = false;
          break;
        }
      }
      if (!coordsMatch) continue;

      if (context.koRule !== KoRule.SimpleKoOnly) {
        // 1. O(1) Monotonic Stone-Count Certificate:
        // If neither source nor query had any captures/passes in history AND the proven sub-DAG
        // contains no captures, no state in the sub-DAG can ever match any strict ancestor snapshot!
        const monotonicSafe =
          queryMonotonic &&
          entry.sourceMonotonicHistory &&
          !entry.hasCaptureInSubtree;

        if (!monotonicSafe) {
          let histOk =
            entry.historySnapshots.length === pos.historySnapshots.length;
          if (histOk) {
            for (const qSnap of pos.historySnapshots) {
              const found = entry.historySnapshots.some((eSnap) =>
                GoPosition.snapshotsMatch(qSnap, eSnap, context.koRule)
              );
              if (!found) {
                histOk = false;
                break;
              }
            }
          }
          if (!histOk) {
            if (
              entry.proofClosureAvailable &&
              entry.outcome !== ProofOutcome.Unknown &&
              revalidateSubtreeFn
            ) {
              if (!revalidateSubtreeFn(entry.proofDagNodeId, entry.outcome)) {
                this.ghiRejectedCount++;
                continue;
              }
            } else {
              continue;
            }
          }
        }
      }

      this.boardHits++;
      return entry;
    }

    return null;
  }

  public storeBoardTT(
    pos: GoPosition,
    context: ProofContext,
    pn: number,
    dn: number,
    outcome: ProofOutcome,
    isKoDependent: boolean,
    proofClosureAvailable: boolean,
    proofDagNodeId: number,
    proofRz: ProofCertificateRZ,
    disproofRz: ProofCertificateRZ,
    hasCaptureInSubtree = false
  ): void {
    // FR-5.7: KoDependent states never enter decisive proof TT
    if (isKoDependent && outcome !== ProofOutcome.Unknown) return;

    const zHex = pos.computeZobristHex();
    const bucket = this.boardBuckets.get(zHex) ?? [];
    const newEntry: BoardTTEntry = {
      zobristHex: zHex,
      proofContextId: context.contextId,
      blackCoords: pos.getBlackCoords(),
      whiteCoords: pos.getWhiteCoords(),
      toPlay: pos.toPlay,
      koPoint: pos.koPoint,
      consecutivePasses: pos.consecutivePasses,
      survivingTokensMask: pos.survivingTargetTokensMask,
      historySnapshots: pos.historySnapshots.slice(),
      sourceMonotonicHistory: pos.isCaptureFreeMonotonicHistory(),
      hasCaptureInSubtree,
      pn,
      dn,
      outcome,
      isKoDependent,
      proofClosureAvailable,
      proofDagNodeId,
      proofRz,
      disproofRz,
    };
    bucket.push(newEntry);
    this.boardBuckets.set(zHex, bucket);
  }

  // FR-6.3, FR-6.4: Two-grade PatternTT lookup projecting position onto stored RZ
  public lookupPatternTT(
    pos: GoPosition,
    context: ProofContext
  ): { grade: PatternHitGrade; record: RadixPatternRecord | null } {
    const queryMonotonic = pos.isCaptureFreeMonotonicHistory();
    for (let idx = this.patternRecords.length - 1; idx >= 0; idx--) {
      const rec = this.patternRecords[idx];
      if (
        rec.proofContextId !== context.contextId ||
        rec.toPlay !== pos.toPlay ||
        rec.consecutivePasses !== pos.consecutivePasses ||
        rec.survivingTokensMask !== pos.survivingTargetTokensMask
      ) {
        continue;
      }

      const zLen = rec.zoneCoords.length;
      if (zLen === 0) continue;

      let patternMatches = true;
      for (let k = 0; k < zLen; k++) {
        if (pos.grid[rec.zoneCoords[k]] !== rec.storedZoneColors[k]) {
          patternMatches = false;
          break;
        }
      }
      if (!patternMatches) continue;

      const qKo =
        pos.koPoint >= 0 && rec.storedRz.has(pos.koPoint)
          ? pos.koPoint
          : NULL_MOVE;
      const sKo =
        rec.koPoint >= 0 && rec.storedRz.has(rec.koPoint)
          ? rec.koPoint
          : NULL_MOVE;
      if (qKo !== sKo) continue;

      rec.lastTouchSeq = ++this.touchSeq;
      this.patternHits++;

      // Check full board + HistorySet equality for direct ProofReusable grade (FR-6.3, FR-6.9);
      // any outside-RZ stone difference returns HEURISTIC_ONLY so DfpnSolver runs full
      // RevalidateSourceProofOnQueryState before accepting proof reuse.
      let fullHistEqual =
        pos.historySnapshots.length === rec.historySnapshots.length &&
        pos.historySnapshots.length > 0 &&
        GoPosition.snapshotsMatch(
          pos.historySnapshots[pos.historySnapshots.length - 1],
          rec.historySnapshots[rec.historySnapshots.length - 1],
          KoRule.SituationalSuperko
        );
      if (fullHistEqual && context.koRule !== KoRule.SimpleKoOnly) {
        for (let i = 0; i < pos.historySnapshots.length; i++) {
          if (
            !GoPosition.snapshotsMatch(
              pos.historySnapshots[i],
              rec.historySnapshots[i],
              context.koRule
            )
          ) {
            fullHistEqual = false;
            break;
          }
        }
      }

      if (fullHistEqual && rec.proofClosureAvailable && !rec.ghiFlag) {
        this.patternProofReusableHits++;
        return { grade: 'PROOF_REUSABLE', record: rec };
      }

      return { grade: 'HEURISTIC_ONLY', record: rec };
    }

    return { grade: 'MISS', record: null };
  }

  public storePatternTT(
    pos: GoPosition,
    context: ProofContext,
    zone: ProofCertificateRZ,
    pn: number,
    dn: number,
    outcome: ProofOutcome,
    proofDagNodeId: number,
    proofClosureAvailable: boolean,
    hasCaptureInSubtree = false
  ): void {
    if (outcome === ProofOutcome.Unknown || zone.size === 0) return;
    const zoneCoords = zone.toArray();
    const storedZoneColors = zoneCoords.map((c) => pos.stoneAt(c));
    this.patternRecords.push({
      proofContextId: context.contextId,
      toPlay: pos.toPlay,
      koPoint: pos.koPoint,
      consecutivePasses: pos.consecutivePasses,
      survivingTokensMask: pos.survivingTargetTokensMask,
      historySnapshots: pos.historySnapshots.slice(),
      storedRz: zone,
      zoneCoords,
      storedZoneColors,
      sourceMonotonicHistory: pos.isCaptureFreeMonotonicHistory(),
      hasCaptureInSubtree,
      pn,
      dn,
      outcome,
      proofDagNodeId,
      proofClosureAvailable,
      ghiFlag: false,
      lastTouchSeq: ++this.touchSeq,
    });
  }
}
