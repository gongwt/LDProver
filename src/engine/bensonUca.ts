// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/terminal/benson_uca.cc (FR-3.1..FR-3.9).
//
// Soundness & Local Model Invariant (NFR-1):
// `computeBensonUca` and `evaluateTerminal` implement Classic Benson's greatest-fixpoint
// algorithm (David B. Benson, "Life in the Game of Go", Information Sciences 10, 1976)
// subject to the explicit Local Tsumego Boundary Axiom (`immortalWallSet` exported in lproof/1):
//   1. Chains are strictly raw orthogonally-connected stone components (no super-chain
//      merging across shared liberties or tiger's mouths).
//   2. Outer shell boundary stones in `immortalWallSet` (stones outside the problem's `region`
//      mask in `masked_sgf_str`) are treated as uncapturable boundary walls: friendly chains
//      containing an immortal wall stone are anchored alive, and complement regions containing
//      an enemy immortal wall stone cannot be vital eyes.
//   3. A region R is vital to chain C in active set X_k iff every boundary chain of R
//      belongs to X_k AND every empty intersection of R is an orthogonal liberty of C
//      (no artificial cap on emptyPoints.size).
//   4. Each vital region contributes strictly 1 towards Benson's >= 2 vital-region
//      fixpoint threshold (never 2 eyes from a single multi-point cavity).
//
// Eye-shape topology classification (`classifyDiagnosticTopology`) and heuristic eye
// potential estimation (`estimateHeuristicShapePotential`) are strictly separated from
// formal terminal adjudication and used solely for UI inspection and df-pn move ordering.

import { GoPosition, colOf, rowOf } from './position';
import {
  Color,
  EyeTopologyType,
  LogicalOp,
  oppositeColor,
  ProofContext,
  SearchGoal,
  TargetToken,
  TerminalStatus,
} from './types';

export interface BensonChainInfo {
  chainId: number;
  color: Color;
  stones: Set<number>;
  liberties: Set<number>;
  vitalRegionIds: number[];
  isUcaAlive: boolean;
}

export interface BensonEyeRegion {
  regionId: number;
  enclosingColor: Color;
  emptyPoints: Set<number>;
  enemyStones: Set<number>;
  boundaryChainIds: number[];
  topology: EyeTopologyType;
  vitalPoints: number[];
  eyeCountContribution: number;
}

export interface TerminalEvalResult {
  status: TerminalStatus;
  evidenceKind:
    | 'NONE'
    | 'BENSON_UCA'
    | 'TOKENS_CAPTURED'
    | 'DOUBLE_PASS_RESOLUTION'
    | 'EMPTY_TARGET_CONSTANT_FALSE';
  leafCertificateRz: Set<number>;
  bensonAliveCoords: number[];
  eyeTopologyRegions: {
    regionId: number;
    coords: number[];
    topology: EyeTopologyType;
    enclosingColor: Color;
    vitalPoints: number[];
  }[];
  diagnosticNote: string;
}

export class BensonTerminalEvaluator {
  private enemyPlayGainsLiberties(
    pos: GoPosition,
    p: number,
    enemyColor: Color,
    enclosingColor: Color
  ): boolean {
    const newLibs = new Set<number>();
    for (const nb of pos.orthogonalNeighbors(p)) {
      const st = pos.stoneAt(nb);
      if (st === Color.Empty) {
        newLibs.add(nb);
        if (newLibs.size >= 2) return true;
      } else if (st === enemyColor) {
        const ech = pos.floodFillChain(nb);
        for (const l of ech.liberties) {
          if (l !== p) {
            newLibs.add(l);
            if (newLibs.size >= 2) return true;
          }
        }
      } else if (st === enclosingColor) {
        const fch = pos.floodFillChain(nb);
        if (fch.liberties.size <= 1) {
          for (const s of fch.stones) {
            newLibs.add(s);
            if (newLibs.size >= 2) return true;
          }
        }
      }
    }
    return newLibs.size >= 2;
  }

  // Diagnostic & heuristic topology classifier for small enclosed regions (UI & ordering only;
  // never overrides Classic Benson fixpoint soundness).
  private classifyDiagnosticTopology(
    pos: GoPosition,
    emptyPoints: Set<number>,
    enemyStones: Set<number>,
    enclosingColor: Color,
    boundaryChains: BensonChainInfo[],
    isBensonVital: boolean
  ): {
    topology: EyeTopologyType;
    vitalPoints: number[];
  } {
    const vitalPoints: number[] = [];
    if (isBensonVital) {
      if (emptyPoints.size >= 3) {
        for (const p of emptyPoints) {
          const deg = pos
            .orthogonalNeighbors(p)
            .filter((n) => emptyPoints.has(n)).length;
          if (deg >= 2) vitalPoints.push(p);
        }
      }
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
      };
    }

    if (boundaryChains.length === 0 || emptyPoints.size === 0) {
      return { topology: EyeTopologyType.SemeaiDame, vitalPoints: [] };
    }

    for (const ch of boundaryChains) {
      if (ch.liberties.size <= 1) {
        return {
          topology: EyeTopologyType.FalseEye,
          vitalPoints: Array.from(ch.liberties),
        };
      }
    }

    const enemyColor = oppositeColor(enclosingColor);
    if (emptyPoints.size === 1 && enemyStones.size === 0) {
      const pt = Array.from(emptyPoints)[0];
      const r = rowOf(pt, pos.boardSize);
      const c = colOf(pt, pos.boardSize);
      const isEdgeOrCorner =
        r === 0 ||
        r === pos.boardSize - 1 ||
        c === 0 ||
        c === pos.boardSize - 1;
      const maxAllowedEnemy = isEdgeOrCorner ? 0 : 1;

      let enemyControlledDiags = 0;
      let unsettledDiags = 0;
      for (const d of pos.diagonalNeighbors(pt)) {
        const dCol = pos.stoneAt(d);
        if (dCol === enemyColor) {
          const ech = pos.floodFillChain(d);
          if (
            ech.liberties.size >= 2 ||
            Array.from(ech.liberties).some((el) =>
              this.enemyPlayGainsLiberties(pos, el, enemyColor, enclosingColor)
            )
          ) {
            enemyControlledDiags++;
          }
        } else if (dCol === Color.Empty) {
          if (
            pos
              .orthogonalNeighbors(d)
              .some((n) => pos.stoneAt(n) === enemyColor)
          ) {
            unsettledDiags++;
            vitalPoints.push(d);
          }
        }
      }

      for (const ch of boundaryChains) {
        if (ch.liberties.size === 2 && ch.liberties.has(pt)) {
          const otherLib = Array.from(ch.liberties).find((l) => l !== pt);
          if (otherLib !== undefined && !vitalPoints.includes(otherLib)) {
            vitalPoints.push(otherLib);
          }
        }
      }

      if (enemyControlledDiags > maxAllowedEnemy) {
        return { topology: EyeTopologyType.FalseEye, vitalPoints };
      }
      if (enemyControlledDiags + unsettledDiags > maxAllowedEnemy || boundaryChains.length >= 2) {
        return { topology: EyeTopologyType.HalfEye, vitalPoints };
      }
    }

    if (emptyPoints.size <= 6) {
      for (const p of emptyPoints) {
        const deg = pos
          .orthogonalNeighbors(p)
          .filter((n) => emptyPoints.has(n)).length;
        if (deg >= 2 || emptyPoints.size <= 2) vitalPoints.push(p);
      }
      return { topology: EyeTopologyType.HalfEye, vitalPoints };
    }

    return { topology: EyeTopologyType.SemeaiDame, vitalPoints };
  }

  private readonly visitedStonesBuf = new Uint8Array(361);
  private readonly visitedCompBuf = new Uint8Array(361);
  private readonly stoneToChainBuf = new Int32Array(361);
  private readonly queueBuf = new Int32Array(361);
  private readonly emptyPtsBuf = new Int32Array(361);
  private readonly enemyPtsBuf = new Int32Array(361);
  private readonly bChainBuf = new Int32Array(361);
  private readonly seenChainStamp = new Uint32Array(361);
  private chainStampCounter = 1;

  // FR-3.1: Strictly Pure Classic Benson (1976) Unconditional Alive (UCA) greatest-fixpoint solver
  public computeBensonUca(
    pos: GoPosition,
    color: Color,
    includeDiagnostics = true
  ): {
    ucaStones: Set<number>;
    chains: BensonChainInfo[];
    regions: BensonEyeRegion[];
    vitalRz: Set<number>;
  } {
    const gridLen = pos.grid.length;
    const visitedStones =
      gridLen <= 361
        ? this.visitedStonesBuf.subarray(0, gridLen)
        : new Uint8Array(gridLen);
    visitedStones.fill(0);
    const stoneToChainId =
      gridLen <= 361
        ? this.stoneToChainBuf.subarray(0, gridLen)
        : new Int32Array(gridLen);
    stoneToChainId.fill(-1);

    const qBuf = gridLen <= 361 ? this.queueBuf : new Int32Array(gridLen);
    const chains: BensonChainInfo[] = [];
    const isImmortalChain: boolean[] = [];

    for (let coord = 0; coord < gridLen; coord++) {
      if (pos.grid[coord] === color && !visitedStones[coord]) {
        const cid = chains.length;
        // Fast BFS using qBuf to identify chain stones & whether any stone is in immortalWallSet
        qBuf[0] = coord;
        visitedStones[coord] = 1;
        stoneToChainId[coord] = cid;
        let qHead = 0;
        let qTail = 1;
        let hasImmortal = pos.immortalWallSet.has(coord);

        while (qHead < qTail) {
          const cur = qBuf[qHead++];
          const nbs = pos.orthogonalNeighbors(cur);
          for (let i = 0; i < nbs.length; i++) {
            const nb = nbs[i];
            if (pos.grid[nb] === color && !visitedStones[nb]) {
              visitedStones[nb] = 1;
              stoneToChainId[nb] = cid;
              if (!hasImmortal && pos.immortalWallSet.has(nb)) {
                hasImmortal = true;
              }
              qBuf[qTail++] = nb;
            }
          }
        }

        const stones = new Set<number>();
        const liberties = new Set<number>();
        if (!hasImmortal || includeDiagnostics) {
          for (let i = 0; i < qTail; i++) {
            const s = qBuf[i];
            stones.add(s);
            const nbs = pos.orthogonalNeighbors(s);
            for (let j = 0; j < nbs.length; j++) {
              const nb = nbs[j];
              if (pos.grid[nb] === Color.Empty) {
                liberties.add(nb);
              }
            }
          }
        } else {
          // Immortal wall chains stay permanently active in X_k and never check liberties;
          // retain stones array in Set only if needed for vitalRz/ucaStones readout.
          for (let i = 0; i < qTail; i++) {
            stones.add(qBuf[i]);
          }
        }

        isImmortalChain.push(hasImmortal);
        chains.push({
          chainId: cid,
          color,
          stones,
          liberties,
          vitalRegionIds: [],
          isUcaAlive: false,
        });
      }
    }

    // Partition complement of `color` stones into connected components (regions)
    const visitedComplement =
      gridLen <= 361
        ? this.visitedCompBuf.subarray(0, gridLen)
        : new Uint8Array(gridLen);
    visitedComplement.set(visitedStones);

    const eBuf = gridLen <= 361 ? this.emptyPtsBuf : new Int32Array(gridLen);
    const enBuf = gridLen <= 361 ? this.enemyPtsBuf : new Int32Array(gridLen);
    const bcBuf = gridLen <= 361 ? this.bChainBuf : new Int32Array(gridLen);
    const regions: BensonEyeRegion[] = [];

    for (let coord = 0; coord < gridLen; coord++) {
      if (visitedComplement[coord]) continue;

      this.chainStampCounter = (this.chainStampCounter + 1) >>> 0;
      if (this.chainStampCounter === 0) {
        this.seenChainStamp.fill(0);
        this.chainStampCounter = 1;
      }
      const cStamp = this.chainStampCounter;

      let emptyLen = 0;
      let enemyLen = 0;
      let bcLen = 0;
      let touchesImmortalEnemy = false;
      let touchesTacticalChain = false;

      qBuf[0] = coord;
      visitedComplement[coord] = 1;
      let qHead = 0;
      let qTail = 1;

      while (qHead < qTail) {
        const cur = qBuf[qHead++];
        const st = pos.grid[cur];
        if (st === Color.Empty) {
          eBuf[emptyLen++] = cur;
        } else {
          enBuf[enemyLen++] = cur;
          if (!touchesImmortalEnemy && pos.immortalWallSet.has(cur)) {
            touchesImmortalEnemy = true;
          }
        }

        const nbs = pos.orthogonalNeighbors(cur);
        for (let i = 0; i < nbs.length; i++) {
          const nb = nbs[i];
          if (pos.grid[nb] === color) {
            const cid = stoneToChainId[nb];
            if (cid >= 0 && this.seenChainStamp[cid] !== cStamp) {
              this.seenChainStamp[cid] = cStamp;
              bcBuf[bcLen++] = cid;
              if (!isImmortalChain[cid]) {
                touchesTacticalChain = true;
              }
            }
          } else if (!visitedComplement[nb]) {
            visitedComplement[nb] = 1;
            qBuf[qTail++] = nb;
          }
        }
      }

      // Exclude complement components containing uncapturable enemy boundary walls
      // or isolated pockets inside the outer mask lattice (zero tactical chain contact).
      // No artificial upper cap is placed on `emptyPoints.size` for the Benson fixpoint.
      if (
        !touchesImmortalEnemy &&
        touchesTacticalChain &&
        emptyLen > 0 &&
        bcLen > 0
      ) {
        const emptyPoints = new Set<number>();
        for (let i = 0; i < emptyLen; i++) emptyPoints.add(eBuf[i]);
        const enemyStones = new Set<number>();
        for (let i = 0; i < enemyLen; i++) enemyStones.add(enBuf[i]);
        const boundaryChainIds: number[] = new Array(bcLen);
        for (let i = 0; i < bcLen; i++) boundaryChainIds[i] = bcBuf[i];

        regions.push({
          regionId: regions.length,
          enclosingColor: color,
          emptyPoints,
          enemyStones,
          boundaryChainIds,
          topology: EyeTopologyType.HalfEye,
          vitalPoints: [],
          eyeCountContribution: 0,
        });
      }
    }

    // Classic Benson (1976) greatest-fixpoint elimination loop
    const activeChains = new Set<number>(chains.map((c) => c.chainId));
    const activeRegions = new Set<number>(regions.map((r) => r.regionId));

    let changed = true;
    while (changed) {
      changed = false;

      // 1. A region remains enclosed in X_k iff ALL of its boundary chains remain in X_k
      for (const rid of Array.from(activeRegions)) {
        const reg = regions[rid];
        const allBoundaryActive = reg.boundaryChainIds.every((cid) =>
          activeChains.has(cid)
        );
        if (!allBoundaryActive) {
          activeRegions.delete(rid);
          changed = true;
        }
      }

      // 2. A non-immortal chain remains in X_k iff it has >= 2 distinct vital regions in R_k,
      //    where R is vital to C iff EVERY empty point in R is an orthogonal liberty of C.
      for (const cid of Array.from(activeChains)) {
        if (isImmortalChain[cid]) continue;
        const ch = chains[cid];

        ch.vitalRegionIds = [];
        for (const rid of activeRegions) {
          const reg = regions[rid];
          let allEmptyAdjacent = true;
          for (const pt of reg.emptyPoints) {
            if (!ch.liberties.has(pt)) {
              allEmptyAdjacent = false;
              break;
            }
          }
          if (allEmptyAdjacent) {
            ch.vitalRegionIds.push(rid);
          }
        }

        if (ch.vitalRegionIds.length < 2) {
          activeChains.delete(cid);
          changed = true;
        }
      }
    }

    // Annotate region topologies after fixpoint convergence (only needed for UI inspection)
    if (includeDiagnostics) {
      const vitalRegionSet = new Set<number>();
      for (const cid of activeChains) {
        for (const rid of chains[cid].vitalRegionIds) {
          vitalRegionSet.add(rid);
        }
      }
      for (const reg of regions) {
        const isVital = vitalRegionSet.has(reg.regionId);
        const bChains = reg.boundaryChainIds.map((id) => chains[id]);
        const diagInfo = this.classifyDiagnosticTopology(
          pos,
          reg.emptyPoints,
          reg.enemyStones,
          color,
          bChains,
          isVital
        );
        reg.topology = diagInfo.topology;
        reg.vitalPoints = diagInfo.vitalPoints;
        reg.eyeCountContribution = isVital ? 1 : 0;
      }
    }

    const ucaStones = new Set<number>();
    const vitalRz = new Set<number>();
    for (const cid of activeChains) {
      const ch = chains[cid];
      ch.isUcaAlive = true;
      for (const s of ch.stones) {
        ucaStones.add(s);
        vitalRz.add(s);
      }
      for (const rid of ch.vitalRegionIds) {
        for (const p of regions[rid].emptyPoints) vitalRz.add(p);
        for (const e of regions[rid].enemyStones) vitalRz.add(e);
        for (const bcid of regions[rid].boundaryChainIds) {
          for (const bs of chains[bcid].stones) vitalRz.add(bs);
        }
      }
    }

    return { ucaStones, chains, regions, vitalRz };
  }

  // Purely heuristic shape & semeai potential estimator for df-pn move ordering and initial
  // (pn, dn) bounds. NEVER invoked by `evaluateTerminal` or `ProofArtifactManager`.
  public estimateHeuristicShapePotential(
    pos: GoPosition,
    tokens: TargetToken[]
  ): {
    eyeLikeCount: number;
    minCrucialLiberties: number;
    minAdjacentEnemyLiberties: number;
  } {
    if (tokens.length === 0) {
      return {
        eyeLikeCount: 0,
        minCrucialLiberties: 0,
        minAdjacentEnemyLiberties: 99,
      };
    }
    const targetColor = tokens[0].stoneColor;
    const enemyColor = oppositeColor(targetColor);
    const crucialStones = new Set<number>();
    let minCrucialLiberties = 99;
    let minAdjacentEnemyLiberties = 99;
    const candidateEyePts = new Set<number>();

    tokens.forEach((tok, idx) => {
      if ((pos.survivingTargetTokensMask & (1 << idx)) === 0) return;
      if (pos.stoneAt(tok.initialCoord) !== targetColor) return;
      const ch = pos.floodFillChain(tok.initialCoord);
      if (ch.liberties.size < minCrucialLiberties) {
        minCrucialLiberties = ch.liberties.size;
      }
      for (const s of ch.stones) {
        crucialStones.add(s);
        for (const nb of pos.orthogonalNeighbors(s)) {
          const st = pos.stoneAt(nb);
          if (st === Color.Empty) {
            candidateEyePts.add(nb);
          } else if (st === enemyColor && !pos.immortalWallSet.has(nb)) {
            const ech = pos.floodFillChain(nb);
            if (ech.liberties.size < minAdjacentEnemyLiberties) {
              minAdjacentEnemyLiberties = ech.liberties.size;
            }
          }
        }
      }
    });

    if (minCrucialLiberties === 99) minCrucialLiberties = 0;

    // Count protected tiger's-mouth / eye-like liberties adjacent to crucial chains
    let eyeLikeCount = 0;
    for (const pt of candidateEyePts) {
      const nbs = pos.orthogonalNeighbors(pt);
      let friendlyNbs = 0;
      let enemyNbs = 0;
      for (const nb of nbs) {
        const st = pos.stoneAt(nb);
        if (st === targetColor) friendlyNbs++;
        else if (st === enemyColor) enemyNbs++;
      }
      if (enemyNbs === 0 && friendlyNbs === nbs.length) {
        eyeLikeCount += 2; // Fully surrounded single-point eye candidate
      } else if (enemyNbs === 0 && friendlyNbs >= Math.max(2, nbs.length - 1)) {
        eyeLikeCount += 1; // Protected tiger's mouth
      }
    }

    return {
      eyeLikeCount,
      minCrucialLiberties,
      minAdjacentEnemyLiberties,
    };
  }

  // FR-3.2, FR-3.3, FR-3.8: Unified four-valued terminal evaluation (100% Sound)
  public evaluateTerminal(
    pos: GoPosition,
    context: ProofContext,
    includeDiagnostics = true
  ): TerminalEvalResult {
    const leafRz = new Set<number>();

    if (context.initialTokens.length === 0) {
      return {
        status:
          context.attackerGoal === SearchGoal.ToLive
            ? TerminalStatus.Loss
            : TerminalStatus.Win,
        evidenceKind: 'EMPTY_TARGET_CONSTANT_FALSE',
        leafCertificateRz: leafRz,
        bensonAliveCoords: [],
        eyeTopologyRegions: [],
        diagnosticNote:
          'FR-1.3: Empty crucial_stone expression evaluates to constant false.',
      };
    }

    let maxGroup = 0;
    for (let i = 0; i < context.initialTokens.length; i++) {
      if (context.initialTokens[i].groupIndex > maxGroup) {
        maxGroup = context.initialTokens[i].groupIndex;
      }
    }
    const groupHasSurvivingToken: boolean[] = new Array(maxGroup + 1).fill(
      false
    );
    const groupHasTwoLibToken: boolean[] = new Array(maxGroup + 1).fill(false);

    for (let idx = 0; idx < context.initialTokens.length; idx++) {
      const tok = context.initialTokens[idx];
      const aliveBit = (pos.survivingTargetTokensMask & (1 << idx)) !== 0;
      if (aliveBit && pos.stoneAt(tok.initialCoord) === tok.stoneColor) {
        groupHasSurvivingToken[tok.groupIndex] = true;
        const { stones, liberties } = pos.floodFillChain(tok.initialCoord);
        for (const s of stones) leafRz.add(s);
        for (const l of liberties) leafRz.add(l);
        if (liberties.size >= 2 || pos.immortalWallSet.has(tok.initialCoord)) {
          groupHasTwoLibToken[tok.groupIndex] = true;
        }
      } else {
        leafRz.add(tok.initialCoord);
      }
    }

    const targetAllCaptured =
      context.crucialStoneOp === LogicalOp.Conjunction
        ? groupHasSurvivingToken.some((v) => !v)
        : groupHasSurvivingToken.every((v) => !v);

    // If crucial tokens are already captured (and UI diagnostics not requested),
    // captured stones cannot be in `ucaStones`, so return TOKENS_CAPTURED in O(1)!
    if (targetAllCaptured && !includeDiagnostics) {
      return {
        status:
          context.attackerGoal === SearchGoal.ToLive
            ? TerminalStatus.Loss
            : TerminalStatus.Win,
        evidenceKind: 'TOKENS_CAPTURED',
        leafCertificateRz: leafRz,
        bensonAliveCoords: [],
        eyeTopologyRegions: [],
        diagnosticNote:
          'Crucial target stone tokens captured and permanently removed.',
      };
    }

    // Mathematical precondition for Classic Benson UCA: two disjoint non-empty vital
    // regions require `ch.liberties.size >= 2` (unless anchored to `immortalWallSet`).
    const canSatisfyBenson =
      context.crucialStoneOp === LogicalOp.Conjunction
        ? groupHasTwoLibToken.every(Boolean)
        : groupHasTwoLibToken.some(Boolean);

    let ucaStones = new Set<number>();
    let regions: BensonEyeRegion[] = [];
    let vitalRz = new Set<number>();

    if (canSatisfyBenson || includeDiagnostics) {
      const targetColor = context.initialTokens[0].stoneColor;
      const bensonRes = this.computeBensonUca(
        pos,
        targetColor,
        includeDiagnostics
      );
      ucaStones = bensonRes.ucaStones;
      regions = bensonRes.regions;
      vitalRz = bensonRes.vitalRz;
    }

    const eyeTopologyRegions = includeDiagnostics
      ? regions.map((r) => ({
          regionId: r.regionId,
          coords: Array.from(r.emptyPoints),
          topology: r.topology,
          enclosingColor: r.enclosingColor,
          vitalPoints: r.vitalPoints,
        }))
      : [];

    const groupHasUcaToken: boolean[] = new Array(maxGroup + 1).fill(false);
    if (ucaStones.size > 0) {
      for (let idx = 0; idx < context.initialTokens.length; idx++) {
        const tok = context.initialTokens[idx];
        const aliveBit = (pos.survivingTargetTokensMask & (1 << idx)) !== 0;
        if (
          aliveBit &&
          pos.stoneAt(tok.initialCoord) === tok.stoneColor &&
          ucaStones.has(tok.initialCoord)
        ) {
          groupHasUcaToken[tok.groupIndex] = true;
        }
      }
    }

    const targetUcaSatisfied =
      context.crucialStoneOp === LogicalOp.Conjunction
        ? groupHasUcaToken.every(Boolean)
        : groupHasUcaToken.some(Boolean);

    // 1. Target stones achieved Classic Benson UCA
    if (targetUcaSatisfied) {
      for (const p of vitalRz) leafRz.add(p);
      return {
        status:
          context.attackerGoal === SearchGoal.ToLive
            ? TerminalStatus.Win
            : TerminalStatus.Loss,
        evidenceKind: 'BENSON_UCA',
        leafCertificateRz: leafRz,
        bensonAliveCoords: includeDiagnostics ? Array.from(ucaStones) : [],
        eyeTopologyRegions,
        diagnosticNote:
          'Classic Benson (1976) UCA greatest-fixpoint satisfied (>= 2 vital enclosed regions).',
      };
    }

    // 2. Target tokens irreversibly captured (FR-2.6, FR-3.2)
    if (targetAllCaptured) {
      return {
        status:
          context.attackerGoal === SearchGoal.ToLive
            ? TerminalStatus.Loss
            : TerminalStatus.Win,
        evidenceKind: 'TOKENS_CAPTURED',
        leafCertificateRz: leafRz,
        bensonAliveCoords: includeDiagnostics ? Array.from(ucaStones) : [],
        eyeTopologyRegions,
        diagnosticNote:
          'Crucial target stone tokens captured and permanently removed.',
      };
    }

    // 3. FR-3.8 Double-pass resolution (strictly evaluated before InPath cycle detection)
    if (pos.isAtDoublePass()) {
      const liveHolds = targetUcaSatisfied;
      const isWin =
        context.attackerGoal === SearchGoal.ToLive ? liveHolds : !liveHolds;
      return {
        status: isWin ? TerminalStatus.Win : TerminalStatus.Loss,
        evidenceKind: 'DOUBLE_PASS_RESOLUTION',
        leafCertificateRz: leafRz,
        bensonAliveCoords: includeDiagnostics ? Array.from(ucaStones) : [],
        eyeTopologyRegions,
        diagnosticNote:
          'Double-pass terminal resolution evaluated prior to InPath cycle check.',
      };
    }

    return {
      status: TerminalStatus.NonTerminal,
      evidenceKind: 'NONE',
      leafCertificateRz: leafRz,
      bensonAliveCoords: includeDiagnostics ? Array.from(ucaStones) : [],
      eyeTopologyRegions,
      diagnosticNote: 'Non-terminal state; search continues.',
    };
  }
}
