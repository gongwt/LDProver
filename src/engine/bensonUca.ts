// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/terminal/benson_uca.cc (FR-3.1..FR-3.9).
//
// Soundness Invariant (NFR-1):
// `computeBensonUca` and `evaluateTerminal` implement strictly pure Classic Benson
// (David B. Benson, "Life in the Game of Go", Information Sciences 10, 1976):
//   1. Chains are strictly raw orthogonally-connected stone components (no super-chain
//      merging across shared liberties or tiger's mouths).
//   2. Enclosed regions of complement(color) cannot contain any uncapturable outer
//      boundary wall stones (`immortalWallSet`).
//   3. A region R is vital to chain C in active set X_k iff every boundary chain of R
//      belongs to X_k AND every empty intersection of R is a liberty of C.
//   4. Each vital region contributes strictly 1 towards Benson's >= 2 vital-region
//      fixpoint threshold (never 2 eyes from a single multi-point cavity).
//
// Eye-shape topology classification (`classifyEyeRegionTopology`) and heuristic eye
// potential estimation (`estimateHeuristicEyePotential`) are strictly separated from
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

  // FR-3.1: Strictly Pure Classic Benson (1976) Unconditional Alive (UCA) greatest-fixpoint solver
  public computeBensonUca(
    pos: GoPosition,
    color: Color
  ): {
    ucaStones: Set<number>;
    chains: BensonChainInfo[];
    regions: BensonEyeRegion[];
    vitalRz: Set<number>;
  } {
    const chains: BensonChainInfo[] = [];
    const visitedStones = new Uint8Array(pos.grid.length);
    const stoneToChainId = new Int32Array(pos.grid.length).fill(-1);
    const isImmortalChain: boolean[] = [];

    for (let coord = 0; coord < pos.grid.length; coord++) {
      if (pos.grid[coord] === color && !visitedStones[coord]) {
        const { stones, liberties } = pos.floodFillChain(coord);
        const cid = chains.length;
        let hasImmortal = false;
        for (const s of stones) {
          visitedStones[s] = 1;
          stoneToChainId[s] = cid;
          if (!hasImmortal && pos.immortalWallSet.has(s)) {
            hasImmortal = true;
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
    const visitedComplement = new Uint8Array(visitedStones);

    const regions: BensonEyeRegion[] = [];

    for (let coord = 0; coord < pos.grid.length; coord++) {
      if (visitedComplement[coord]) continue;

      const emptyPoints = new Set<number>();
      const enemyStones = new Set<number>();
      const boundaryChainSet = new Set<number>();
      let touchesImmortalEnemy = false;

      const queue: number[] = [coord];
      visitedComplement[coord] = 1;

      while (queue.length > 0) {
        const cur = queue.pop()!;
        const st = pos.stoneAt(cur);
        if (st === Color.Empty) {
          emptyPoints.add(cur);
        } else {
          enemyStones.add(cur);
          if (pos.immortalWallSet.has(cur)) {
            touchesImmortalEnemy = true;
          }
        }

        for (const nb of pos.orthogonalNeighbors(cur)) {
          if (pos.stoneAt(nb) === color) {
            const cid = stoneToChainId[nb];
            if (cid >= 0) boundaryChainSet.add(cid);
          } else if (!visitedComplement[nb]) {
            visitedComplement[nb] = 1;
            queue.push(nb);
          }
        }
      }

      const touchesTacticalChain = Array.from(boundaryChainSet).some(
        (cid) => !isImmortalChain[cid]
      );

      // Exclude outer board / uncapturable wall components and pure mask-lattice pockets
      if (
        !touchesImmortalEnemy &&
        touchesTacticalChain &&
        emptyPoints.size > 0 &&
        emptyPoints.size <= 15 &&
        boundaryChainSet.size > 0
      ) {
        regions.push({
          regionId: regions.length,
          enclosingColor: color,
          emptyPoints,
          enemyStones,
          boundaryChainIds: Array.from(boundaryChainSet),
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
        const ch = chains[cid];
        const isImmortalWall = Array.from(ch.stones).some((s) =>
          pos.immortalWallSet.has(s)
        );
        if (isImmortalWall) continue;

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

    // Annotate region topologies after fixpoint convergence (for UI and heuristic inspection)
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
    context: ProofContext
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

    const targetColor = context.initialTokens[0].stoneColor;
    const { ucaStones, regions, vitalRz } = this.computeBensonUca(
      pos,
      targetColor
    );

    const eyeTopologyRegions = regions.map((r) => ({
      regionId: r.regionId,
      coords: Array.from(r.emptyPoints),
      topology: r.topology,
      enclosingColor: r.enclosingColor,
      vitalPoints: r.vitalPoints,
    }));

    const maxGroup = Math.max(
      ...context.initialTokens.map((t) => t.groupIndex),
      0
    );
    const groupHasSurvivingToken: boolean[] = new Array(maxGroup + 1).fill(
      false
    );
    const groupHasUcaToken: boolean[] = new Array(maxGroup + 1).fill(false);

    context.initialTokens.forEach((tok, idx) => {
      const aliveBit = (pos.survivingTargetTokensMask & (1 << idx)) !== 0;
      if (aliveBit && pos.stoneAt(tok.initialCoord) === tok.stoneColor) {
        groupHasSurvivingToken[tok.groupIndex] = true;
        const { stones, liberties } = pos.floodFillChain(tok.initialCoord);
        for (const s of stones) leafRz.add(s);
        for (const l of liberties) leafRz.add(l);
        if (ucaStones.has(tok.initialCoord)) {
          groupHasUcaToken[tok.groupIndex] = true;
        }
      } else {
        leafRz.add(tok.initialCoord);
      }
    });

    let targetUcaSatisfied = false;
    let targetAllCaptured = false;

    if (context.crucialStoneOp === LogicalOp.Conjunction) {
      targetUcaSatisfied = groupHasUcaToken.every(Boolean);
      targetAllCaptured = groupHasSurvivingToken.some((v) => !v);
    } else {
      targetUcaSatisfied = groupHasUcaToken.some(Boolean);
      targetAllCaptured = groupHasSurvivingToken.every((v) => !v);
    }

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
        bensonAliveCoords: Array.from(ucaStones),
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
        bensonAliveCoords: Array.from(ucaStones),
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
        bensonAliveCoords: Array.from(ucaStones),
        eyeTopologyRegions,
        diagnosticNote:
          'Double-pass terminal resolution evaluated prior to InPath cycle check.',
      };
    }

    return {
      status: TerminalStatus.NonTerminal,
      evidenceKind: 'NONE',
      leafCertificateRz: leafRz,
      bensonAliveCoords: Array.from(ucaStones),
      eyeTopologyRegions,
      diagnosticNote: 'Non-terminal state; search continues.',
    };
  }
}
