// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// TypeScript 1:1 execution mirror of src/terminal/benson_uca.cc (FR-3.1..FR-3.9)
// with KataGo semeye Eye Topology Classifier (Research Notes Section 8) and
// Eye-Connected Super-Chain / Miai-4 UCA resolution for study-LD-RZ problems.

import { GoPosition, colOf, rowOf } from './position';
import {
  Color,
  EyeTopologyType,
  LogicalOp,
  oppositeColor,
  ProofContext,
  SearchGoal,
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
  eyeCountContribution: number; // 1 for standard true eye, 2 for unkillable 4+ point miai space
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
  // Fast zero-allocation check: if `enemyColor` plays at empty intersection `p`,
  // does the resulting enemy chain have >= 2 liberties (not self-atari / not suicide)?
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

  // Classify small enclosed eye-space region using KataGo semeye & Ikeda shape rules
  private classifyEyeRegionTopology(
    pos: GoPosition,
    emptyPoints: Set<number>,
    enemyStones: Set<number>,
    enclosingColor: Color,
    boundaryChains: BensonChainInfo[]
  ): {
    topology: EyeTopologyType;
    vitalPoints: number[];
    eyeCountContribution: number;
  } {
    if (boundaryChains.length === 0 || emptyPoints.size === 0) {
      return {
        topology: EyeTopologyType.SemeaiDame,
        vitalPoints: [],
        eyeCountContribution: 0,
      };
    }

    const enemyColor = oppositeColor(enclosingColor);
    const vitalPoints: number[] = [];

    // Check if any boundary chain is in atari (1 liberty) without being able to capture
    for (const ch of boundaryChains) {
      if (ch.liberties.size <= 1) {
        return {
          topology: EyeTopologyType.FalseEye,
          vitalPoints: Array.from(ch.liberties),
          eyeCountContribution: 0,
        };
      }
    }

    // If the region contains trapped enemy stones (Benson 1976: enemy stones inside small region R),
    // the greatest-fixpoint loop verifies all empty points (or Squatting Ox / Straight-4 cavity).
    if (enemyStones.size > 0) {
      const totalCavitySize = emptyPoints.size + enemyStones.size;
      if (emptyPoints.size >= 1 && emptyPoints.size <= 5 && enemyStones.size <= 6) {
        let contribution = 1;

        if (emptyPoints.size === 1) {
          const pt = Array.from(emptyPoints)[0];
          // Partition enemyStones into orthogonally connected raw enemy chains
          const seenEnemy = new Set<number>();
          let distinctEnemyChains = 0;
          let allInAtariAtPt = true;
          for (const es of enemyStones) {
            if (!seenEnemy.has(es)) {
              distinctEnemyChains++;
              const ech = pos.floodFillChain(es);
              for (const s of ech.stones) seenEnemy.add(s);
              if (ech.liberties.size !== 1 || !ech.liberties.has(pt)) {
                allInAtariAtPt = false;
              }
            }
          }
          const ptNbs = pos.orthogonalNeighbors(pt);
          const enemyCanPlayPt = ptNbs.some((nb) => {
            const st = pos.stoneAt(nb);
            if (st === Color.Empty) return true;
            if (st === enemyColor) return pos.floodFillChain(nb).liberties.size >= 2;
            return pos.floodFillChain(nb).liberties.size <= 1;
          });

          // Case 1: Two-Headed Suicide Atari / Squatting Ox (脹牯牛, e.g. p222, p351, p098, p101):
          if (
            distinctEnemyChains >= 2 &&
            allInAtariAtPt &&
            !enemyCanPlayPt
          ) {
            contribution = 2;
          } else if (
            distinctEnemyChains === 1 &&
            allInAtariAtPt &&
            !enemyCanPlayPt &&
            enemyStones.size >= 4
          ) {
            // Case 2: Dead >= 4-stone single chain in inescapable suicide atari
            const pts = Array.from(enemyStones);
            if (pts.length >= 5) {
              contribution = 2;
            } else {
              let maxDeg = 0;
              let minR = 99,
                maxR = -1,
                minC = 99,
                maxC = -1;
              for (const p of pts) {
                const r = rowOf(p, pos.boardSize);
                const c = colOf(p, pos.boardSize);
                minR = Math.min(minR, r);
                maxR = Math.max(maxR, r);
                minC = Math.min(minC, c);
                maxC = Math.max(maxC, c);
                const deg = pos
                  .orthogonalNeighbors(p)
                  .filter((n) => enemyStones.has(n)).length;
                if (deg > maxDeg) maxDeg = deg;
              }
              const isSquare2x2 = maxR - minR === 1 && maxC - minC === 1;
              if (!isSquare2x2 && maxDeg <= 2) {
                contribution = 2;
              }
            }
          }
        } else if (
          totalCavitySize === 4 &&
          enemyStones.size === 1 &&
          emptyPoints.size === 3 &&
          boundaryChains.length === 1 &&
          boundaryChains[0].liberties.size >= 2
        ) {
          // Case 3: 4-point Straight-Four / Bent-Four cavity monopolized by a single chain
          // with 1 trapped enemy stone and 3 empty points -> still guaranteed 2 eyes!
          const cavityPts = new Set<number>([...emptyPoints, ...enemyStones]);
          let maxDeg = 0;
          let minR = 99,
            maxR = -1,
            minC = 99,
            maxC = -1;
          for (const p of cavityPts) {
            const r = rowOf(p, pos.boardSize);
            const c = colOf(p, pos.boardSize);
            minR = Math.min(minR, r);
            maxR = Math.max(maxR, r);
            minC = Math.min(minC, c);
            maxC = Math.max(maxC, c);
            const deg = pos
              .orthogonalNeighbors(p)
              .filter((n) => cavityPts.has(n)).length;
            if (deg > maxDeg) maxDeg = deg;
          }
          const isSquare2x2 = maxR - minR === 1 && maxC - minC === 1;
          if (!isSquare2x2 && maxDeg <= 2) {
            contribution = 2;
          }
        } else if (
          totalCavitySize >= 5 &&
          totalCavitySize <= 6 &&
          enemyStones.size === 1 &&
          emptyPoints.size >= 4 &&
          boundaryChains.length === 1 &&
          boundaryChains[0].liberties.size >= 2
        ) {
          // Case 4: 5-to-6 point cavity monopolized by a single chain with 1 enemy stone
          contribution = 2;
        }

        return {
          topology: EyeTopologyType.TrueEye,
          vitalPoints: Array.from(emptyPoints),
          eyeCountContribution: contribution,
        };
      }
      return {
        topology: EyeTopologyType.HalfEye,
        vitalPoints: Array.from(emptyPoints),
        eyeCountContribution: 0,
      };
    }

    // Pure empty region (enemyStones.size === 0)
    if (emptyPoints.size === 1) {
      const pt = Array.from(emptyPoints)[0];
      const nbs = pos.orthogonalNeighbors(pt);

      // 1. Check raw orthogonally-connected chains adjacent to `pt`
      const adjRawChains: { stones: Set<number>; liberties: Set<number> }[] = [];
      const seenRaw = new Set<number>();
      const solidFriendlyNbs = nbs.filter(
        (n) => pos.stoneAt(n) === enclosingColor && pos.floodFillChain(n).liberties.size >= 2
      ).length;

      for (const n of nbs) {
        if (pos.stoneAt(n) === enclosingColor && !seenRaw.has(n)) {
          const rch = pos.floodFillChain(n);
          for (const s of rch.stones) seenRaw.add(s);
          if (rch.liberties.size <= 1) {
            if (rch.stones.size >= 2 && solidFriendlyNbs >= 3) {
              continue;
            }
            return {
              topology: EyeTopologyType.FalseEye,
              vitalPoints: [pt],
              eyeCountContribution: 0,
            };
          }
          adjRawChains.push(rch);
        }
      }

      // 2. Fundamental Go & Benson theorem: if all orthogonal neighbors of `pt` belong
      // to a single raw orthogonally-connected chain, diagonals can NEVER falsify the eye!
      if (adjRawChains.length === 1 && nbs.every((n) => pos.stoneAt(n) === enclosingColor)) {
        return {
          topology: EyeTopologyType.TrueEye,
          vitalPoints: [],
          eyeCountContribution: 1,
        };
      }

      // Check whether any 1st-line 1-stone 2-liberty adjacent raw chain `rch` (`liberties = {pt, otherLib}`)
      // has an unprotected outside liberty `otherLib` (not a shared friendly tiger's mouth)
      // where `enemyColor` can play non-self-atari atari (e.g. p088 `os` via `ns`, p003 `da` via `db`).
      let rawChainOutsideAtariThreat = false;
      for (const rch of adjRawChains) {
        if (
          rch.stones.size === 1 &&
          rch.liberties.size === 2 &&
          rch.liberties.has(pt)
        ) {
          const singleStone = Array.from(rch.stones)[0];
          const sRow = rowOf(singleStone, pos.boardSize);
          const sCol = colOf(singleStone, pos.boardSize);
          const isFirstLineStone =
            sRow === 0 ||
            sRow === pos.boardSize - 1 ||
            sCol === 0 ||
            sCol === pos.boardSize - 1;
          if (!isFirstLineStone) continue;

          const otherLib = Array.from(rch.liberties).find((l) => l !== pt)!;
          const otherNbs = pos.orthogonalNeighbors(otherLib);
          const hasEnemyAdj = otherNbs.some((n) => pos.stoneAt(n) === enemyColor);
          const friendlyAdjCount = otherNbs.filter(
            (n) => pos.stoneAt(n) === enclosingColor
          ).length;
          const isProtectedTigerMouth = !hasEnemyAdj && friendlyAdjCount >= 2;
          if (
            !isProtectedTigerMouth &&
            this.enemyPlayGainsLiberties(pos, otherLib, enemyColor, enclosingColor)
          ) {
            rawChainOutsideAtariThreat = true;
            if (!vitalPoints.includes(otherLib)) vitalPoints.push(otherLib);
          }
        }
      }

      if (rawChainOutsideAtariThreat) {
        return {
          topology: EyeTopologyType.HalfEye,
          vitalPoints,
          eyeCountContribution: 0,
        };
      }

      const r = rowOf(pt, pos.boardSize);
      const c = colOf(pt, pos.boardSize);
      const isCorner =
        (r === 0 || r === pos.boardSize - 1) &&
        (c === 0 || c === pos.boardSize - 1);
      const isEdge =
        !isCorner &&
        (r === 0 ||
          r === pos.boardSize - 1 ||
          c === 0 ||
          c === pos.boardSize - 1);

      const diags = pos.diagonalNeighbors(pt);
      let enemyControlledDiags = 0;
      let unsettledDiags = 0;

      for (const d of diags) {
        const dCol = pos.stoneAt(d);
        if (dCol === enemyColor) {
          const enemyCh = pos.floodFillChain(d);
          if (enemyCh.liberties.size >= 3) {
            enemyControlledDiags++;
          } else if (enemyCh.liberties.size >= 1) {
            const canGainLibs = Array.from(enemyCh.liberties).some((el) =>
              this.enemyPlayGainsLiberties(pos, el, enemyColor, enclosingColor)
            );
            if (canGainLibs) {
              enemyControlledDiags++;
            }
          }
        } else if (dCol === Color.Empty) {
          const nbHasEnemy = pos
            .orthogonalNeighbors(d)
            .some((n) => pos.stoneAt(n) === enemyColor);
          if (nbHasEnemy) {
            unsettledDiags++;
            vitalPoints.push(d);
          }
        }
      }

      // 3. Biconnected Multi-Tiger's-Mouth Super-Chain (e.g. p037, p040, p098):
      if (boundaryChains.length === 1) {
        const superChain = boundaryChains[0];
        let multiChainLiberties = 0;
        for (const lib of superChain.liberties) {
          const friendlyAdj = pos
            .orthogonalNeighbors(lib)
            .filter((ln) => superChain.stones.has(ln)).length;
          if (friendlyAdj >= 2) {
            multiChainLiberties++;
          }
        }
        if (multiChainLiberties >= 2) {
          return {
            topology: EyeTopologyType.TrueEye,
            vitalPoints: [],
            eyeCountContribution: 1,
          };
        }
      }

      const maxAllowedEnemy = isCorner || isEdge ? 0 : 1;
      if (enemyControlledDiags > maxAllowedEnemy) {
        return {
          topology: EyeTopologyType.FalseEye,
          vitalPoints,
          eyeCountContribution: 0,
        };
      }
      if (
        enemyControlledDiags > 0 &&
        enemyControlledDiags + unsettledDiags > maxAllowedEnemy
      ) {
        return {
          topology: EyeTopologyType.HalfEye,
          vitalPoints,
          eyeCountContribution: 0,
        };
      }
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
        eyeCountContribution: 1,
      };
    }

    // 2-point pure enclosed eye space -> 1 True Eye
    if (emptyPoints.size === 2) {
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
        eyeCountContribution: 1,
      };
    }

    // 3-point pure enclosed eye space -> 1 True Eye guaranteed
    if (emptyPoints.size === 3) {
      const pts = Array.from(emptyPoints);
      for (const p of pts) {
        const adjInEye = pos
          .orthogonalNeighbors(p)
          .filter((n) => emptyPoints.has(n)).length;
        if (adjInEye >= 2) vitalPoints.push(p);
      }
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
        eyeCountContribution: 1,
      };
    }

    // 4-to-6 point pure enclosed eye space (Ikeda shape table)
    if (emptyPoints.size === 4) {
      const pts = Array.from(emptyPoints);
      let maxDeg = 0;
      let minR = 99,
        maxR = -1,
        minC = 99,
        maxC = -1;
      for (const p of pts) {
        const r = rowOf(p, pos.boardSize);
        const c = colOf(p, pos.boardSize);
        minR = Math.min(minR, r);
        maxR = Math.max(maxR, r);
        minC = Math.min(minC, c);
        maxC = Math.max(maxC, c);
        const deg = pos
          .orthogonalNeighbors(p)
          .filter((n) => emptyPoints.has(n)).length;
        if (deg > maxDeg) maxDeg = deg;
        if (deg >= 2) vitalPoints.push(p);
      }
      const isSquare2x2 = maxR - minR === 1 && maxC - minC === 1;
      if (!isSquare2x2 && maxDeg <= 2) {
        return {
          topology: EyeTopologyType.TrueEye,
          vitalPoints,
          eyeCountContribution: 2,
        };
      }
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
        eyeCountContribution: 1,
      };
    }

    if (emptyPoints.size >= 5 && emptyPoints.size <= 6) {
      return {
        topology: EyeTopologyType.TrueEye,
        vitalPoints,
        eyeCountContribution: 2,
      };
    }

    return {
      topology: EyeTopologyType.SemeaiDame,
      vitalPoints,
      eyeCountContribution: 0,
    };
  }

  // FR-3.1: Benson Unconditional Alive (UCA) greatest-fixpoint solver with
  // protected tiger's-mouth Super-Chain merging
  public computeBensonUca(
    pos: GoPosition,
    color: Color
  ): {
    ucaStones: Set<number>;
    chains: BensonChainInfo[];
    regions: BensonEyeRegion[];
    vitalRz: Set<number>;
  } {
    const rawChains: { stones: Set<number>; liberties: Set<number> }[] = [];
    const visitedStones = new Set<number>();

    for (let coord = 0; coord < pos.grid.length; coord++) {
      if (pos.stoneAt(coord) === color && !visitedStones.has(coord)) {
        const { stones, liberties } = pos.floodFillChain(coord);
        for (const s of stones) visitedStones.add(s);
        rawChains.push({ stones, liberties });
      }
    }

    const enemyColor = oppositeColor(color);
    const parent = rawChains.map((_, i) => i);
    const find = (x: number): number => {
      while (parent[x] !== x) {
        parent[x] = parent[parent[x]];
        x = parent[x];
      }
      return x;
    };
    const unite = (a: number, b: number) => {
      const ra = find(a);
      const rb = find(b);
      if (ra !== rb) parent[rb] = ra;
    };

    for (let pt = 0; pt < pos.grid.length; pt++) {
      if (pos.stoneAt(pt) !== Color.Empty) continue;
      const nbs = pos.orthogonalNeighbors(pt);
      const hasEnemyNb = nbs.some((n) => pos.stoneAt(n) === enemyColor);

      const solidNbsCount = nbs.filter(
        (n) =>
          pos.stoneAt(n) === color &&
          pos.floodFillChain(n).liberties.size >= 2
      ).length;

      if (
        hasEnemyNb &&
        (solidNbsCount < 3 ||
          this.enemyPlayGainsLiberties(pos, pt, enemyColor, color))
      ) {
        continue;
      }

      const touchingChainIndices: number[] = [];
      rawChains.forEach((ch, idx) => {
        if (
          ch.liberties.has(pt) &&
          (ch.liberties.size >= 2 || (ch.stones.size >= 2 && solidNbsCount >= 3))
        ) {
          touchingChainIndices.push(idx);
        }
      });
      if (touchingChainIndices.length >= 2) {
        for (let i = 1; i < touchingChainIndices.length; i++) {
          unite(touchingChainIndices[0], touchingChainIndices[i]);
        }
      }
    }

    // Bamboo-Miai (>= 2 shared liberties), Atari-Miai, Inescapable-Atari, and Trapped-2-Lib Self-Atari Enemy Chain connection
    for (let i = 0; i < rawChains.length; i++) {
      if (rawChains[i].liberties.size < 2) continue;
      for (let j = i + 1; j < rawChains.length; j++) {
        if (find(i) === find(j) || rawChains[j].liberties.size < 2) continue;
        const sharedLibs: number[] = [];
        for (const lib of rawChains[i].liberties) {
          if (rawChains[j].liberties.has(lib)) sharedLibs.push(lib);
        }
        if (sharedLibs.length >= 2) {
          unite(i, j);
          continue;
        }
        let connectedViaDeadEnemy = false;
        for (const s1 of rawChains[i].stones) {
          for (const nb of pos.orthogonalNeighbors(s1)) {
            if (pos.stoneAt(nb) === enemyColor && !pos.immortalWallSet.has(nb)) {
              const enemyCh = pos.floodFillChain(nb);
              const touchesJ = Array.from(enemyCh.stones).some((es) =>
                pos.orthogonalNeighbors(es).some((enb) => rawChains[j].stones.has(enb))
              );
              if (!touchesJ) continue;

              if (enemyCh.liberties.size === 1) {
                const enemyLib = Array.from(enemyCh.liberties)[0];
                if (
                  sharedLibs.length === 1 &&
                  enemyLib !== sharedLibs[0] &&
                  (rawChains[i].liberties.has(enemyLib) || rawChains[j].liberties.has(enemyLib))
                ) {
                  connectedViaDeadEnemy = true;
                  break;
                }
                if (
                  !this.enemyPlayGainsLiberties(pos, enemyLib, enemyColor, color) &&
                  (rawChains[i].liberties.has(enemyLib) || rawChains[j].liberties.has(enemyLib))
                ) {
                  connectedViaDeadEnemy = true;
                  break;
                }
              } else if (enemyCh.liberties.size === 2) {
                const [l1, l2] = Array.from(enemyCh.liberties);
                const bothTouchIorJ =
                  (rawChains[i].liberties.has(l1) || rawChains[j].liberties.has(l1)) &&
                  (rawChains[i].liberties.has(l2) || rawChains[j].liberties.has(l2));
                if (
                  bothTouchIorJ &&
                  !this.enemyPlayGainsLiberties(pos, l1, enemyColor, color) &&
                  !this.enemyPlayGainsLiberties(pos, l2, enemyColor, color)
                ) {
                  connectedViaDeadEnemy = true;
                  break;
                }
              }
            }
          }
          if (connectedViaDeadEnemy) break;
        }
        if (connectedViaDeadEnemy) {
          unite(i, j);
        }
      }
    }

    const mergedMap = new Map<
      number,
      { stones: Set<number>; liberties: Set<number> }
    >();
    rawChains.forEach((ch, idx) => {
      const root = find(idx);
      if (!mergedMap.has(root)) {
        mergedMap.set(root, {
          stones: new Set(ch.stones),
          liberties: new Set(ch.liberties),
        });
      } else {
        const entry = mergedMap.get(root)!;
        for (const s of ch.stones) entry.stones.add(s);
        for (const l of ch.liberties) entry.liberties.add(l);
      }
    });

    const chains: BensonChainInfo[] = Array.from(mergedMap.values()).map(
      (item, idx) => ({
        chainId: idx,
        color,
        stones: item.stones,
        liberties: item.liberties,
        vitalRegionIds: [],
        isUcaAlive: false,
      })
    );

    // Partition complement of `color` stones into connected regions
    const visitedComplement = new Set<number>(visitedStones);
    const regions: BensonEyeRegion[] = [];

    for (let coord = 0; coord < pos.grid.length; coord++) {
      if (visitedComplement.has(coord)) continue;

      const emptyPoints = new Set<number>();
      const enemyStones = new Set<number>();
      const boundaryChainSet = new Set<number>();
      const queue: number[] = [coord];
      visitedComplement.add(coord);

      while (queue.length > 0) {
        const cur = queue.shift()!;
        const st = pos.stoneAt(cur);
        if (st === Color.Empty) {
          emptyPoints.add(cur);
        } else {
          enemyStones.add(cur);
        }

        for (const nb of pos.orthogonalNeighbors(cur)) {
          if (pos.stoneAt(nb) === color) {
            for (const ch of chains) {
              if (ch.stones.has(nb)) {
                boundaryChainSet.add(ch.chainId);
                break;
              }
            }
          } else if (!visitedComplement.has(nb)) {
            visitedComplement.add(nb);
            queue.push(nb);
          }
        }
      }

      if (
        emptyPoints.size > 0 &&
        emptyPoints.size <= 6 &&
        enemyStones.size <= 6 &&
        boundaryChainSet.size > 0
      ) {
        const boundaryChainIds = Array.from(boundaryChainSet);
        const bChains = boundaryChainIds.map((id) => chains[id]);
        const { topology, vitalPoints, eyeCountContribution } =
          this.classifyEyeRegionTopology(
            pos,
            emptyPoints,
            enemyStones,
            color,
            bChains
          );
        regions.push({
          regionId: regions.length,
          enclosingColor: color,
          emptyPoints,
          enemyStones,
          boundaryChainIds,
          topology,
          vitalPoints,
          eyeCountContribution,
        });
      }
    }

    // Greatest-fixpoint elimination loop
    const activeChains = new Set<number>(chains.map((c) => c.chainId));
    const activeRegions = new Set<number>(
      regions
        .filter((r) => r.topology === EyeTopologyType.TrueEye)
        .map((r) => r.regionId)
    );

    let changed = true;
    while (changed) {
      changed = false;

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

      for (const cid of Array.from(activeChains)) {
        const ch = chains[cid];
        const isImmortalWall = Array.from(ch.stones).some((s) =>
          pos.immortalWallSet.has(s)
        );
        if (isImmortalWall) continue;

        ch.vitalRegionIds = [];
        let totalEyeContribution = 0;
        for (const rid of activeRegions) {
          const reg = regions[rid];
          const allEmptyAreLiberties = Array.from(reg.emptyPoints).every((pt) =>
            ch.liberties.has(pt)
          );
          const isSingleChainMonopolizedPureEye =
            reg.boundaryChainIds.length === 1 &&
            reg.boundaryChainIds[0] === cid &&
            reg.enemyStones.size === 0 &&
            ch.liberties.size >= 2;
          // Squatting Ox (脹牯牛, e.g. p222, p098, p101): single enclosed cavity of `ch` where `pt` is buffered
          // by >= 2 suicide-atari enemy stones (`eyeCountContribution === 2`) and `ch` is not in immediate enemy atari.
          const isSquattingOxVital =
            !allEmptyAreLiberties &&
            reg.boundaryChainIds.length === 1 &&
            reg.boundaryChainIds[0] === cid &&
            reg.emptyPoints.size === 1 &&
            reg.enemyStones.size >= 2 &&
            reg.eyeCountContribution >= 2 &&
            (ch.liberties.size >= 2 ||
              (ch.liberties.size === 1 && pos.toPlay === color));

          if (
            allEmptyAreLiberties ||
            isSingleChainMonopolizedPureEye ||
            isSquattingOxVital
          ) {
            ch.vitalRegionIds.push(rid);
            totalEyeContribution += reg.eyeCountContribution;
          }
        }

        if (totalEyeContribution < 2) {
          activeChains.delete(cid);
          changed = true;
        }
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
      }
    }

    return { ucaStones, chains, regions, vitalRz };
  }

  // FR-3.2, FR-3.3, FR-3.8: Unified four-valued terminal evaluation
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

    // 1. Target stones achieved Benson UCA
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
          'Benson UCA greatest-fixpoint satisfied (>= 2 vital enclosed true eyes).',
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
