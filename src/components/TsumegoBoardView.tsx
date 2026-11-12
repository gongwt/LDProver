// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

import React from 'react';
import {
  colOf,
  coordFromRowCol,
  coordToHumanLabel,
  coordToSgf,
  GoPosition,
  PASS_MOVE,
  rowOf,
} from '../engine/position';
import {
  Color,
  EyeTopologyType,
  ProofContext,
  SolveReport,
} from '../engine/types';

interface TsumegoBoardViewProps {
  position: GoPosition;
  context: ProofContext;
  report: SolveReport;
  viewportRows: [number, number];
  viewportCols: [number, number];
  showFullBoard: boolean;
  overlayMode: 'proof-rz' | 'disproof-rz' | 'benson-uca' | 'none';
  selectedPvStepIndex: number | null;
  onPlayCoord: (coord: number) => void;
}

const GO_COL_LETTERS = 'ABCDEFGHJKLMNOPQRST';

export const TsumegoBoardView: React.FC<TsumegoBoardViewProps> = ({
  position,
  context,
  report,
  viewportRows,
  viewportCols,
  showFullBoard,
  overlayMode,
  selectedPvStepIndex,
  onPlayCoord,
}) => {
  const minR = showFullBoard ? 0 : viewportRows[0];
  const maxR = showFullBoard ? 18 : viewportRows[1];
  const minC = showFullBoard ? 0 : viewportCols[0];
  const maxC = showFullBoard ? 18 : viewportCols[1];

  const numRows = maxR - minR + 1;
  const numCols = maxC - minC + 1;
  const cellSize = showFullBoard ? 28 : 48;
  const pad = showFullBoard ? 34 : 44;

  const width = pad * 2 + (numCols - 1) * cellSize;
  const height = pad * 2 + (numRows - 1) * cellSize;

  const proofRzSet = new Set(report.rootProofRzCoords);
  const disproofRzSet = new Set(report.rootDisproofRzCoords);
  const bensonAliveSet = new Set(report.bensonAliveCoords);
  const crucialCoords = new Set(
    context.initialTokens.map((t) => t.initialCoord)
  );

  // Pruned moves at root child nodes
  const prunedMovesSet = new Set<number>();
  for (const n of report.proofDagNodes) {
    if (n.isPrunedOutsideRz && n.incomingMove >= 0) {
      prunedMovesSet.add(n.incomingMove);
    }
  }

  // Eye topology lookup
  const eyeMap = new Map<number, EyeTopologyType>();
  for (const reg of report.eyeTopologyRegions) {
    for (const c of reg.coords) {
      eyeMap.set(c, reg.topology);
    }
  }

  // PV move numbers up to selectedPvStepIndex
  const pvMoveMap = new Map<number, { stepNum: number; color: Color }>();
  const maxStep =
    selectedPvStepIndex !== null
      ? selectedPvStepIndex
      : report.principalVariation.length - 1;
  for (
    let i = 0;
    i <= maxStep && i < report.principalVariation.length;
    i++
  ) {
    const step = report.principalVariation[i];
    if (step.move >= 0) {
      pvMoveMap.set(step.move, { stepNum: i + 1, color: step.color });
    }
  }

  const hoshiPoints = new Set([
    coordFromRowCol(3, 3),
    coordFromRowCol(3, 9),
    coordFromRowCol(3, 15),
    coordFromRowCol(9, 3),
    coordFromRowCol(9, 9),
    coordFromRowCol(9, 15),
    coordFromRowCol(15, 3),
    coordFromRowCol(15, 9),
    coordFromRowCol(15, 15),
  ]);

  return (
    <div className="flex flex-col items-center">
      <div className="relative overflow-x-auto rounded-lg border border-slate-300 bg-[#EBC687] p-3 shadow-xs">
        <svg
          width={width}
          height={height}
          viewBox={`0 0 ${width} ${height}`}
          className="select-none"
          role="img"
          aria-label="Go Life-and-Death Tsumego Board"
        >
          {/* Coordinate Labels */}
          {Array.from({ length: numCols }, (_, i) => {
            const c = minC + i;
            const x = pad + i * cellSize;
            return (
              <g key={`col-label-${c}`}>
                <text
                  x={x}
                  y={16}
                  textAnchor="middle"
                  className="fill-slate-800 font-mono text-[11px] font-semibold"
                >
                  {GO_COL_LETTERS[c]}
                </text>
                <text
                  x={x}
                  y={height - 8}
                  textAnchor="middle"
                  className="fill-slate-800 font-mono text-[10px]"
                >
                  {String.fromCharCode(97 + c)}
                </text>
              </g>
            );
          })}

          {Array.from({ length: numRows }, (_, i) => {
            const r = minR + i;
            const y = pad + i * cellSize;
            return (
              <g key={`row-label-${r}`}>
                <text
                  x={16}
                  y={y + 4}
                  textAnchor="middle"
                  className="fill-slate-800 font-mono text-[11px] font-semibold"
                >
                  {19 - r}
                </text>
                <text
                  x={width - 14}
                  y={y + 4}
                  textAnchor="middle"
                  className="fill-slate-800 font-mono text-[10px]"
                >
                  {String.fromCharCode(97 + r)}
                </text>
              </g>
            );
          })}

          {/* Horizontal Grid Lines */}
          {Array.from({ length: numRows }, (_, i) => {
            const r = minR + i;
            const y = pad + i * cellSize;
            const isBoardEdge = r === 0 || r === 18;
            return (
              <line
                key={`hline-${r}`}
                x1={pad}
                y1={y}
                x2={pad + (numCols - 1) * cellSize}
                y2={y}
                stroke="#2D2318"
                strokeWidth={isBoardEdge ? 2.2 : 1.1}
              />
            );
          })}

          {/* Vertical Grid Lines */}
          {Array.from({ length: numCols }, (_, i) => {
            const c = minC + i;
            const x = pad + i * cellSize;
            const isBoardEdge = c === 0 || c === 18;
            return (
              <line
                key={`vline-${c}`}
                x1={x}
                y1={pad}
                x2={x}
                y2={pad + (numRows - 1) * cellSize}
                stroke="#2D2318"
                strokeWidth={isBoardEdge ? 2.2 : 1.1}
              />
            );
          })}

          {/* Intersections, Overlays, and Stones */}
          {Array.from({ length: numRows }, (_, ri) =>
            Array.from({ length: numCols }, (_, ci) => {
              const r = minR + ri;
              const c = minC + ci;
              const coord = coordFromRowCol(r, c, 19);
              const cx = pad + ci * cellSize;
              const cy = pad + ri * cellSize;
              const stone = position.stoneAt(coord);
              const isBestMove = report.bestMove === coord;
              const isCrucial = crucialCoords.has(coord);
              const isPruned = prunedMovesSet.has(coord);
              const isInProofRz = proofRzSet.has(coord);
              const isInDisproofRz = disproofRzSet.has(coord);
              const isBensonAlive = bensonAliveSet.has(coord);
              const eyeType = eyeMap.get(coord);
              const pvStep = pvMoveMap.get(coord);
              const stoneRadius = cellSize * 0.43;

              return (
                <g
                  key={`pt-${coord}`}
                  onClick={() => onPlayCoord(coord)}
                  className="cursor-pointer group"
                >
                  {/* Transparent hit target */}
                  <rect
                    x={cx - cellSize / 2}
                    y={cy - cellSize / 2}
                    width={cellSize}
                    height={cellSize}
                    fill="transparent"
                  />

                  {/* Hoshi Star Point */}
                  {hoshiPoints.has(coord) && stone === Color.Empty && (
                    <circle cx={cx} cy={cy} r={3.2} fill="#2D2318" />
                  )}

                  {/* Relevance-Zone / Benson Overlay Highlights (FR-8.2 SGF Color Contract) */}
                  {overlayMode === 'proof-rz' && isInProofRz && (
                    <rect
                      x={cx - cellSize * 0.44}
                      y={cy - cellSize * 0.44}
                      width={cellSize * 0.88}
                      height={cellSize * 0.88}
                      rx={4}
                      fill="rgba(22, 163, 74, 0.24)"
                      stroke="#15803D"
                      strokeWidth={1.2}
                      strokeDasharray="3 2"
                    />
                  )}

                  {overlayMode === 'disproof-rz' && isInDisproofRz && (
                    <rect
                      x={cx - cellSize * 0.44}
                      y={cy - cellSize * 0.44}
                      width={cellSize * 0.88}
                      height={cellSize * 0.88}
                      rx={4}
                      fill="rgba(217, 119, 6, 0.26)"
                      stroke="#B45309"
                      strokeWidth={1.2}
                      strokeDasharray="3 2"
                    />
                  )}

                  {overlayMode === 'benson-uca' && isBensonAlive && (
                    <rect
                      x={cx - cellSize * 0.44}
                      y={cy - cellSize * 0.44}
                      width={cellSize * 0.88}
                      height={cellSize * 0.88}
                      rx={4}
                      fill="rgba(37, 99, 235, 0.24)"
                      stroke="#1D4ED8"
                      strokeWidth={1.4}
                    />
                  )}

                  {/* Outside-RZ Pruned Candidate Marker (Gray per FR-8.2) */}
                  {stone === Color.Empty && isPruned && (
                    <g>
                      <circle
                        cx={cx}
                        cy={cy}
                        r={stoneRadius * 0.65}
                        fill="rgba(100, 116, 139, 0.32)"
                        stroke="#475569"
                        strokeWidth={1.3}
                        strokeDasharray="2 2"
                      />
                      {!showFullBoard && (
                        <text
                          x={cx}
                          y={cy + 3}
                          textAnchor="middle"
                          className="fill-slate-800 font-mono text-[9px] font-bold"
                        >
                          RZ外
                        </text>
                      )}
                    </g>
                  )}

                  {/* Eye Topology Annotation on Empty Points */}
                  {stone === Color.Empty &&
                    overlayMode === 'benson-uca' &&
                    eyeType &&
                    !showFullBoard && (
                      <text
                        x={cx}
                        y={cy - stoneRadius * 0.45}
                        textAnchor="middle"
                        className="fill-blue-950 font-mono text-[9px] font-bold"
                      >
                        {eyeType === EyeTopologyType.TrueEye
                          ? '真眼'
                          : eyeType === EyeTopologyType.HalfEye
                          ? '半眼'
                          : eyeType === EyeTopologyType.FalseEye
                          ? '假眼'
                          : ''}
                      </text>
                    )}

                  {/* Best Move Marker on Empty Point (Red per FR-8.2) */}
                  {stone === Color.Empty && isBestMove && (
                    <g>
                      <circle
                        cx={cx}
                        cy={cy}
                        r={stoneRadius * 0.72}
                        fill="rgba(220, 38, 38, 0.22)"
                        stroke="#DC2626"
                        strokeWidth={2}
                      />
                      <text
                        x={cx}
                        y={cy + 4}
                        textAnchor="middle"
                        className="fill-red-800 font-mono text-[10px] font-bold"
                      >
                        急所
                      </text>
                    </g>
                  )}

                  {/* Simple Ko Ban Marker */}
                  {stone === Color.Empty && position.koPoint === coord && (
                    <rect
                      x={cx - 6}
                      y={cy - 6}
                      width={12}
                      height={12}
                      fill="none"
                      stroke="#DC2626"
                      strokeWidth={2}
                    />
                  )}

                  {/* Hover Preview on Empty Legal Point */}
                  {stone === Color.Empty && (
                    <circle
                      cx={cx}
                      cy={cy}
                      r={stoneRadius * 0.85}
                      fill={
                        position.toPlay === Color.Black
                          ? 'rgba(15, 23, 42, 0.25)'
                          : 'rgba(255, 255, 255, 0.45)'
                      }
                      className="opacity-0 group-hover:opacity-100 transition-opacity"
                    />
                  )}

                  {/* Placed Black or White Stone */}
                  {stone !== Color.Empty && (
                    <g>
                      <circle
                        cx={cx}
                        cy={cy + 1.2}
                        r={stoneRadius}
                        fill="rgba(0,0,0,0.22)"
                      />
                      <circle
                        cx={cx}
                        cy={cy}
                        r={stoneRadius}
                        fill={stone === Color.Black ? '#111827' : '#F8FAFC'}
                        stroke={stone === Color.Black ? '#030712' : '#475569'}
                        strokeWidth={1.3}
                      />

                      {/* Crucial Target Token Triangle Marker (FR-2.6) */}
                      {isCrucial && !pvStep && (
                        <polygon
                          points={`${cx},${cy - stoneRadius * 0.52} ${
                            cx - stoneRadius * 0.46
                          },${cy + stoneRadius * 0.34} ${
                            cx + stoneRadius * 0.46
                          },${cy + stoneRadius * 0.34}`}
                          fill="none"
                          stroke={
                            stone === Color.Black ? '#F59E0B' : '#D97706'
                          }
                          strokeWidth={1.8}
                        />
                      )}

                      {/* PV Step Number */}
                      {pvStep && (
                        <text
                          x={cx}
                          y={cy + 4}
                          textAnchor="middle"
                          fill={
                            stone === Color.Black ? '#FFFFFF' : '#0F172A'
                          }
                          className="font-mono text-[11px] font-bold"
                        >
                          {pvStep.stepNum}
                        </text>
                      )}
                    </g>
                  )}

                  <title>
                    {`${coordToHumanLabel(coord, 19)} | SGF: ${coordToSgf(
                      coord,
                      19
                    )}${isCrucial ? ' | 关键目标令牌 (crucial_stone)' : ''}${
                      isInProofRz ? ' | ProofCertificateRZ 内' : ''
                    }${isPruned ? ' | OutsideRZRevalidated 剪枝点' : ''}`}
                  </title>
                </g>
              );
            })
          )}
        </svg>
      </div>

      {/* Legend Bar (Unboxed clean metadata per Zero-Pill rule) */}
      <div className="mt-3 flex flex-wrap items-center justify-center gap-x-4 gap-y-1 text-xs text-slate-600">
        <span className="flex items-center gap-1.5">
          <span className="inline-block h-3 w-3 rounded-xs border border-amber-500" />
          <span>△ 关键目标令牌 (crucial_stone)</span>
        </span>
        <span aria-hidden="true">·</span>
        <span className="flex items-center gap-1.5">
          <span className="inline-block h-3 w-3 rounded-xs border border-red-600 bg-red-600/20" />
          <span>红框：胜着急所 (BestMove)</span>
        </span>
        <span aria-hidden="true">·</span>
        <span className="flex items-center gap-1.5">
          <span className="inline-block h-3 w-3 rounded-xs border border-green-700 bg-green-600/25" />
          <span>绿域：ProofCertificateRZ</span>
        </span>
        <span aria-hidden="true">·</span>
        <span className="flex items-center gap-1.5">
          <span className="inline-block h-3 w-3 rounded-xs border border-slate-600 bg-slate-500/30" />
          <span>灰圈：RZ 外重放剪枝 (OutsideRZRevalidated)</span>
        </span>
      </div>
    </div>
  );
};
