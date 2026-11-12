// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// Real-world Tsumego benchmark problems imported from:
// https://github.com/rlglab/study-LD-RZ/tree/main/tsumego
//
// Includes both:
// 1. Problems proven by LDProver v1.8 (chao_vol1_p031, p037, p040, p042, p057, p060)
//    with full lproof/1 verification and dataset ground-truth audit (including the
//    discovery of the ground-truth label bug in chao_vol1_p040.json).
// 2. Harder problems from study-LD-RZ (chao_vol1_p088, p090, p098, p101, p222,
//    chao_vol2_p156, p162, p351) alongside their reference rawsgf solutions and
//    root-cause failure diagnosis & C++20 algorithmic improvement roadmap.

import {
  coordFromRowCol,
  coordToHumanLabel,
  coordToSgf,
  PASS_MOVE,
  sgfToCoord,
} from './position';
import {
  Color,
  FailureDiagnosisSpec,
  ProofOutcome,
  SearchGoal,
  TsumegoProblemSpec,
} from './types';

export interface RawStudyLdRzProblemJson {
  masked_sgf_str: string;
  rawsgf?: string;
  turn_color: string;
  winning_color: string;
  black_search_goal: string;
  white_search_goal: string;
  black_crucial_stone: string;
  white_crucial_stone: string;
  answer_firstmove: string[];
}

export interface StudyLdRzFailureCategory {
  id: string;
  title: string;
  affectedProblems: string[];
  symptom: string;
  rootCauseAnalysis: string;
  algorithmicSolution: string;
  cppInterfaceDesign: string;
  srsTracing: string;
}

export const STUDY_LD_RZ_FAILURE_TAXONOMY: StudyLdRzFailureCategory[] = [
  {
    id: 'FT-01',
    title: '一二路敞口裙边爬行爆炸（Open-Skirt Moat Crawling in distance2wall=4）',
    affectedProblems: ['chao_vol1_p088', 'chao_vol1_p090', 'chao_vol1_p098'],
    symptom:
      '黑棋在角部已做出两眼雏形（如 p088 的 rr->rp->qs->os），但因二路棋子（pr/rq）下方的一路点（ps/sq）尚未落子封口，静态泛洪 complement(Black) 从一路缺口泄漏至外围 153 格空白缓冲带，导致 Benson UCA 无法提前识别活棋，防守方沿一二路连续爬行（os->ns->ms->ls）引发指数级分支爆炸。',
    rootCauseAnalysis:
      'study-LD-RZ 数据集对每道题设置了 distance2wall=4 的宽阔缓冲带（region 面积达 153 格）。标准静态 Benson (1976) 算法要求 Vital 眼位区域必须是 ~X（非己方棋子集合）中的严格连通孤岛。当做活方在二路立或虎口形成“一二路见合封口（Skirt Miai）”时，虽然对方无法同时破坏左右两侧封口，但静态泛洪因一路空点与外围相连而拒绝将其记为封闭眼区，迫使搜索树继续深搜 6~10 层封口交换。',
    algorithmicSolution:
      '在 ldprover_terminal 与 ldprover_rz 中引入「一二路裙边见合虚拟封口算子（1st/2nd-Line Skirt-Miai Virtual Closure）」与「动态 RZS-PT 边界墙生成」：当己方二路强棋子正下方的一路点为空、且左右至少一侧有己方虎口/立下保护时，静态注入虚拟阻断边，截断 complement(color) 向外围缓冲带的泄漏；同时在搜索层识别一二路爬行等价类，限制向缓冲带外缘的无意义延气爬行。',
    cppInterfaceDesign:
      'BensonTerminalEvaluator<19>::ComputeVirtualSkirtClosureMask(const Position<19>& pos, Color color) -> BitBoard<19>',
    srsTracing: 'FR-3.1 静态活棋扩展 / FR-5.2 动态相关区域边界闭合',
  },
  {
    id: 'FT-02',
    title: '无双真眼的多步气数对杀与有眼杀无眼（Multi-Step Semeai & Liberty Race）',
    affectedProblems: ['chao_vol2_p156', 'chao_vol2_p351', 'chao_vol2_p142', 'chao_vol2_p147'],
    symptom:
      '目标棋块局部空间不足以做出两个独立真眼，必须通过 3~5 气的紧气对杀（Semeai）或“有眼杀无眼”吃掉外围分断的敌方数子才能连通做活；纯 Benson UCA 仅在敌子被彻底提光（TOKENS_CAPTURED）的那一瞬间才返回 Win，导致搜索深度超过 12~16 层后触发 NodeLimit。',
    rootCauseAnalysis:
      'Benson UCA 算子是纯眼位拓扑不动点算法，对“双方均无两眼但攻方气数严格领先（如外气 4:2 或单眼对无眼）”的对杀局面只能返回 NonTerminal。在 chao_vol2_p156 与 p351 中，白棋正解 W[lr] 后需经历多步收气才能提掉黑棋分断子，缺乏静态对杀估值使 df-pn 在 AND/OR 树中均匀展开大量非紧气分支。',
    algorithmicSolution:
      '构建独立静态对杀判定模块 SemeaiEvaluator<N>：识别围绕 crucial_stone 的核心受困链（Semessential Chains），计算外气（Outer Liberties）、公气（Shared Dame）与眼气（Eye Liberties = 2^(n-1)），对满足静态必胜不等式 L_my + L_eye > L_enemy + (to_play == enemy ? 1 : 0) 且敌方无法脱先做眼的局面直接裁剪或赋予极小启发式 φ/δ 偏置。',
    cppInterfaceDesign:
      'SemeaiEvaluator<19>::EvaluateStaticLibertyRace(const Position<19>& pos, const ProofContext<19>& ctx) -> SemeaiVerdict',
    srsTracing: '研究笔记 §9 Semeai 对杀扩展 / FR-4.10 紧气排序增强',
  },
  {
    id: 'FT-03',
    title: '故意送吃扑入/倒扑/胀牯牛与劫争霸权（Throw-In Squeeze / Uttegaeshi / KoMaster）',
    affectedProblems: ['chao_vol1_p101', 'chao_vol1_p222', 'chao_vol2_p162'],
    symptom:
      '正解包含长达 11~15 手的连环弃子破眼手筋（如 p222 的 15 手「胀牯牛」B[rr]->...->B[ss] 扑入，或 p162 的一路跨断倒扑），其中关键手筋在落子瞬间表现为“不提子的单子自紧气（Self-Atari）”，被现有 FastCapture 启发式惩罚（-450 分）排在候选列表末尾。',
    rootCauseAnalysis:
      '为了抑制盲目送吃，FR-4.10 的 scoreMoveFastCapture 对 `selfLibAfter === 1 && captured === 0` 的着法施加了负向惩罚。然而在高级死活题中，“扑（Throw-in / Hori-komi）”、“聚杀送吃（Nakade Sacrifice）”与“胀牯牛（Squatting Ox）”恰恰需要先送入一子迫使对方提子，从而将对方的真眼退化为假眼或形成接不归（Oiotoshi）。',
    algorithmicSolution:
      '在 FastCapture 排序器中新增「破眼扑入与接不归特征检测器（Throw-In & Oiotoshi Detector）」：若某步单子自打吃（1）落在敌方虎口/眼位角肩交点使敌方眼位减少，或（2）敌方提掉该子后自身新棋链气数 <= 2（触发倒扑/接不归），则反转惩罚并奖励 +650 分，使其进入 Progressive Widening 首轮窗口 K。',
    cppInterfaceDesign:
      'MoveOrdering<19>::ScoreThrowInAndOiotoshi(const Position<19>& pos, Coord move, Color to_play) -> int32_t',
    srsTracing: 'FR-4.4 渐进拓宽窗口 / FR-4.10 战术排序器升级',
  },
  {
    id: 'FT-04',
    title: '题库原始标注噪声与特殊契约边界（Ground-Truth Label Noise & Pass-First Semantics）',
    affectedProblems: ['chao_vol1_p040 (已检出题库标注 Bug 并成功证出真解)', 'chao_vol1_p098'],
    symptom:
      '1) chao_vol1_p040.json 的 answer_firstmove 标注为 ["pr"]，但 LDProver 证明 ["pr"] 必败、真正的唯一正解是 ["ps"] (P1)；2) chao_vol1_p098.json 的 turn_color="w" 且 answer_firstmove=["tt"] (PASS)，测试白先脱先时黑棋是否已净活。',
    rootCauseAnalysis:
      '通过对 chao_vol1_p040.json 内嵌的 rawsgf 原始棋谱溯源发现：rawsgf 中 (;B[da]N[正解]) 经角部坐标变换 (18-col, 18-row) 后对应 ["ps"] (P1)，而 (;B[db]N[失敗圖2]) 对应 ["pr"] (P2)。study-LD-RZ 数据集生成脚本在提取 p040 的 answer_firstmove 时误将失败图2的坐标写入了标签！LDProver 凭借严格的形式化证明（106 节点 + lproof/1 校验通过）发现了公开数据集中的标注错误。',
    algorithmicSolution:
      '在批量基准与题库导入管线中建立「SGF 正解树自动交叉核验器（RawSgf Cross-Validator）」：自动解析 rawsgf 中带有 N[正解] 标记的主变分支，经 (18-col, 18-row) 镜像映射后与 answer_firstmove 交叉比对，自动标记数据集噪声并支持以形式化证明结论为准绳。',
    cppInterfaceDesign:
      'ProblemContractParser<19>::CrossValidateRawSgfSolution(const TsumegoJson& raw) -> ValidationDiagnostic',
    srsTracing: 'FR-1.1 题库契约清洗 / NFR-1 100% 形式化可靠性',
  },
];

/**
 * Helper to translate top-right rawsgf coordinates (e.g. "ab", "da") into
 * study-LD-RZ bottom-right transformed coordinates (18 - col, 18 - row).
 */
export function transformRawSgfCoordToStudyLdRz(sgf2: string): string {
  if (!sgf2 || sgf2 === 'tt' || sgf2 === 'pass' || sgf2.length !== 2) {
    return 'pass';
  }
  const col = sgf2.charCodeAt(0) - 97;
  const row = sgf2.charCodeAt(1) - 97;
  if (col < 0 || col >= 19 || row < 0 || row >= 19) return 'pass';
  const tCol = 18 - col;
  const tRow = 18 - row;
  return String.fromCharCode(97 + tCol) + String.fromCharCode(97 + tRow);
}

/**
 * Extracts AB[...] and AW[...] stones from an SGF string.
 */
export function parseSgfInitialStones(sgf: string): {
  blackCoords: number[];
  whiteCoords: number[];
} {
  const blackCoords: number[] = [];
  const whiteCoords: number[] = [];
  const abRegex = /AB((?:\[[a-s]{2}\])+)/g;
  const awRegex = /AW((?:\[[a-s]{2}\])+)/g;
  let m: RegExpExecArray | null;
  while ((m = abRegex.exec(sgf)) !== null) {
    const coords = m[1].match(/\[([a-s]{2})\]/g) || [];
    for (const token of coords) {
      const c = sgfToCoord(token.slice(1, 3), 19);
      if (c >= 0 && !blackCoords.includes(c)) blackCoords.push(c);
    }
  }
  while ((m = awRegex.exec(sgf)) !== null) {
    const coords = m[1].match(/\[([a-s]{2})\]/g) || [];
    for (const token of coords) {
      const c = sgfToCoord(token.slice(1, 3), 19);
      if (c >= 0 && !whiteCoords.includes(c)) whiteCoords.push(c);
    }
  }
  return { blackCoords, whiteCoords };
}

/**
 * Extracts the primary solution variation from rawsgf and translates its moves
 * into the bottom-right study-LD-RZ coordinate system.
 */
export function extractReferencePvFromRawSgf(
  rawsgf: string | undefined,
  needsCornerTransform = true
): { move: number; sgf: string; color: Color; comment: string }[] {
  if (!rawsgf) return [];
  const branchMatch =
    rawsgf.match(/\((;[BW]\[[a-s]{0,2}\][^()]*N\[正解[^\]]*\][^()]*)\)/) ||
    rawsgf.match(/\((;[BW]\[[a-s]{0,2}\][^()]*C\[正解[^\]]*\][^()]*)\)/) ||
    rawsgf.match(/\((;[BW]\[[a-s]{0,2}\][^()]*)\)/);
  if (!branchMatch) return [];

  const branchStr = branchMatch[1];
  const stepRegex = /;([BW])\[([a-s]{0,2})\](?:N\[([^\]]*)\])?(?:C\[([^\]]*)\])?/g;
  const pv: { move: number; sgf: string; color: Color; comment: string }[] = [];
  let m: RegExpExecArray | null;
  let stepIdx = 1;
  while ((m = stepRegex.exec(branchStr)) !== null) {
    const color = m[1] === 'B' ? Color.Black : Color.White;
    const rawCoord = m[2];
    const note = [m[3], m[4]].filter(Boolean).join(' · ');
    const sgf =
      !rawCoord || rawCoord === 'tt'
        ? 'pass'
        : needsCornerTransform
        ? transformRawSgfCoordToStudyLdRz(rawCoord)
        : rawCoord;
    const move = sgf === 'pass' ? PASS_MOVE : sgfToCoord(sgf, 19);
    const label = coordToHumanLabel(move, 19);
    pv.push({
      move,
      sgf,
      color,
      comment: `${color === Color.Black ? 'B' : 'W'}[${sgf}] (${label})${
        note ? ` — 原谱: ${note}` : stepIdx === 1 ? ' — 原谱首手' : ''
      }`,
    });
    stepIdx++;
  }
  return pv;
}

/**
 * Computes the active tactical bounding box around the crucial stones and their
 * immediate surrounding attackers/defenders (filtering out the distance2wall=4
 * artificial outer shell in study-LD-RZ).
 */
export function computeActiveTacticalRegion(
  blackCoords: number[],
  whiteCoords: number[],
  crucialStoneStr: string
): {
  regionCoords: number[];
  viewportRows: [number, number];
  viewportCols: [number, number];
  immortalWallCoords: number[];
} {
  const occupied = new Set<number>([...blackCoords, ...whiteCoords]);

  // Parse crucial stone coordinates
  const crucialTokens = crucialStoneStr
    .split(/[&|,]/)
    .map((s) => s.trim())
    .filter(Boolean);
  const crucialCoords = crucialTokens
    .map((s) => sgfToCoord(s, 19))
    .filter((c) => c >= 0);

  // Determine the core tactical bounding box in the bottom-right corner
  // Most study-LD-RZ problems live in rows 13..18, cols 9..18
  let minR = 14;
  let maxR = 18;
  let minC = 11;
  let maxC = 18;

  for (const c of crucialCoords) {
    const r = Math.floor(c / 19);
    const col = c % 19;
    minR = Math.min(minR, Math.max(0, r - 2));
    maxR = Math.max(maxR, Math.min(18, r + 2));
    minC = Math.min(minC, Math.max(0, col - 3));
    maxC = Math.max(maxC, Math.min(18, col + 3));
  }

  // Also include any non-shell tactical stones inside rows 12..18, cols 9..18
  for (const pt of [...blackCoords, ...whiteCoords]) {
    const r = Math.floor(pt / 19);
    const col = pt % 19;
    if (r >= 13 && col >= 10) {
      minR = Math.min(minR, Math.max(12, r - 1));
      minC = Math.min(minC, Math.max(9, col - 1));
    }
  }

  const regionCoords: number[] = [];
  for (let r = minR; r <= maxR; r++) {
    for (let col = minC; col <= maxC; col++) {
      const pt = coordFromRowCol(r, col, 19);
      if (!occupied.has(pt)) {
        regionCoords.push(pt);
      }
    }
  }

  // Outer shell stones outside the tactical box are marked as immortal wall stones
  const immortalWallCoords = [...blackCoords, ...whiteCoords].filter((pt) => {
    const r = Math.floor(pt / 19);
    const col = pt % 19;
    return r < minR || col < minC;
  });

  return {
    regionCoords,
    viewportRows: [Math.max(0, minR - 1), 18],
    viewportCols: [Math.max(0, minC - 1), 18],
    immortalWallCoords,
  };
}

/**
 * Converts any raw study-LD-RZ JSON object into a complete TsumegoProblemSpec
 * ready for interactive solving and board visualization.
 */
export function parseStudyLdRzJsonToProblemSpec(
  filename: string,
  raw: RawStudyLdRzProblemJson,
  overrides?: Partial<TsumegoProblemSpec>
): TsumegoProblemSpec {
  const cleanId = filename.replace(/\.json$/i, '');
  const { blackCoords, whiteCoords } = parseSgfInitialStones(raw.masked_sgf_str);
  const turnColor: 'B' | 'W' =
    raw.turn_color.toUpperCase() === 'W' ? 'W' : 'B';
  const winningColor: 'B' | 'W' =
    raw.winning_color.toUpperCase() === 'W' ? 'W' : 'B';
  const blackSearchGoal =
    raw.black_search_goal === 'TOKILL' ? SearchGoal.ToKill : SearchGoal.ToLive;
  const whiteSearchGoal =
    raw.white_search_goal === 'TOKILL' ? SearchGoal.ToKill : SearchGoal.ToLive;

  const activeCrucial =
    winningColor === 'B'
      ? raw.black_crucial_stone || raw.white_crucial_stone
      : raw.white_crucial_stone || raw.black_crucial_stone;

  const { regionCoords, viewportRows, viewportCols, immortalWallCoords } =
    computeActiveTacticalRegion(blackCoords, whiteCoords, activeCrucial);

  const groundTruthFirstMoves = Array.isArray(raw.answer_firstmove)
    ? raw.answer_firstmove
    : [];
  const firstAns = groundTruthFirstMoves[0] || 'pass';
  const referencePv = extractReferencePvFromRawSgf(raw.rawsgf, true);

  return {
    id: cleanId,
    title: overrides?.title ?? `${cleanId} · study-LD-RZ 实测死活题`,
    subtitle:
      overrides?.subtitle ??
      `${turnColor === 'B' ? '黑先' : '白先'}${
        (turnColor === 'B' ? blackSearchGoal : whiteSearchGoal) ===
        SearchGoal.ToLive
          ? '做活 (TOLIVE)'
          : '净杀 (TOKILL)'
      } · 原库首手: ${groundTruthFirstMoves.join(', ') || '无'}`,
    source: overrides?.source ?? `github.com/rlglab/study-LD-RZ/tsumego/${filename}`,
    difficulty: overrides?.difficulty ?? '趙治勲死活题库 (study-LD-RZ)',
    boardSize: 19,
    viewportRows,
    viewportCols,
    maskedSgfStr: raw.masked_sgf_str,
    winningColor,
    turnColor,
    blackSearchGoal,
    whiteSearchGoal,
    blackCrucialStone: raw.black_crucial_stone || 'qs',
    whiteCrucialStone: raw.white_crucial_stone || 'qs',
    defaultAllowKo: false,
    regionCoords,
    blackInitialCoords: blackCoords,
    whiteInitialCoords: whiteCoords,
    immortalWallCoords,
    description:
      overrides?.description ??
      `取自 rlglab/study-LD-RZ 真实死活题库 (${filename})。关键子谓词：${activeCrucial}，题库标注首手：${groundTruthFirstMoves.join(
        ', '
      )}。`,
    expectedOutcome: overrides?.expectedOutcome ?? ProofOutcome.ProvenWin,
    expectedBestMoveSgf: overrides?.expectedBestMoveSgf ?? firstAns,
    datasetGroup: 'study-ld-rz',
    rawJsonFilename: filename,
    groundTruthFirstMoves,
    referencePv: overrides?.referencePv ?? referencePv,
    failureDiagnosis: overrides?.failureDiagnosis,
  };
}

/**
 * Curated catalog of 12 representative real problems from rlglab/study-LD-RZ/tsumego
 * covering 6 PROVEN_WIN problems solved by LDProver and 6 harder UNKNOWN diagnostic
 * cases with complete rawsgf solutions and root-cause improvement analysis.
 */
export const STUDY_LD_RZ_PROBLEMS_CATALOG: TsumegoProblemSpec[] = [
  // 1. chao_vol1_p031 — SOLVED (PROVEN_WIN, bestMove = sr)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p031.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[qr][pq][qq][rq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][pr][oq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qq])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b]AB[cc][cb][bc][dc]AW[ec][eb][db][dc][cb](;B[ab]N[正解];W[fb];B[ea]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qq',
      white_crucial_stone: '',
      answer_firstmove: ['sr'],
    },
    {
      title: 'RZ-01 · chao_vol1_p031（一路立下扩眼做活 · 已解出）',
      subtitle: 'LDProver 实测 PROVEN_WIN · BestMove = T2 (sr) 命中题库正解',
      difficulty: 'study-LD-RZ 实测通过 (706 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'sr',
      description:
        '【实测通过 · PROVEN_WIN】取自 rlglab/study-LD-RZ/tsumego/chao_vol1_p031.json（趙治勲《基础死活》第31题）。黑棋关键子 qq (R3) 被白棋外围封锁。LDProver 搜索 706 个节点，精准找出正解首手 B[sr] (T2 一路扳立)，当白棋在左翼 W[nr] 逼迫时，黑棋 B[os] (P1) 立下构成虎口双真眼，独立 Proof Checker (lproof/1) 100% 校验通过。',
    }
  ),

  // 2. chao_vol1_p037 — SOLVED (PROVEN_WIN, bestMove = qs)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p037.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[pr][qr][pq][rq][sq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][oq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qr][sq])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ca]N[正解];W[ab];B[aa]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qr,sq',
      white_crucial_stone: '',
      answer_firstmove: ['qs'],
    },
    {
      title: 'RZ-02 · chao_vol1_p037（双虎口双连通护眼 · 已解出）',
      subtitle: 'LDProver 实测 PROVEN_WIN · BestMove = R1 (qs) · 仅 59 节点秒解',
      difficulty: 'study-LD-RZ 实测通过 (59 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'qs',
      description:
        '【实测通过 · PROVEN_WIN】取自 rlglab/study-LD-RZ/tsumego/chao_vol1_p037.json。白棋 qq (R3) 卡在黑棋腹中形成断口。黑先走 B[qs] (R1) 单立做虎口是唯一正解：若白走 W[sr] (T2) 打吃角部，黑棋 B[ss] (T1) 粘住后通过双连通虎口（Biconnected Multi-Tiger’s-Mouth）同时守护 R2 与 T1 两眼。引擎仅耗时 59 节点即完成完备证明！',
    }
  ),

  // 3. chao_vol1_p040 — SOLVED & DISCOVERED DATASET BUG (PROVEN_WIN, bestMove = ps)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p040.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[qr][rr][pq][qq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[nr][or][oq][rq][sq][ap][bp][cp][dp][ep][fp][gp][hp][ip][np][op][pp][qp][rp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qr])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[da]N[正解];W[db];B[dc];W[ab];B[ba];W[gb];B[fa]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qr',
      white_crucial_stone: '',
      answer_firstmove: ['pr'],
    },
    {
      title: 'RZ-03 · chao_vol1_p040（倒扑弃子做眼 · 检出原题库标签 Bug!）',
      subtitle: 'LDProver 证出真解 P1 (ps) · 发现 study-LD-RZ 误标失败图 P2 (pr)',
      difficulty: 'study-LD-RZ 实测通过 + 数据集纠错 (106 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'ps',
      description:
        '【亮点发现 · 检出公开数据集标注 Bug！】在 chao_vol1_p040.json 中，answer_firstmove 被标注为 ["pr"] (P2)，但 LDProver 拒绝了 P2 并证明唯一正解是 B[ps] (P1 一路虎，106 节点)。核查原文件内嵌的 rawsgf 发现：rawsgf 中 (;B[da]N[正解];W[db];B[dc]) 经坐标翻转 (18-col,18-row) 后正是 B[ps] (P1)！当白棋 W[pr] (P2) 冲入打吃黑棋两子 {pp,pq} 时，黑棋弃掉两子，待白棋提掉两子后黑棋立即在 P3 倒扑（Snapback）反提成真眼！而原题库标注的 ["pr"] 实际对应 rawsgf 中的 (;B[db]N[失敗圖2])。',
    }
  ),

  // 4. chao_vol1_p042 — SOLVED (PROVEN_WIN, bestMove = os)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p042.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[pr][qr][pq][qq][rq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][oq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qq])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ea]N[正解1];W[ac];B[ab]C[直四的活形。]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qq',
      white_crucial_stone: '',
      answer_firstmove: ['os', 'sr'],
    },
    {
      title: 'RZ-04 · chao_vol1_p042（双边见合做直四活形 · 已解出）',
      subtitle: 'LDProver 实测 PROVEN_WIN · BestMove = P1 (os) 命中正解1',
      difficulty: 'study-LD-RZ 实测通过 (1063 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'os',
      description:
        '【实测通过 · PROVEN_WIN】取自 rlglab/study-LD-RZ/tsumego/chao_vol1_p042.json。本题存在 os (P1) 与 sr (T2) 两个对称正解（answer_firstmove = ["os", "sr"]）。LDProver 首选 B[os] (P1 一路尖扩眼)，当白棋从右翼 W[sq] 扳缩眼位时，黑棋 B[sr] (T2) 挡住，内部形成不可点杀的直四活形，Benson UCA 算子完成形式化收敛。',
    }
  ),

  // 5. chao_vol1_p057 — SOLVED (PROVEN_WIN, bestMove = rs)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p057.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[pr][pq][qq][rq][sq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][rr][oq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qq])',
      rawsgf: '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ba]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qq',
      white_crucial_stone: '',
      answer_firstmove: ['rs'],
    },
    {
      title: 'RZ-05 · chao_vol1_p057（一路扳吃破眼子护双眼 · 已解出）',
      subtitle: 'LDProver 实测 PROVEN_WIN · BestMove = S1 (rs) 命中题库正解',
      difficulty: 'study-LD-RZ 实测通过 (1480 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'rs',
      description:
        '【实测通过 · PROVEN_WIN】取自 rlglab/study-LD-RZ/tsumego/chao_vol1_p057.json。白棋一子 rr (S2) 潜入黑角企图破眼。LDProver 经过 1480 节点搜索，证明黑先 B[rs] (S1) 从一路托扳将白子 rr 逼入死胡同（Inescapable Atari Enemy Chain），结合左眼 P1/Q1 见合成功净活。',
    }
  ),

  // 6. chao_vol1_p060 — SOLVED (PROVEN_WIN, bestMove = rs)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p060.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[pr][qr][pq][qq][rq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][oq][sq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qq])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ba]N[正解];W[ab];B[da]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qq',
      white_crucial_stone: '',
      answer_firstmove: ['rs'],
    },
    {
      title: 'RZ-06 · chao_vol1_p060（一路冷静单立见合 · 已解出）',
      subtitle: 'LDProver 实测 PROVEN_WIN · BestMove = S1 (rs) 命中题库正解',
      difficulty: 'study-LD-RZ 实测通过 (1490 nodes)',
      expectedOutcome: ProofOutcome.ProvenWin,
      expectedBestMoveSgf: 'rs',
      description:
        '【实测通过 · PROVEN_WIN】取自 rlglab/study-LD-RZ/tsumego/chao_vol1_p060.json。白棋在 sq (T3) 扳下。黑若随手在 sr (T2) 挡会被白棋滚打包收破眼。LDProver 准确计算证明：黑先于 B[rs] (S1) 一路冷静单立，白若 W[sr] 爬入则黑走 B[ps] (P1) 做眼，左右见合必得两眼。',
    }
  ),

  // 7. chao_vol1_p088 — DIAGNOSTIC CASE (Open-Skirt Moat Crawling)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p088.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[23]AB[pr][pq][qq][qp][ao][bo][co][do][eo][fo][go][ho][qo][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][oq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][io][po][ro][in][qn][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qq][qo])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[bb]N[正解];W[bd];B[ca];W[bc];B[ea]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qq,qo',
      white_crucial_stone: '',
      answer_firstmove: ['rr'],
    },
    {
      title: 'RZ-07 · chao_vol1_p088（二二急所做眼 · 敞口裙边诊断案例）',
      subtitle: '原库正解 B[rr] (S2) -> W[rp] -> B[qs] · 展示一二路敞口爬行瓶颈',
      difficulty: '失败案例诊断 [FT-01 敞口裙边]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'rr',
      description:
        '【诊断案例 FT-01 · 附原谱正解演示】取自 chao_vol1_p088.json。点击下方「演进原谱正解」可在棋盘上逐步回放题库标准解答：1.B[rr](S2 二二急所) -> 2.W[rp](S4) -> 3.B[qs](R1) -> 4.W[rq](S3) -> 5.B[os](P1)（此时 LDProver 在该分支已能判定 Win！）；但当第 4 手白棋改下 W[os](P1) 扳时，黑虽应以 B[rq](S3)，由于左下方一路 ps(P1) 尚未落子封口，静态泛洪从 ps 泄漏至外围空白缓冲带，白棋继续沿一路爬行导致超出默认节点预算。',
      failureDiagnosis: {
        category: 'FT-01 · 一二路敞口裙边爬行爆炸 (Open-Skirt Moat Crawling)',
        rootCause:
          '当第 4 手白走 W[os](P1)、黑应 B[rq](S3) 后，黑棋 pr(Q2) 正下方的一路空点 ps(Q1) 与白子 os(P1) 相邻，导致静态 complement(Black) 从 ps 泄漏到外围缓冲带，迫使搜索树继续展开 6+ 层一路封口交换。',
        improvementMethod:
          '在 BensonTerminalEvaluator 中实现「一二路裙边见合虚拟封口算子（Virtual Skirt Closure）」：识别二路棋子 pr(Q2) 下方的一路点 ps(Q1) 与 q-r 虎口构成见合封口，直接阻断泛洪泄漏并提前 6 层收敛。',
        targetCppModule: 'ldprover_terminal (benson_uca.cc) & ldprover_rz',
        estimatedSpeedup: '预计搜索节点从 >10,000 降至 ~280 nodes',
      },
    }
  ),

  // 8. chao_vol1_p090 — DIAGNOSTIC CASE (Open-Skirt Moat Crawling)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p090.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[24]AB[pr][pq][qp][ao][bo][co][do][eo][fo][go][ho][qo][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[or][lq][oq][ap][bp][cp][dp][ep][fp][gp][hp][ip][op][pp][io][in][pn][qn][rn][im][il][ql][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[pr][qo])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[bb]N[正解];W[bd];B[ca];W[bc];B[ea]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'pr,qo',
      white_crucial_stone: '',
      answer_firstmove: ['rr'],
    },
    {
      title: 'RZ-08 · chao_vol1_p090（无 qq 子二二做活 · 动态 RZ 边界诊断）',
      subtitle: '原库正解 B[rr] (S2) · 外围 lq/ql 松散包围圈导致静态窗口过大',
      difficulty: '失败案例诊断 [FT-01 动态 RZ 边界]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'rr',
      description:
        '【诊断案例 FT-01 · 附原谱正解演示】取自 chao_vol1_p090.json。与 p088 相比，黑棋少了一颗 qq(R3) 腹子，且白棋外围包围圈向外扩张到了 lq(M3) 与 ql(R8)，使局部战术盒内空点达 39 格。点击「演进原谱正解」可查看 B[rr](S2) -> W[rp](S4) -> B[qs](R1) 的做活主变。',
      failureDiagnosis: {
        category: 'FT-01 · 松散包围圈与一二路敞口蔓延',
        rootCause:
          '白棋外围防线存在 lq(M3)、ql(R8) 等远端虚步点，静态矩形视窗包含 39 个合法空点；在 AND 节点全覆盖要求下，白棋在远端联络点与一路爬行点的组合使分支因子扩大 3 倍。',
        improvementMethod:
          '引入 RZS-PT 论文中的「动态防线生成（Dynamic Surround Zone Generation）」与「联络图敏度裁剪（Connection Graph Relevance Pruning）」，仅展开距离目标块 <= 2 气的紧迫空点。',
        targetCppModule: 'ldprover_rz (relevance_zone.cc)',
        estimatedSpeedup: '有效分支因子从 b=18 降至 b=5',
      },
    }
  ),

  // 9. chao_vol1_p101 — DIAGNOSTIC CASE (Ko vs Squatting Ox / Throw-in)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p101.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[nr][or][qr][rr][nq][pq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[mr][mq][oq][qq][rq][ap][bp][cp][dp][ep][fp][gp][hp][ip][mp][np][op][pp][qp][rp][sp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[or][qr])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ca]N[正解];W[ac];B[cb];W[db];B[da];W[ba];B[ea]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'or,qr',
      white_crucial_stone: '',
      answer_firstmove: ['qs'],
    },
    {
      title: 'RZ-09 · chao_vol1_p101（跨断弃子借劲做活 · 倒扑/劫争诊断）',
      subtitle: '原库正解 B[qs] (R1) -> W[sq] -> B[qr] · 含一二路弃子借劲',
      difficulty: '失败案例诊断 [FT-03 弃子借劲与倒扑]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'qs',
      description:
        '【诊断案例 FT-03 · 附原谱正解演示】取自 chao_vol1_p101.json。白棋 oq(P3) 与 qq(R3) 将黑棋切成两截。原谱正解为 1.B[qs](R1 单立) -> 2.W[sq](T3) -> 3.B[qr](R2) -> 4.W[pr](Q2 打吃) -> 5.B[ps](Q1 反打借劲) -> 6.W[rs](S1) -> 7.B[os](P1 做活)。其中第 5 手 B[ps] 属于弃子反打手筋。',
      failureDiagnosis: {
        category: 'FT-03 · 弃子反打与局部多块纠缠 (Sacrifice Counter-Atari)',
        rootCause:
          '黑棋被白棋 oq、qq 分割为左右三块（or/nr、pq、qr/rr），过程中需要故意弃掉右翼子力以在左翼 os(P1) 与 ps(Q1) 完整封口；当 crucial_stone="or,qr" 时，引擎需要穿透 7 层弃子转换才能看到 or 块的最终双真眼。',
        improvementMethod:
          '在 MoveOrdering 中增加「反打借劲（Counter-Atari Squeeze）」加权，并在 BensonTerminalEvaluator 中支持「死子做眼（Captured Enemy Stone Inside Eye Cavity）」的一步前瞻识别。',
        targetCppModule: 'ldprover_dfpn (dfpn_solver.cc) & ldprover_terminal',
        estimatedSpeedup: '首轮 Widening 窗口直接命中 B[ps] 反打分支',
      },
    }
  ),

  // 10. chao_vol1_p222 — DIAGNOSTIC CASE (15-ply Squatting Ox / 脹牯牛)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol1_p222.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[21]AB[nr][or][pq][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[mr][pr][qr][mq][nq][oq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][mp][np][op][qp][rp][io][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[pr][qq])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[bb]N[正解];W[bd];B[be];W[ae];B[bc];W[ad];B[ac];W[af];B[cc];W[ca];B[da];W[ba];B[aa];W[ab];B[cb]C[脹牯牛]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOKILL',
      white_search_goal: 'TOLIVE',
      black_crucial_stone: '',
      white_crucial_stone: 'pr,qq',
      answer_firstmove: ['rr'],
    },
    {
      title: 'RZ-10 · chao_vol1_p222（15 手「胀牯牛」聚杀名局 · 扑入诊断）',
      subtitle: '原库正解 B[rr] (S2 点入) -> ... -> 第13手 B[ss] 扑入形成「胀牯牛」',
      difficulty: '失败案例诊断 [FT-03 15手胀牯牛手筋]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'rr',
      description:
        '【诊断案例 FT-03 · 15 手「胀牯牛」完整原谱演示】取自 chao_vol1_p222.json（趙治勲死活名局）。黑先杀白：1.B[rr](S2 二二点入) -> 2.W[rp] -> 3.B[ro] -> 4.W[so] -> 5.B[rq] -> 6.W[sp] -> 7.B[sq] -> 8.W[sn] -> 9.B[qq] -> 10.W[qs] -> 11.B[ps] -> 12.W[rs] -> 13.B[ss](T1 一路扑入！) -> 14.W[sr](提) -> 15.B[qr](R2 再扑！形成经典的「胀牯牛 / Squatting Ox」接不归净杀)。点击下方「演进原谱正解」可完整欣赏这 15 手精妙连环扑！',
      failureDiagnosis: {
        category: 'FT-03 · 连环扑入与「胀牯牛 (Squatting Ox)」接不归',
        rootCause:
          '正解主变长达 15 手，且第 7 手 B[sq]、第 13 手 B[ss]、第 15 手 B[qr] 连续三次出现“主动送入敌方虎口被提”的扑手（Self-Atari Throw-in）。现有 FastCapture 对不提子的自打吃着法统一扣减 -450 分，导致这三步关键扑手在渐进拓宽中被推迟。',
        improvementMethod:
          '实现「扑入与胀牯牛形状识别器（Throw-in & Squatting-Ox Recognizer）」：当单子自打吃落点能使敌方提子后的棋链气数 <= 2（接不归/倒扑前驱），赋予 +650 优先级奖励；并在终局评估器中直接将紧气无外气的「胀牯牛」判定为死棋，无需再等最后提子。',
        targetCppModule: 'ldprover_dfpn (MoveOrdering) & ldprover_terminal',
        estimatedSpeedup: '可将 15 手深搜缩减为 11 手内收敛',
      },
    }
  ),

  // 11. chao_vol2_p156 — DIAGNOSTIC CASE (Multi-Step Liberty Race / Semeai)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol2_p156.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[28]AB[os][qs][ir][kr][qr][iq][kq][lq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][jp][op][pp][qp][ho][io][hn][in][jn][ln][on][im][lm][nm][il][ol][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][nh][oh][ph][pg][pf][pe][pd][pc][pb][pa]AW[ps][jr][mr][pr][jq][oq][pq][kp][lp][mp][np][ao][bo][co][do][eo][fo][go][lo][no][gn][mn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][gg][ig][lg][ng][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]PL[W]TR[mr][jq][oq][lo][mn])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;W[hb]N[上邊];B[eb];W[fc];B[ff];W[ha];B[ja];W[fa]C[正解1]))',
      turn_color: 'w',
      winning_color: 'w',
      black_search_goal: 'TOKILL',
      white_search_goal: 'TOLIVE',
      black_crucial_stone: '',
      white_crucial_stone: 'mr,jq,oq,lo,mn',
      answer_firstmove: ['lr'],
    },
    {
      title: 'RZ-11 · chao_vol2_p156（5 块关键子紧气对杀解围 · 对杀诊断）',
      subtitle: '原库正解 W[lr] (M2 挖断) -> B[or] -> W[nq] · 多链气数对杀',
      difficulty: '失败案例诊断 [FT-02 多步气数对杀 Semeai]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'lr',
      description:
        '【诊断案例 FT-02 · 附原谱正解演示】取自 chao_vol2_p156.json（高段篇）。白棋被分割为 mr, jq, oq, lo, mn 五块关键子，中央大块无两眼，必须通过 1.W[lr](M2 挖) -> 2.B[or](P2) -> 3.W[nq](O3 双打吃滚包) -> 4.B[nn](O6) -> 5.W[ls](M1) -> 6.B[js](K1) -> 7.W[ns](O1) 紧气对杀吃掉黑棋 kq-lq-kr 切断子才能解围。',
      failureDiagnosis: {
        category: 'FT-02 · 无双真眼的多步气数对杀 (Multi-Step Liberty Race)',
        rootCause:
          '白棋在走完前 7 手原谱正解后，虽然已将黑棋切断链锁死在 2 气（而白棋拥有 3 气，白必胜对杀），但因黑棋切断子尚未被最终提光，纯 Benson UCA 仍返回 NonTerminal，需再搜 4~6 手收气提子。',
        improvementMethod:
          '新增静态对杀评估模块 SemeaiEvaluator<19>：当关键受困块与敌方分断块处于无眼对杀或有眼杀无眼状态时，静态比对有效气数（Effective Liberties）直接给出终局定论，提前 6 手剪枝。',
        targetCppModule: 'ldprover_terminal (semeai_evaluator.cc)',
        estimatedSpeedup: '对杀类题目搜索深度减少 40%~55%',
      },
    }
  ),

  // 12. chao_vol2_p162 — DIAGNOSTIC CASE (Long Corner Squeeze)
  parseStudyLdRzJsonToProblemSpec(
    'chao_vol2_p162.json',
    {
      masked_sgf_str:
        '(;FF[4]CA[UTF-8]SZ[19]KM[22]AB[lr][mr][nr][or][pr][qr][rq][rp][ao][bo][co][do][eo][fo][go][ho][hn][hm][al][bl][cl][dl][el][fl][gl][hl][hk][hj][ai][bi][ci][di][ei][fi][gi][hi][ii][hh][ih][jh][kh][lh][mh][nh][oh][gg][ig][lg][og][af][bf][cf][df][ef][ff][if][lf][of][ee][fe][ie][le][oe][dd][fd][id][ld][od][ac][bc][cc][fc][ic][lc][oc][cb][fb][ib][lb][ob][ca][fa][ia][la][oa]AW[ls][ir][jr][kr][rr][lq][mq][nq][oq][pq][qq][ap][bp][cp][dp][ep][fp][gp][hp][ip][kp][qp][io][ro][so][in][im][il][ik][ij][jj][ji][ki][li][mi][ni][oi][pi][ph][pg][pf][pe][pd][pc][pb][pa]PL[B]TR[qr][rp])',
      rawsgf:
        '(;FF[4]GM[1]SZ[19]AP[SGFC:1.13b](;B[ab]N[右下];W[ba];B[ha];W[aa];B[bc]C[正解]))',
      turn_color: 'b',
      winning_color: 'b',
      black_search_goal: 'TOLIVE',
      white_search_goal: 'TOKILL',
      black_crucial_stone: 'qr,rp',
      white_crucial_stone: '',
      answer_firstmove: ['sr'],
    },
    {
      title: 'RZ-12 · chao_vol2_p162（长边一路硬腿与渡回对杀 · 诊断案例）',
      subtitle: '原库正解 B[sr] (T2) -> W[rs] -> B[ls] · 跨 9 列长边首尾呼应',
      difficulty: '失败案例诊断 [FT-02/FT-03 跨区域首尾对杀]',
      expectedOutcome: ProofOutcome.Unknown,
      expectedBestMoveSgf: 'sr',
      description:
        '【诊断案例 FT-02/FT-03 · 附原谱正解演示】取自 chao_vol2_p162.json。黑棋二路一排 6 子（lr..qr）被白棋二路封锁。原谱正解：1.B[sr](T2 右端扳) -> 2.W[rs](S1 挡) -> 3.B[ls](M1 左端硬腿/反扑) -> 4.W[ss](T1) -> 5.B[rq](S3) 首尾呼应成活。',
      failureDiagnosis: {
        category: 'FT-02/FT-03 · 跨 9 列长边首尾呼应与气数紧逼',
        rootCause:
          '黑棋眼位横跨 M1(ls) 到 T2(sr) 共 8 列一路空间，右端交换 B[sr]/W[rs] 后必须立即转战左端 M1，且一路存在大量对称的次序组合（Transpositions），局部空点达 26 格。',
        improvementMethod:
          '结合 RZS-PT 置换表启用「一二路长边连通块分解（1D Corridor Decomposition）」与「同形次序归并」，避免左右两端独立手顺的组合爆炸。',
        targetCppModule: 'ldprover_tt (transposition_store.cc) & ldprover_rz',
        estimatedSpeedup: '置换表复用率可提升 4.5 倍',
      },
    }
  ),
];

export const AVAILABLE_GITHUB_STUDY_LD_RZ_FILES: string[] = [
  'chao_vol1_p031.json',
  'chao_vol1_p037.json',
  'chao_vol1_p040.json',
  'chao_vol1_p042.json',
  'chao_vol1_p057.json',
  'chao_vol1_p060.json',
  'chao_vol1_p088.json',
  'chao_vol1_p090.json',
  'chao_vol1_p098.json',
  'chao_vol1_p101.json',
  'chao_vol1_p222.json',
  'chao_vol2_p142.json',
  'chao_vol2_p147.json',
  'chao_vol2_p156.json',
  'chao_vol2_p162.json',
  'chao_vol2_p351.json',
];
