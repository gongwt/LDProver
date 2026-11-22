// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/search/dfpn_solver.cc
// Description: Implementation of DfpnSolver<N> (FR-4.1..FR-4.10, FR-5.5, FR-5.7).

#include "ldprover/search/dfpn_solver.h"

#include <algorithm>
#include <array>
#include <cstdlib>
#include <limits>
#include <utility>
#include <vector>

namespace ldprover {

namespace {

constexpr uint32_t ClampSat(uint64_t val) noexcept {
  return val >= kPnDnSaturation ? kPnDnSaturation : static_cast<uint32_t>(val);
}

std::string HexU64Compact(uint64_t v) {
  static constexpr char kHex[] = "0123456789abcdef";
  std::string out(16, '0');
  for (int i = 15; i >= 0; --i) {
    out[static_cast<size_t>(i)] = kHex[v & 0xFULL];
    v >>= 4;
  }
  return out;
}

}  // namespace

template <int N>
bool DfpnSolver<N>::IsMemoryBudgetExceeded(
    uint32_t active_depth) const noexcept {
  if (config_.memory_budget_bytes == 0ULL) return false;
  const uint64_t approx_bytes =
      static_cast<uint64_t>(report_.proof_dag_nodes.size()) * 768ULL +
      static_cast<uint64_t>(tt_store_.EstimatedEntryCount()) * 1024ULL +
      static_cast<uint64_t>(node_frontier_cache_.size()) * 4096ULL +
      static_cast<uint64_t>(reval_cache_.size()) * 128ULL +
      static_cast<uint64_t>(active_depth + 1U) * 2048ULL;
  return approx_bytes > config_.memory_budget_bytes;
}

template <int N>
SolveReport<N> DfpnSolver<N>::Solve(
    const Position<N>& initial_pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint,
    const std::string& problem_id) {
  // FR-6.2: Clear BoardTT, PatternTT, and per-solve caches at problem start.
  tt_store_.ClearAll();
  node_frontier_cache_.clear();
  reval_cache_.clear();
  dag_has_capture_.clear();
  next_path_id_ = 1ULL;
  report_ = SolveReport<N>{};
  report_.problem_id = problem_id;
  report_.input_hash = initial_pos.ZobristHash();
  report_.region_hint = region_hint;

  // Build target-anchored local tactical attention mask matching TS
  // studyLdRzCatalog.ts: Chebyshev radius 1 around target-side non-immortal
  // stones + crucial tokens + 1st/2nd-line edge strip inside region_hint.
  attention_mask_.reset();
  if (region_hint.has_value() && region_hint->Any()) {
    const Color target_color =
        !context.initial_tokens.empty()
            ? context.initial_tokens[0].stone_color
            : (context.attacker_goal == SearchGoal::kToLive
                   ? context.root_attacker
                   : OppositeColor(context.root_attacker));
    const BitBoard<N> non_wall = ~initial_pos.ImmortalWall();
    BitBoard<N> anchor_stones = initial_pos.Stones(target_color) & non_wall;
    if (anchor_stones.None()) {
      anchor_stones = (initial_pos.Stones(Color::kBlack) |
                       initial_pos.Stones(Color::kWhite)) &
                      non_wall;
    }
    BitBoard<N> anchors = anchor_stones;
    for (const auto& tok : context.initial_tokens) {
      if (tok.initial_coord >= 0 && tok.initial_coord < N * N) {
        anchors.Set(tok.initial_coord, true);
      }
    }
    const std::vector<int> anchor_coords = anchors.ToCoords();
    if (!anchor_coords.empty()) {
      int min_r = N - 1;
      int max_r = 0;
      int min_c = N - 1;
      int max_c = 0;
      for (int pt : anchor_coords) {
        const int r = pt / N;
        const int c = pt % N;
        if (r < min_r) min_r = r;
        if (r > max_r) max_r = r;
        if (c < min_c) min_c = c;
        if (c > max_c) max_c = c;
      }
      const int att_min_r = std::max(0, min_r - 2);
      const int att_min_c = std::max(0, min_c - 2);
      const int att_max_r = std::min(N - 1, max_r + 2);
      const int att_max_c = std::min(N - 1, max_c + 2);
      const bool bottom_right_study = (N == 19 && max_r >= 12 && max_c >= 12);

      BitBoard<N> att;
      for (int pt : region_hint->ToCoords()) {
        const int r = pt / N;
        const int c = pt % N;
        if (bottom_right_study) {
          if (r < att_min_r || c < att_min_c) continue;
          if (r >= N - 2 && c >= att_min_c + 1) {
            att.Set(pt, true);
            continue;
          }
        } else {
          if (r < att_min_r || r > att_max_r || c < att_min_c ||
              c > att_max_c) {
            continue;
          }
          const bool near_top_edge = (min_r <= 2 && r <= 1);
          const bool near_bot_edge = (max_r >= N - 3 && r >= N - 2);
          const bool near_left_edge = (min_c <= 2 && c <= 1);
          const bool near_right_edge = (max_c >= N - 3 && c >= N - 2);
          if (near_top_edge || near_bot_edge || near_left_edge ||
              near_right_edge) {
            att.Set(pt, true);
            continue;
          }
        }
        for (int st : anchor_coords) {
          if (std::abs((st / N) - r) <= 1 && std::abs((st % N) - c) <= 1) {
            att.Set(pt, true);
            break;
          }
        }
      }
      if (att.Any()) attention_mask_ = att;
    }
  }

  Position<N> work_pos = initial_pos;
  std::unordered_set<uint64_t> in_path_hashes;
  bool ko_dep = false;
  bool root_has_capture = false;
  const uint64_t root_path_id = next_path_id_++;

  MidSearch(work_pos, context, region_hint, kPnDnSaturation, kPnDnSaturation,
            0, root_path_id, in_path_hashes, &report_.root_pn, &report_.root_dn,
            &report_.root_status, &ko_dep, &root_has_capture,
            &report_.root_proof_rz, &report_.root_disproof_rz,
            &report_.root_dag_node_id, kPassMove);

  if (ko_dep && report_.root_status == ProofOutcome::kUnknown &&
      report_.unknown_reason == UnknownReason::kNone) {
    report_.unknown_reason = UnknownReason::kKoDependent;
  }

  // Extract principal variation when proven.
  if (report_.root_status != ProofOutcome::kUnknown &&
      report_.root_dag_node_id != kInvalidDagNodeId &&
      report_.root_dag_node_id < report_.proof_dag_nodes.size()) {
    uint32_t cur_id = report_.root_dag_node_id;
    for (int step = 0; step < 64 && cur_id < report_.proof_dag_nodes.size();
         ++step) {
      const auto& cur = report_.proof_dag_nodes[cur_id];
      if ((cur.is_pruned_outside_rz || cur.is_tt_hit) &&
          cur.source_proof_node_id != kInvalidDagNodeId &&
          cur.source_proof_node_id < cur.node_id) {
        cur_id = cur.source_proof_node_id;
        continue;
      }
      if (cur.child_node_ids.empty()) break;
      int chosen = -1;
      for (size_t i = 0; i < cur.child_node_ids.size(); ++i) {
        if (cur.child_node_ids[i] < report_.proof_dag_nodes.size() &&
            report_.proof_dag_nodes[cur.child_node_ids[i]].outcome ==
                cur.outcome) {
          chosen = static_cast<int>(i);
          if (cur.child_moves[i] != kPassMove) break;
        }
      }
      if (chosen < 0) break;
      report_.principal_variation.push_back(cur.child_moves[chosen]);
      cur_id = cur.child_node_ids[chosen];
    }
  }

  report_.board_tt_hits = tt_store_.BoardHits();
  report_.pattern_tt_hits = tt_store_.PatternHits();
  report_.pattern_proof_reusable = tt_store_.PatternProofReusableHits();
  report_.rz_size_at_root =
      (report_.root_status == ProofOutcome::kProvenWin)
          ? report_.root_proof_rz.Size()
          : report_.root_disproof_rz.Size();
  return report_;
}

template <int N>
typename DfpnSolver<N>::NodeTacticalContext
DfpnSolver<N>::BuildNodeTacticalContext(const Position<N>& pos,
                                        const ProofContext& context) const {
  NodeTacticalContext ctx;
  constexpr int kGridLen = N * N;
  ctx.chain_id_at.fill(-1);
  ctx.crucial_lib_min_libs.fill(99U);
  ctx.chain_libs.reserve(64U);
  ctx.chain_is_immortal.reserve(64U);
  ctx.chain_is_cutting_enemy.reserve(64U);

  std::array<int, kGridLen> bfs_q{};
  std::array<int, kGridLen> lib_stamp{};
  lib_stamp.fill(-1);

  const BitBoard<N>& wall = pos.ImmortalWall();
  const Color us = pos.ToPlay();
  const Color enemy = OppositeColor(us);

  for (int coord = 0; coord < kGridLen; ++coord) {
    const Color col = pos.StoneAt(coord);
    if (col == Color::kEmpty || ctx.chain_id_at[static_cast<size_t>(coord)] != -1) {
      continue;
    }
    const int16_t cid = static_cast<int16_t>(ctx.chain_libs.size());
    ctx.chain_id_at[static_cast<size_t>(coord)] = cid;
    bfs_q[0] = coord;
    int head = 0;
    int tail = 1;
    bool immortal = wall.Get(coord);
    int16_t libs = 0;

    while (head < tail) {
      const int cur = bfs_q[static_cast<size_t>(head++)];
      for (int nb : pos.OrthogonalNeighbors(cur)) {
        const Color st = pos.StoneAt(nb);
        if (st == col) {
          if (ctx.chain_id_at[static_cast<size_t>(nb)] == -1) {
            ctx.chain_id_at[static_cast<size_t>(nb)] = cid;
            if (!immortal && wall.Get(nb)) immortal = true;
            bfs_q[static_cast<size_t>(tail++)] = nb;
          }
        } else if (st == Color::kEmpty) {
          if (lib_stamp[static_cast<size_t>(nb)] != cid) {
            lib_stamp[static_cast<size_t>(nb)] = cid;
            ++libs;
          }
        }
      }
    }

    ctx.chain_libs.push_back(libs);
    ctx.chain_is_immortal.push_back(immortal ? 1U : 0U);
    ctx.chain_is_cutting_enemy.push_back(0U);
  }

  // Mark cutting enemy chains (non-immortal enemy chains with <= 3 liberties
  // touching >= 2 distinct friendly chains).
  const size_t num_chains = ctx.chain_libs.size();
  std::vector<uint8_t> seen_enemy_chain(num_chains, 0U);
  for (int coord = 0; coord < kGridLen; ++coord) {
    if (pos.StoneAt(coord) != enemy) continue;
    const int16_t cid = ctx.chain_id_at[static_cast<size_t>(coord)];
    if (cid < 0) continue;
    const size_t ucid = static_cast<size_t>(cid);
    if (seen_enemy_chain[ucid] || ctx.chain_is_immortal[ucid] ||
        ctx.chain_libs[ucid] > 3) {
      continue;
    }
    seen_enemy_chain[ucid] = 1U;
    int16_t first_friendly_cid = -1;
    bool second_friendly_found = false;
    for (int p = coord; p < kGridLen && !second_friendly_found; ++p) {
      if (ctx.chain_id_at[static_cast<size_t>(p)] != cid) continue;
      for (int nb : pos.OrthogonalNeighbors(p)) {
        if (pos.StoneAt(nb) == us) {
          const int16_t fcid = ctx.chain_id_at[static_cast<size_t>(nb)];
          if (first_friendly_cid == -1) {
            first_friendly_cid = fcid;
          } else if (fcid != first_friendly_cid) {
            second_friendly_found = true;
            break;
          }
        }
      }
    }
    if (second_friendly_found) {
      ctx.chain_is_cutting_enemy[ucid] = 1U;
    }
  }

  // Mark surviving crucial target chains and their liberties.
  std::vector<uint8_t> seen_crucial_chains(num_chains, 0U);
  for (size_t idx = 0; idx < context.initial_tokens.size() && idx < 64U; ++idx) {
    if ((pos.SurvivingTargetTokensMask() & (1ULL << idx)) == 0ULL) continue;
    const int t_coord = context.initial_tokens[idx].initial_coord;
    if (t_coord < 0 || t_coord >= kGridLen) continue;
    const int16_t cid = ctx.chain_id_at[static_cast<size_t>(t_coord)];
    if (cid < 0 || seen_crucial_chains[static_cast<size_t>(cid)]) continue;
    seen_crucial_chains[static_cast<size_t>(cid)] = 1U;
    const uint8_t libs = static_cast<uint8_t>(
        std::min<int>(98, std::max<int>(0, ctx.chain_libs[static_cast<size_t>(cid)])));
    for (int p = 0; p < kGridLen; ++p) {
      if (ctx.chain_id_at[static_cast<size_t>(p)] != cid) continue;
      ctx.crucial_stone_mask.Set(p, true);
      for (int nb : pos.OrthogonalNeighbors(p)) {
        if (pos.StoneAt(nb) == Color::kEmpty &&
            libs < ctx.crucial_lib_min_libs[static_cast<size_t>(nb)]) {
          ctx.crucial_lib_min_libs[static_cast<size_t>(nb)] = libs;
        }
      }
    }
  }

  ctx.target_color =
      !context.initial_tokens.empty()
          ? context.initial_tokens[0].stone_color
          : (context.attacker_goal == SearchGoal::kToLive
                 ? context.root_attacker
                 : OppositeColor(context.root_attacker));
  return ctx;
}

template <int N>
int DfpnSolver<N>::EstimateParentEyeLikeCount(const Position<N>& pos,
                                              const ProofContext& context) {
  if (context.initial_tokens.empty()) return 0;
  const Color target_color = context.initial_tokens[0].stone_color;
  const Color enemy_color = OppositeColor(target_color);

  // Count protected tiger's-mouth (+1) and fully surrounded single-point (+2)
  // eye-like liberties adjacent to surviving crucial chains (1:1 parity with TS
  // BensonTerminalEvaluator::estimateHeuristicShapePotential).
  BitBoard<N> candidate_eye_pts;
  for (size_t idx = 0; idx < context.initial_tokens.size() && idx < 64U; ++idx) {
    if ((pos.SurvivingTargetTokensMask() & (1ULL << idx)) == 0ULL) continue;
    const int t_coord = context.initial_tokens[idx].initial_coord;
    if (t_coord < 0 || t_coord >= N * N) continue;
    if (pos.StoneAt(t_coord) != target_color) continue;
    BitBoard<N> libs;
    (void)pos.FloodFillChain(t_coord, &libs);
    candidate_eye_pts |= libs;
  }

  int eye_like_count = 0;
  for (int pt : candidate_eye_pts.ToCoords()) {
    const auto nbs = pos.OrthogonalNeighbors(pt);
    int friendly_nbs = 0;
    int enemy_nbs = 0;
    for (int nb : nbs) {
      const Color st = pos.StoneAt(nb);
      if (st == target_color) {
        ++friendly_nbs;
      } else if (st == enemy_color) {
        ++enemy_nbs;
      }
    }
    const int deg = static_cast<int>(nbs.size());
    if (enemy_nbs == 0 && friendly_nbs == deg) {
      eye_like_count += 2;  // Fully surrounded single-point eye candidate
    } else if (enemy_nbs == 0 && friendly_nbs >= std::max(2, deg - 1)) {
      eye_like_count += 1;  // Protected tiger's mouth
    }
  }
  return eye_like_count;
}

template <int N>
int32_t DfpnSolver<N>::EvaluatePassMoveScore(const Position<N>& pos,
                                             const ProofContext& context,
                                             bool is_or_node) const {
  const int parent_eye_like_count =
      (!is_or_node && pos.ConsecutivePasses() == 0U &&
       config_.enable_fast_capture_ordering)
          ? EstimateParentEyeLikeCount(pos, context)
          : 0;
  const NodeTacticalContext empty_tctx{};
  return EvaluateCandidateMove(pos, context, empty_tctx, kPassMove, is_or_node,
                               parent_eye_like_count)
      .score;
}

template <int N>
typename DfpnSolver<N>::MoveEvalMeta DfpnSolver<N>::EvaluateCandidateMove(
    const Position<N>& pos, const ProofContext& context,
    const NodeTacticalContext& tctx, int16_t move, bool is_or_node,
    int parent_eye_like_count) const {
  if (move == kPassMove) {
    if (pos.ConsecutivePasses() >= 1U) {
      Position<N> probe = pos;
      if (probe.PlayMove(kPassMove)) {
        const auto term = terminal_eval_.EvaluateTerminal(probe, context);
        if (is_or_node && term.status == TerminalStatus::kWin) {
          return MoveEvalMeta{60000, true, false, true};
        }
        if (!is_or_node && term.status == TerminalStatus::kLoss) {
          return MoveEvalMeta{60000, false, true, true};
        }
      }
    }
    // At AND nodes (consecutivePasses == 0), rank Null-Move (PASS) inside the
    // initial tactical window right behind top immediate captures/refutations
    // so PASS seeds active_null_move_rz early without preempting 1-ply refutations.
    if (!is_or_node && pos.ConsecutivePasses() == 0U) {
      if (parent_eye_like_count >= 2) {
        return MoveEvalMeta{3850, false, false, true};
      }
      return MoveEvalMeta{config_.enable_rz_pruning ? 3450 : 360, false, false,
                          true};
    }
    return MoveEvalMeta{-2500, false, false, false};
  }

  const auto ortho_nbs = pos.OrthogonalNeighbors(move);
  const auto diag_nbs = pos.DiagonalNeighbors(move);
  const BitBoard<N>& wall = pos.ImmortalWall();
  bool in_attention =
      !attention_mask_.has_value() || attention_mask_->Get(move);

  // Dynamic tactical attention: follow the live fight when crucial target
  // chains extend (or non-immortal chains drop to <= 3 liberties) beyond the
  // static root bounding box.
  if (!in_attention && tctx.crucial_lib_min_libs[static_cast<size_t>(move)] < 99U) {
    in_attention = true;
  }
  if (!in_attention) {
    for (int nb : ortho_nbs) {
      if (pos.StoneAt(nb) != Color::kEmpty && !wall.Get(nb)) {
        const int16_t cid = tctx.chain_id_at[static_cast<size_t>(nb)];
        if (cid >= 0 && !tctx.chain_is_immortal[static_cast<size_t>(cid)] &&
            tctx.chain_libs[static_cast<size_t>(cid)] <= 3) {
          in_attention = true;
          break;
        }
      }
    }
  }
  if (!in_attention) {
    for (int d : diag_nbs) {
      if (tctx.crucial_stone_mask.Get(d)) {
        in_attention = true;
        break;
      }
    }
  }

  // Fast O(1) path for outer buffer-moat moves (!in_attention) touching no
  // non-immortal tactical stones.
  if (!in_attention) {
    bool touches_tactical_stone = false;
    for (int nb : ortho_nbs) {
      if (pos.StoneAt(nb) != Color::kEmpty && !wall.Get(nb)) {
        touches_tactical_stone = true;
        break;
      }
    }
    if (!touches_tactical_stone) {
      return MoveEvalMeta{-950, false, false, false};
    }
  }

  int32_t score = in_attention ? 150 : -950;
  const Color us = pos.ToPlay();
  const Color enemy = OppositeColor(us);
  const Color opp_target_color = OppositeColor(tctx.target_color);

  // 1. O(1) precomputed proximity to surviving crucial chains & their liberties.
  const int r = move / N;
  const int c = move % N;
  const int dist_r = std::min(r, N - 1 - r);
  const int dist_c = std::min(c, N - 1 - c);
  const int dist_edge = std::min(dist_r, dist_c);

  const int c_libs =
      static_cast<int>(tctx.crucial_lib_min_libs[static_cast<size_t>(move)]);
  if (c_libs < 99) {
    if (c_libs == 1) score += 1750;
    else if (c_libs == 2) score += 1080;
    else if (c_libs <= 4 || dist_edge <= 2) score += 480;
    else score += 220;
  }
  int adj_crucial_count = 0;
  for (int nb : ortho_nbs) {
    if (tctx.crucial_stone_mask.Get(nb)) ++adj_crucial_count;
  }
  if (adj_crucial_count >= 2) score += 580;

  // Pre-move neighbor chain inspection (O(1) via NodeTacticalContext).
  bool tightened_low_lib_enemy = false;
  bool tightened_cutting_enemy = false;
  int min_enemy_lib_before = 99;
  int friendly_ortho_count = 0;
  int enemy_ortho_count = 0;
  bool has_tactical_friendly_adj = false;
  int16_t first_friendly_cid = -1;
  bool connects_distinct_friendly = false;
  int empty_ortho_count = 0;
  int target_ortho_count = 0;
  int opp_target_ortho_count = 0;

  for (int nb : ortho_nbs) {
    const Color st = pos.StoneAt(nb);
    if (st == Color::kEmpty) {
      ++empty_ortho_count;
    } else if (st == us) {
      ++friendly_ortho_count;
      const int16_t fcid = tctx.chain_id_at[static_cast<size_t>(nb)];
      if (fcid >= 0) {
        const size_t ufcid = static_cast<size_t>(fcid);
        if (!tctx.chain_is_immortal[ufcid]) {
          has_tactical_friendly_adj = true;
        }
        if (tctx.chain_libs[ufcid] >= 2) {
          if (first_friendly_cid == -1) first_friendly_cid = fcid;
          else if (first_friendly_cid != fcid) connects_distinct_friendly = true;
        }
      }
    } else if (st == enemy) {
      ++enemy_ortho_count;
      const int16_t ecid = tctx.chain_id_at[static_cast<size_t>(nb)];
      if (ecid >= 0) {
        const size_t uecid = static_cast<size_t>(ecid);
        if (!tctx.chain_is_immortal[uecid]) {
          const int elibs = static_cast<int>(tctx.chain_libs[uecid]);
          if (elibs < min_enemy_lib_before) min_enemy_lib_before = elibs;
          if (elibs <= 3) {
            tightened_low_lib_enemy = true;
            if (tctx.chain_is_cutting_enemy[uecid]) {
              tightened_cutting_enemy = true;
            }
          }
        }
      }
    }
    if (st == tctx.target_color) ++target_ortho_count;
    else if (st == opp_target_color) ++opp_target_ortho_count;
  }

  // 2. Simulate move on probe for fast capture, crucial-token, & liberty checks.
  Position<N> probe = pos;
  const int prev_enemy_count = pos.Stones(enemy).Count();
  if (!probe.PlayMove(move)) {
    return MoveEvalMeta{-99999, false, false, false};
  }
  const int captured_count = prev_enemy_count - probe.Stones(enemy).Count();

  if (captured_count > 0) {
    score += 1300 + captured_count * 320;
    bool all_crucial_gone = false;
    if (!context.initial_tokens.empty()) {
      if (context.crucial_stone_op == LogicalOp::kConjunction) {
        for (size_t idx = 0; idx < context.initial_tokens.size() && idx < 64U;
             ++idx) {
          if ((probe.SurvivingTargetTokensMask() & (1ULL << idx)) == 0ULL) {
            all_crucial_gone = true;
            break;
          }
        }
      } else {
        all_crucial_gone = true;
        for (size_t idx = 0; idx < context.initial_tokens.size() && idx < 64U;
             ++idx) {
          if ((probe.SurvivingTargetTokensMask() & (1ULL << idx)) != 0ULL) {
            all_crucial_gone = false;
            break;
          }
        }
      }
    }
    if (all_crucial_gone) {
      const bool tok_cap_is_win = (context.attacker_goal == SearchGoal::kToKill);
      if (is_or_node && tok_cap_is_win) {
        return MoveEvalMeta{55000, true, false, true};
      }
      if (!is_or_node && !tok_cap_is_win) {
        return MoveEvalMeta{55000, false, true, true};
      }
    }
  }

  BitBoard<N> our_libs_bb;
  (void)probe.FloodFillChain(move, &our_libs_bb);
  const int our_libs_cnt = our_libs_bb.Count();
  if (our_libs_cnt == 1) {
    bool is_tesuji_throw_in = false;
    if (captured_count == 0 && in_attention) {
      const std::vector<int> sole_libs = our_libs_bb.ToCoords();
      if (!sole_libs.empty()) {
        const int sole_lib = sole_libs[0];
        Position<N> cap_probe = probe;
        if (cap_probe.PlayMove(static_cast<int16_t>(sole_lib))) {
          BitBoard<N> enemy_after_libs;
          (void)cap_probe.FloodFillChain(sole_lib, &enemy_after_libs);
          if (enemy_after_libs.Count() <= 2) {
            is_tesuji_throw_in = true;
          }
        }
      }
    }
    if (is_tesuji_throw_in) {
      score += 780;
    } else {
      bool adj_stone = false;
      for (int nb : ortho_nbs) {
        if (probe.StoneAt(nb) != Color::kEmpty) {
          adj_stone = true;
          break;
        }
      }
      score += adj_stone ? -240 : -780;
    }
  } else if (our_libs_cnt >= 3) {
    score += 240;
  }

  if (tightened_low_lib_enemy && our_libs_cnt >= 2) {
    score += tightened_cutting_enemy ? 740 : 380;
  }

  if (enemy_ortho_count > 0) {
    for (int nb : ortho_nbs) {
      if (probe.StoneAt(nb) == enemy && !wall.Get(nb)) {
        BitBoard<N> enemy_libs_bb;
        (void)probe.FloodFillChain(nb, &enemy_libs_bb);
        const int elibs = enemy_libs_bb.Count();
        if (elibs == 1) {
          score += 740;
        } else if (elibs == 2 && elibs < min_enemy_lib_before) {
          score += 340;
        }
      }
    }
  }

  // 3. Corner / Edge & Symmetric Eye-Vitality Geometry Heuristics.
  if (dist_r == 1 && dist_c == 1) {
    score += 560;
  } else if (dist_edge == 1) {
    score += 300;
  } else if (dist_edge == 0) {
    score += 260;
  }

  if (connects_distinct_friendly && has_tactical_friendly_adj) {
    score += 820;
  }

  int friendly_diag_count = 0;
  int enemy_diag_count = 0;
  int target_diag_count = 0;
  for (int d : diag_nbs) {
    const Color st = pos.StoneAt(d);
    if (st == us) ++friendly_diag_count;
    else if (st == enemy) ++enemy_diag_count;
    if (st == tctx.target_color) ++target_diag_count;
  }

  bool splits_eye_cavity = false;
  if (empty_ortho_count >= 2 && in_attention) {
    for (size_t i = 0; i < ortho_nbs.size() && !splits_eye_cavity; ++i) {
      const int a = ortho_nbs[i];
      if (pos.StoneAt(a) != Color::kEmpty) continue;
      const auto a_nbs = pos.OrthogonalNeighbors(a);
      for (size_t j = i + 1U; j < ortho_nbs.size(); ++j) {
        const int b = ortho_nbs[j];
        if (pos.StoneAt(b) != Color::kEmpty) continue;
        const auto b_nbs = pos.OrthogonalNeighbors(b);
        bool shared_empty = false;
        for (int cand : a_nbs) {
          if (cand != move && pos.StoneAt(cand) == Color::kEmpty &&
              std::find(b_nbs.begin(), b_nbs.end(), cand) != b_nbs.end()) {
            shared_empty = true;
            break;
          }
        }
        if (!shared_empty) {
          splits_eye_cavity = true;
          break;
        }
      }
    }
    if (splits_eye_cavity &&
        (friendly_ortho_count >= 1 || enemy_ortho_count >= 1 ||
         friendly_diag_count >= 2 || enemy_diag_count >= 2)) {
      score += 960;
    }
  }

  // Calm eye-making / eye-destroying vital point along target's 1st/2nd line.
  if (in_attention && our_libs_cnt >= 2 && dist_edge <= 1 &&
      (target_diag_count >= 1 || target_ortho_count >= 1)) {
    int enclosed_edge_pockets = 0;
    for (int enb : ortho_nbs) {
      if (pos.StoneAt(enb) != Color::kEmpty) continue;
      const auto enb_nbs = pos.OrthogonalNeighbors(enb);
      int target_walls = 0;
      for (int nn : enb_nbs) {
        if (nn == move || pos.StoneAt(nn) == tctx.target_color) {
          ++target_walls;
        }
      }
      if (target_walls >= static_cast<int>(enb_nbs.size()) - 1) {
        ++enclosed_edge_pockets;
      }
    }
    if (enclosed_edge_pockets >= 1) {
      score += 480 + (enclosed_edge_pockets >= 2 ? 360 : 0);
    } else if (dist_edge == 0 && empty_ortho_count >= 1 &&
               (target_ortho_count >= 1 || opp_target_ortho_count >= 1)) {
      score += 340;
    }
  }

  if (friendly_diag_count >= 2 && enemy_ortho_count == 0 &&
      (friendly_ortho_count == 0 || connects_distinct_friendly ||
       enemy_diag_count >= 1)) {
    score += 520;
    for (int enb : ortho_nbs) {
      if (pos.StoneAt(enb) == Color::kEmpty) {
        const auto enb_nbs = pos.OrthogonalNeighbors(enb);
        int enb_friendly_walls = 0;
        for (int n : enb_nbs) {
          if (n == move || pos.StoneAt(n) == us) ++enb_friendly_walls;
        }
        if (enb_friendly_walls >= 3) {
          score += 620;
        }
      }
    }
  } else if (enemy_diag_count >= 2 && friendly_ortho_count == 0 &&
             our_libs_cnt >= 2 && in_attention) {
    score += 560;
  } else if (empty_ortho_count <= 1 && friendly_ortho_count >= 1 &&
             !connects_distinct_friendly && friendly_diag_count >= 2 &&
             enemy_ortho_count == 0 && enemy_diag_count == 0) {
    score -= 340;
  }

  if (friendly_ortho_count >= 1 && enemy_ortho_count >= 1) score += 340;
  if (friendly_ortho_count >= 1 && enemy_diag_count >= 1) score += 290;

  // 4. Exact post-move single-point true-eye count, crucial-chain liberty-delta,
  // and immediate 1-ply Benson UCA detection.
  int post_true_eyes = 0;
  if (in_attention && our_libs_cnt >= 2) {
    for (int ep : ortho_nbs) {
      if (probe.StoneAt(ep) != Color::kEmpty) continue;
      const auto ep_ortho = probe.OrthogonalNeighbors(ep);
      bool all_target = true;
      for (int nb : ep_ortho) {
        if (probe.StoneAt(nb) != tctx.target_color) {
          all_target = false;
          break;
        }
      }
      if (!all_target) continue;
      const auto ep_diag = probe.DiagonalNeighbors(ep);
      int enemy_diags = 0;
      for (int d : ep_diag) {
        if (probe.StoneAt(d) == opp_target_color) ++enemy_diags;
      }
      const int max_enemy_diags = (ep_diag.size() == 4U) ? 1 : 0;
      if (enemy_diags <= max_enemy_diags) {
        ++post_true_eyes;
      }
    }
    if (post_true_eyes > 0) {
      score += post_true_eyes * 680;
    }

    // 4b. Crucial-chain liberty-delta heuristic (O(1), zero extra flood-fill).
    if (c_libs < 99 && us == tctx.target_color) {
      const int lib_delta = our_libs_cnt - c_libs;
      if (lib_delta >= 2) {
        score += 560;
      } else if (lib_delta == 1) {
        score += 260;
      } else if (lib_delta < 0 && captured_count == 0 && post_true_eyes == 0 &&
                 !splits_eye_cavity && !connects_distinct_friendly) {
        score -= 220;
      }
    }

    if (is_or_node && context.attacker_goal == SearchGoal::kToLive &&
        (post_true_eyes > 0 || captured_count > 0 || score >= 2200)) {
      const auto term = terminal_eval_.EvaluateTerminal(probe, context);
      if (term.status == TerminalStatus::kWin) {
        return MoveEvalMeta{58000, true, false, true};
      }
    }
  }

  return MoveEvalMeta{score, false, false, in_attention};
}

template <int N>
std::pair<uint32_t, uint32_t> DfpnSolver<N>::ComputeInitialChildBounds(
    size_t rank_idx, bool is_or_node, const MoveEvalMeta& meta,
    int16_t move) const noexcept {
  if (!config_.enable_fast_capture_ordering) {
    return {1U, 1U};
  }
  const uint32_t r = static_cast<uint32_t>(rank_idx);
  if (is_or_node) {
    if (meta.immediate_win) return {1U, 10U};
    if (meta.immediate_loss) return {180U, 1U};
    if (move == kPassMove) return {220U, 1U};
    if (!meta.in_attention) return {2400U + r * 16U, 1U};
    uint32_t pn = 1U;
    if (r == 0U) pn = 1U;
    else if (r == 1U) pn = 4U;
    else if (r == 2U) pn = 8U;
    else if (r <= 5U) pn = 12U + (r - 3U) * 4U;
    else if (r <= 10U) pn = 24U + (r - 5U) * 5U;
    else pn = 50U + (r - 10U) * 6U;
    if (meta.score < 0) pn += 24U;
    return {pn, 1U};
  } else {
    if (meta.immediate_loss) return {10U, 1U};
    if (move == kPassMove) {
      if (r == 0U) return {1U, 1U};
      return meta.score >= 3400 ? std::pair<uint32_t, uint32_t>{1U, 3U}
                                : std::pair<uint32_t, uint32_t>{1U, 5U};
    }
    if (!meta.in_attention) return {1U, 96U + r * 4U};
    uint32_t dn = 1U;
    if (r == 0U) dn = 1U;
    else if (r == 1U) dn = 4U;
    else if (r == 2U) dn = 8U;
    else if (r <= 5U) dn = 12U + (r - 3U) * 4U;
    else if (r <= 10U) dn = 24U + (r - 5U) * 5U;
    else dn = 50U + (r - 10U) * 6U;
    if (meta.score < 0) dn += 16U;
    return {1U, dn};
  }
}

template <int N>
bool DfpnSolver<N>::RevalidateSourceProofOnQueryState(
    const Position<N>& query_pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint,
    uint32_t source_dag_node_id, ProofOutcome expected_outcome,
    uint32_t guard_depth) const {
  if (guard_depth > 48 || source_dag_node_id >= report_.proof_dag_nodes.size()) {
    return false;
  }

  uint32_t resolved_id = source_dag_node_id;
  for (int hop = 0; hop < 32 && resolved_id < report_.proof_dag_nodes.size();
       ++hop) {
    const auto& cur = report_.proof_dag_nodes[resolved_id];
    if (!cur.is_pruned_outside_rz && !cur.is_tt_hit) break;
    if (cur.source_proof_node_id >= cur.node_id) return false;
    resolved_id = cur.source_proof_node_id;
  }
  if (resolved_id >= report_.proof_dag_nodes.size()) return false;
  const auto& node = report_.proof_dag_nodes[resolved_id];
  if (node.outcome != expected_outcome) return false;

  // Memoize revalidation per exact semantic query state + history + source DAG.
  std::string cache_key;
  cache_key.reserve(96);
  cache_key.append(HexU64Compact(query_pos.ZobristHash()));
  cache_key.push_back(':');
  cache_key.push_back(query_pos.ToPlay() == Color::kWhite ? 'W' : 'B');
  cache_key.push_back(':');
  cache_key.append(std::to_string(query_pos.KoPoint()));
  cache_key.push_back(':');
  cache_key.append(std::to_string(query_pos.ConsecutivePasses()));
  cache_key.push_back(':');
  cache_key.append(HexU64Compact(query_pos.SurvivingTargetTokensMask()));
  cache_key.push_back(':');
  if (query_pos.IsCaptureFreeMonotonicHistory()) {
    cache_key.push_back('M');
  } else {
    cache_key.append(query_pos.ComputeCanonicalHistoryKey());
  }
  cache_key.push_back(':');
  cache_key.append(std::to_string(resolved_id));
  cache_key.push_back(':');
  cache_key.push_back(
      expected_outcome == ProofOutcome::kProvenWin ? 'W' : 'L');

  if (const auto it = reval_cache_.find(cache_key); it != reval_cache_.end()) {
    return it->second;
  }

  auto finish = [&](bool result) -> bool {
    if (reval_cache_.size() < 200000U) {
      reval_cache_.emplace(std::move(cache_key), result);
    }
    return result;
  };

  const auto term = terminal_eval_.EvaluateTerminal(query_pos, context);
  if (term.status == TerminalStatus::kWin) {
    return finish(expected_outcome == ProofOutcome::kProvenWin);
  }
  if (term.status == TerminalStatus::kLoss) {
    return finish(expected_outcome == ProofOutcome::kProvenLoss);
  }

  if (node.child_node_ids.empty()) return finish(false);
  const bool is_or = (query_pos.ToPlay() == context.root_attacker);
  const bool restricted_side =
      (query_pos.ToPlay() == context.root_attacker &&
       !context.attacker_allow_ko) ||
      (query_pos.ToPlay() != context.root_attacker &&
       !context.defender_allow_ko);

  // Case 1: Single-witness node (OR -> ProvenWin, or AND -> ProvenLoss)
  if ((is_or && expected_outcome == ProofOutcome::kProvenWin) ||
      (!is_or && expected_outcome == ProofOutcome::kProvenLoss)) {
    for (size_t i = 0; i < node.child_node_ids.size(); ++i) {
      const uint32_t cid = node.child_node_ids[i];
      if (cid >= report_.proof_dag_nodes.size() ||
          report_.proof_dag_nodes[cid].outcome != expected_outcome) {
        continue;
      }
      const int16_t mv = node.child_moves[i];
      if (mv != kPassMove && region_hint.has_value() &&
          (mv < 0 || mv >= N * N || !region_hint->Get(mv))) {
        continue;
      }
      Position<N> next = query_pos;
      bool is_ko_cap = false;
      if (!next.PlayMove(mv, &is_ko_cap)) continue;
      if (is_ko_cap && restricted_side) continue;
      if (RevalidateSourceProofOnQueryState(
              next, context, region_hint, cid, expected_outcome,
              guard_depth + 1U)) {
        return finish(true);
      }
    }
    return finish(false);
  }

  // Case 2: Full-coverage node (AND -> ProvenWin, or OR -> ProvenLoss).
  // Every legal move on `query_pos` must exist in `node` and replay cleanly!
  const auto query_legal = query_pos.GenerateLegalMoves(region_hint);
  for (int16_t mv : query_legal) {
    int found_idx = -1;
    for (size_t i = 0; i < node.child_moves.size(); ++i) {
      if (node.child_moves[i] == mv) {
        found_idx = static_cast<int>(i);
        break;
      }
    }
    if (found_idx < 0) return finish(false);
    const uint32_t cid = node.child_node_ids[static_cast<size_t>(found_idx)];
    if (cid >= report_.proof_dag_nodes.size() ||
        report_.proof_dag_nodes[cid].outcome != expected_outcome) {
      return finish(false);
    }
    Position<N> next = query_pos;
    if (!next.PlayMove(mv)) return finish(false);
    if (!RevalidateSourceProofOnQueryState(
            next, context, region_hint, cid, expected_outcome,
            guard_depth + 1U)) {
      return finish(false);
    }
  }
  return finish(true);
}

template <int N>
void DfpnSolver<N>::MidSearch(
    Position<N>& pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint, uint32_t th_pn,
    uint32_t th_dn, uint32_t depth, uint64_t node_path_id,
    std::unordered_set<uint64_t>& in_path_hashes, uint32_t* out_pn,
    uint32_t* out_dn, ProofOutcome* out_outcome, bool* out_ko_dependent,
    bool* out_has_capture, ProofCertificateRZ<N>* out_proof_rz,
    ProofCertificateRZ<N>* out_disproof_rz, uint32_t* out_dag_node_id,
    int16_t incoming_move) {
  ++report_.num_nodes;
  *out_ko_dependent = false;
  *out_has_capture = false;
  *out_dag_node_id = kInvalidDagNodeId;
  const bool is_or_node = (pos.ToPlay() == context.root_attacker);

  // Step 1 (FR-3.2, FR-3.8): Evaluate Terminal BEFORE InPath cycle detection.
  const TerminalEvaluationResult<N> term =
      terminal_eval_.EvaluateTerminal(pos, context);
  if (term.status == TerminalStatus::kWin ||
      term.status == TerminalStatus::kLoss) {
    const bool is_win = (term.status == TerminalStatus::kWin);
    *out_pn = is_win ? 0 : kPnDnSaturation;
    *out_dn = is_win ? kPnDnSaturation : 0;
    *out_outcome = is_win ? ProofOutcome::kProvenWin : ProofOutcome::kProvenLoss;
    *out_has_capture = false;
    if (is_win) {
      *out_proof_rz = ProofCertificateRZ<N>(term.leaf_certificate_rz);
    } else {
      *out_disproof_rz = ProofCertificateRZ<N>(term.leaf_certificate_rz);
    }

    ProofDagNode<N> dag_node;
    dag_node.node_id = static_cast<uint32_t>(report_.proof_dag_nodes.size());
    dag_node.is_or_node = is_or_node;
    dag_node.to_play = pos.ToPlay();
    dag_node.incoming_move = incoming_move;
    dag_node.pn = *out_pn;
    dag_node.dn = *out_dn;
    dag_node.outcome = *out_outcome;
    dag_node.terminal_evidence = term.evidence_kind;
    dag_node.proof_rz = *out_proof_rz;
    dag_node.disproof_rz = *out_disproof_rz;
    report_.proof_dag_nodes.push_back(dag_node);
    dag_has_capture_.push_back(false);
    *out_dag_node_id = dag_node.node_id;
    return;
  }

  // Step 2 (FR-4.5): Conservative InPath cycle guard.
  if (in_path_hashes.find(pos.ZobristHash()) != in_path_hashes.end()) {
    ++report_.cycle_detections;
    *out_pn = 1;
    *out_dn = 1;
    *out_outcome = ProofOutcome::kUnknown;
    if (report_.unknown_reason == UnknownReason::kNone) {
      report_.unknown_reason = UnknownReason::kCycle;
    }
    return;
  }

  // Step 3 (FR-4.7): Resource & depth guardrails.
  if (depth >= config_.max_depth) {
    report_.resource_exhausted = true;
    report_.unknown_reason = UnknownReason::kDepthLimit;
    *out_pn = 1;
    *out_dn = 1;
    *out_outcome = ProofOutcome::kUnknown;
    return;
  }
  if (report_.num_nodes >= config_.max_nodes) {
    report_.resource_exhausted = true;
    report_.unknown_reason = UnknownReason::kNodeLimit;
    *out_pn = 1;
    *out_dn = 1;
    *out_outcome = ProofOutcome::kUnknown;
    return;
  }
  if (IsMemoryBudgetExceeded(depth)) {
    report_.resource_exhausted = true;
    report_.unknown_reason = UnknownReason::kMemoryBudget;
    *out_pn = 1;
    *out_dn = 1;
    *out_outcome = ProofOutcome::kUnknown;
    return;
  }

  auto emit_tt_hit_node = [&](uint32_t src_dag_id, uint32_t pn, uint32_t dn,
                              ProofOutcome outcome,
                              const ProofCertificateRZ<N>& p_rz,
                              const ProofCertificateRZ<N>& d_rz,
                              bool inherited_capture) {
    ProofDagNode<N> tt_node;
    tt_node.node_id = static_cast<uint32_t>(report_.proof_dag_nodes.size());
    tt_node.is_or_node = is_or_node;
    tt_node.to_play = pos.ToPlay();
    tt_node.incoming_move = incoming_move;
    tt_node.pn = pn;
    tt_node.dn = dn;
    tt_node.outcome = outcome;
    tt_node.is_tt_hit = true;
    tt_node.source_proof_node_id = src_dag_id;
    tt_node.proof_rz = p_rz;
    tt_node.disproof_rz = d_rz;
    report_.proof_dag_nodes.push_back(tt_node);
    dag_has_capture_.push_back(inherited_capture);
    return tt_node.node_id;
  };

  auto reval_cb = [&](uint32_t src_id, ProofOutcome expected_out) -> bool {
    return RevalidateSourceProofOnQueryState(pos, context, region_hint, src_id,
                                             expected_out);
  };

  // Step 4 (FR-6.1, FR-6.3, FR-6.9): History-safe BoardTT & PatternTT lookup.
  if (auto hit = tt_store_.LookupBoardTT(pos, context, reval_cb);
      hit.has_value()) {
    if (hit->outcome != ProofOutcome::kUnknown &&
        hit->proof_closure_available &&
        hit->proof_dag_node_id < report_.proof_dag_nodes.size()) {
      const bool inh_cap =
          hit->has_capture_in_subtree ||
          (hit->proof_dag_node_id < dag_has_capture_.size() &&
           dag_has_capture_[hit->proof_dag_node_id]);
      *out_pn = hit->pn;
      *out_dn = hit->dn;
      *out_outcome = hit->outcome;
      *out_has_capture = inh_cap;
      *out_proof_rz = hit->proof_rz;
      *out_disproof_rz = hit->disproof_rz;
      *out_dag_node_id = emit_tt_hit_node(
          hit->proof_dag_node_id, hit->pn, hit->dn, hit->outcome,
          hit->proof_rz, hit->disproof_rz, inh_cap);
      return;
    }
  }

  if (config_.enable_pattern_tt) {
    RadixPatternRecord<N> pat_rec;
    const PatternHitGrade grade =
        tt_store_.LookupPatternTT(pos, context, &pat_rec, reval_cb);
    if (grade == PatternHitGrade::kProofReusable &&
        pat_rec.proof_dag_node_id < report_.proof_dag_nodes.size()) {
      const bool inh_cap =
          pat_rec.has_capture_in_subtree ||
          (pat_rec.proof_dag_node_id < dag_has_capture_.size() &&
           dag_has_capture_[pat_rec.proof_dag_node_id]);
      *out_pn = pat_rec.pn;
      *out_dn = pat_rec.dn;
      *out_outcome = pat_rec.outcome;
      *out_has_capture = inh_cap;
      *out_proof_rz = pat_rec.stored_rz;
      *out_disproof_rz = pat_rec.stored_rz;
      *out_dag_node_id = emit_tt_hit_node(
          pat_rec.proof_dag_node_id, pat_rec.pn, pat_rec.dn, pat_rec.outcome,
          pat_rec.stored_rz, pat_rec.stored_rz, inh_cap);
      return;
    }
  }

  // Step 5: Retrieve or initialize persistent CachedNodeFrontier for this exact
  // search-tree path node so threshold cutoffs preserve child (pn, dn) and RZ!
  auto frontier_it = node_frontier_cache_.find(node_path_id);
  if (frontier_it == node_frontier_cache_.end()) {
    CachedNodeFrontier fresh;
    const int parent_eye_like_count =
        (!is_or_node && pos.ConsecutivePasses() == 0 &&
         config_.enable_fast_capture_ordering)
            ? EstimateParentEyeLikeCount(pos, context)
            : 0;
    const NodeTacticalContext tctx =
        config_.enable_fast_capture_ordering
            ? BuildNodeTacticalContext(pos, context)
            : NodeTacticalContext{};
    std::vector<int16_t> legal_moves = pos.GenerateLegalMoves(region_hint);

    std::vector<std::pair<int16_t, MoveEvalMeta>> scored;
    scored.reserve(legal_moves.size());
    for (int16_t mv : legal_moves) {
      MoveEvalMeta meta;
      if (config_.enable_fast_capture_ordering) {
        meta = EvaluateCandidateMove(pos, context, tctx, mv, is_or_node,
                                     parent_eye_like_count);
      }
      scored.emplace_back(mv, meta);
    }
    if (config_.enable_fast_capture_ordering) {
      std::stable_sort(
          scored.begin(), scored.end(),
          [](const std::pair<int16_t, MoveEvalMeta>& a,
             const std::pair<int16_t, MoveEvalMeta>& b) {
            return a.second.score > b.second.score;
          });
    }

    fresh.children.reserve(scored.size());
    for (size_t idx = 0; idx < scored.size(); ++idx) {
      const int16_t mv = scored[idx].first;
      const MoveEvalMeta& meta = scored[idx].second;
      const auto init_bounds =
          ComputeInitialChildBounds(idx, is_or_node, meta, mv);
      SearchChild ch;
      ch.move = mv;
      ch.child_path_id = next_path_id_++;
      ch.tactical_score = meta.score;
      ch.pn = init_bounds.first;
      ch.dn = init_bounds.second;
      fresh.children.push_back(ch);
    }
    node_frontier_cache_.emplace(node_path_id, std::move(fresh));
  }

  in_path_hashes.insert(pos.ZobristHash());

  while (true) {
    CachedNodeFrontier& frontier = node_frontier_cache_.at(node_path_id);
    auto& children = frontier.children;
    const size_t total_legal = children.size();

    size_t window_size = total_legal;
    if (config_.enable_progressive_widening && frontier.widening_level < 6U) {
      const size_t base_k =
          is_or_node
              ? std::min<size_t>(static_cast<size_t>(config_.widening_base_k),
                                 depth == 0U ? 4U : 3U)
              : std::min<size_t>(
                    std::max<size_t>(
                        2U, static_cast<size_t>(config_.widening_base_k) / 2U),
                    3U);
      const size_t cap = base_k << frontier.widening_level;
      if (cap < total_legal) window_size = cap;
    }

    const bool has_active_rz =
        config_.enable_rz_pruning && frontier.has_null_move_rz &&
        frontier.representative_dag_id != kInvalidDagNodeId;
    const bool restricted_side =
        (pos.ToPlay() == context.root_attacker &&
         !context.attacker_allow_ko) ||
        (pos.ToPlay() != context.root_attacker &&
         !context.defender_allow_ko);
    const bool rep_has_cap =
        has_active_rz &&
        frontier.representative_dag_id < dag_has_capture_.size() &&
        dag_has_capture_[frontier.representative_dag_id];
    const int prev_opp_cnt =
        pos.Stones(OppositeColor(pos.ToPlay())).Count();

    // FR-5.5: Helper to run zero-trust OutsideRZRevalidated revalidation on a
    // single candidate child (per-child stamp avoids repeated failed checks).
    auto try_prune_child_outside_rz = [&](SearchChild& ch) -> bool {
      if (!has_active_rz || ch.probed || ch.has_decisive_dag ||
          ch.outcome != ProofOutcome::kUnknown ||
          ch.checked_null_move_dag_id == frontier.representative_dag_id) {
        return false;
      }
      ch.checked_null_move_dag_id = frontier.representative_dag_id;
      if (!rz_engine_.IsOutsideRZCandidate(ch.move,
                                           frontier.active_null_move_rz)) {
        return false;
      }
      Position<N> next_pos = pos;
      bool is_ko_cap = false;
      if (!next_pos.PlayMove(ch.move, &is_ko_cap) ||
          (is_ko_cap && restricted_side) ||
          !RevalidateSourceProofOnQueryState(
              next_pos, context, region_hint, frontier.representative_dag_id,
              frontier.representative_outcome)) {
        return false;
      }
      const bool did_cap =
          next_pos.Stones(OppositeColor(pos.ToPlay())).Count() < prev_opp_cnt;
      ProofDagNode<N> pruned_node;
      pruned_node.node_id =
          static_cast<uint32_t>(report_.proof_dag_nodes.size());
      pruned_node.is_or_node = !is_or_node;
      pruned_node.to_play = next_pos.ToPlay();
      pruned_node.incoming_move = ch.move;
      pruned_node.pn =
          (frontier.representative_outcome == ProofOutcome::kProvenWin)
              ? 0
              : kPnDnSaturation;
      pruned_node.dn =
          (frontier.representative_outcome == ProofOutcome::kProvenWin)
              ? kPnDnSaturation
              : 0;
      pruned_node.outcome = frontier.representative_outcome;
      pruned_node.is_pruned_outside_rz = true;
      pruned_node.source_proof_node_id = frontier.representative_dag_id;
      pruned_node.proof_rz = frontier.active_null_move_rz;
      pruned_node.disproof_rz = frontier.active_null_move_rz;
      report_.proof_dag_nodes.push_back(pruned_node);
      dag_has_capture_.push_back(did_cap || rep_has_cap);

      ch.probed = true;
      ch.has_decisive_dag = true;
      ch.pruned_outside_rz = true;
      ch.move_captured = did_cap;
      ch.subtree_has_capture = rep_has_cap;
      ch.outcome = frontier.representative_outcome;
      ch.pn = pruned_node.pn;
      ch.dn = pruned_node.dn;
      ch.proof_rz = frontier.active_null_move_rz;
      ch.disproof_rz = frontier.active_null_move_rz;
      ch.dag_node_id = pruned_node.node_id;
      ++report_.pruned_outside_rz_count;
      return true;
    };

    // O(1) lazy outside-RZ predicate: an unprobed Unknown move strictly outside
    // `active_null_move_rz` that has not failed revalidation is deferred until
    // all in-RZ moves close (avoiding wasted DAG pushes on refuted internal
    // nodes and artificial widen_trigger throttling from outer-moat moves).
    auto is_lazy_outside_rz = [&](const SearchChild& ch) -> bool {
      return has_active_rz && !ch.probed && !ch.has_decisive_dag &&
             ch.outcome == ProofOutcome::kUnknown &&
             ch.checked_null_move_dag_id != frontier.representative_dag_id &&
             rz_engine_.IsOutsideRZCandidate(ch.move,
                                             frontier.active_null_move_rz);
    };

    std::vector<size_t> active_indices;
    active_indices.reserve(total_legal);
    size_t lazy_outside_count = 0;
    size_t unexpanded_u = 0;
    int first_unexpanded_idx = -1;
    uint32_t outside_witness_metric = kPnDnSaturation;

    if (has_active_rz) {
      for (size_t i = 0; i < total_legal; ++i) {
        if (is_lazy_outside_rz(children[i])) {
          ++lazy_outside_count;
        } else {
          active_indices.push_back(i);
        }
      }
    } else {
      for (size_t i = 0; i < window_size; ++i) {
        active_indices.push_back(i);
      }
      for (size_t i = window_size; i < total_legal; ++i) {
        const auto& ch = children[i];
        if (is_or_node) {
          if (ch.pn == 0 && ch.outcome == ProofOutcome::kProvenWin &&
              !ch.ko_dependent && ch.has_decisive_dag) {
            outside_witness_metric = 0;
          }
          if (ch.dn > 0 || ch.outcome != ProofOutcome::kProvenLoss ||
              !ch.has_decisive_dag) {
            ++unexpanded_u;
            if (first_unexpanded_idx < 0) {
              first_unexpanded_idx = static_cast<int>(i);
            }
          }
        } else {
          if (ch.dn == 0 && ch.outcome == ProofOutcome::kProvenLoss &&
              !ch.ko_dependent && ch.has_decisive_dag) {
            outside_witness_metric = 0;
          }
          if (ch.pn > 0 || ch.outcome != ProofOutcome::kProvenWin ||
              !ch.has_decisive_dag) {
            ++unexpanded_u;
            if (first_unexpanded_idx < 0) {
              first_unexpanded_idx = static_cast<int>(i);
            }
          }
        }
      }
      if (unexpanded_u == 0 && window_size < total_legal) {
        for (size_t i = window_size; i < total_legal; ++i) {
          active_indices.push_back(i);
        }
        window_size = total_legal;
      }
    }

    // FR-4.1: Frontier PN/DN aggregation without breadth-exploding sum inflation.
    const uint32_t widen_trigger =
        (unexpanded_u > 0 && first_unexpanded_idx >= 0)
            ? std::max(
                  is_or_node
                      ? children[static_cast<size_t>(first_unexpanded_idx)].pn
                      : children[static_cast<size_t>(first_unexpanded_idx)].dn,
                  (is_or_node ? 20U : 16U) * (frontier.widening_level + 1U))
            : kPnDnSaturation;
    uint32_t cur_pn = 1;
    uint32_t cur_dn = 1;
    int force_expand_pass_idx = -1;

    if (is_or_node) {
      uint32_t min_pn = outside_witness_metric;
      uint64_t sum_dn = 0;
      for (size_t idx : active_indices) {
        min_pn = std::min(min_pn, children[idx].pn);
        sum_dn += children[idx].dn;
      }
      if (has_active_rz && min_pn >= 48U && min_pn < kPnDnSaturation) {
        // High-cost unexpanded in-RZ JIT relaxation: once all sharp (< 48) in-RZ
        // candidates have closed or exceeded 48, relax remaining unexpanded
        // high-cost in-RZ moves (both !in_attention and low-ranked in-attention
        // candidates) to pn=8 so stale initial bounds do not stall closure.
        bool relaxed = false;
        for (size_t idx : active_indices) {
          auto& ch = children[idx];
          if (!ch.probed && ch.outcome == ProofOutcome::kUnknown &&
              !ch.ko_dependent && ch.pn >= 48U) {
            ch.pn = 8U;
            relaxed = true;
          }
        }
        if (relaxed) continue;
      }
      if (unexpanded_u > 0) {
        min_pn = std::min(min_pn, widen_trigger);
      }
      if (min_pn > 0 && sum_dn == 0 && lazy_outside_count > 0) {
        for (size_t i = 0; i < total_legal; ++i) {
          if (is_lazy_outside_rz(children[i])) {
            try_prune_child_outside_rz(children[i]);
          }
        }
        continue;
      }
      if (min_pn > 0 && sum_dn == 0 && unexpanded_u > 0) {
        ++frontier.widening_level;
        ++report_.widening_upgrades;
        continue;
      }
      cur_pn = min_pn;
      cur_dn = ClampSat(
          sum_dn + ((unexpanded_u > 0 || lazy_outside_count > 0) ? 1ULL : 0ULL));
    } else {
      uint64_t sum_pn = 0;
      uint32_t min_dn = outside_witness_metric;
      for (size_t idx : active_indices) {
        sum_pn += children[idx].pn;
        min_dn = std::min(min_dn, children[idx].dn);
      }
      if (has_active_rz && min_dn >= 48U && min_dn < kPnDnSaturation) {
        // High-cost unexpanded in-RZ JIT relaxation: once all sharp (< 48) in-RZ
        // defenses have closed or exceeded 48, relax remaining unexpanded
        // high-cost in-RZ defenses (both !in_attention and low-ranked
        // in-attention candidates) to dn=4 so stale initial bounds do not spike
        // ancestor dn and bounce out of a nearly closed subtree.
        bool relaxed = false;
        for (size_t idx : active_indices) {
          auto& ch = children[idx];
          if (!ch.probed && ch.outcome == ProofOutcome::kUnknown &&
              !ch.ko_dependent && ch.dn >= 48U) {
            ch.dn = 4U;
            relaxed = true;
          }
        }
        if (relaxed) continue;
      }
      if (unexpanded_u > 0) {
        min_dn = std::min(min_dn, widen_trigger);
      }
      if (min_dn > 0 && sum_pn == 0 && lazy_outside_count > 0) {
        for (size_t i = 0; i < total_legal; ++i) {
          if (is_lazy_outside_rz(children[i])) {
            try_prune_child_outside_rz(children[i]);
          }
        }
        continue;
      }
      if (min_dn > 0 && sum_pn == 0 && unexpanded_u > 0) {
        // Before widening across the full region, probe PASS once if unprobed
        // so active_null_move_rz carries a stone-free tenuki certificate.
        int pass_idx = -1;
        if (config_.enable_rz_pruning && pos.ConsecutivePasses() == 0 &&
            !frontier.pass_probed) {
          for (size_t i = 0; i < total_legal; ++i) {
            if (children[i].move == kPassMove && !children[i].probed &&
                !children[i].ko_dependent &&
                children[i].outcome == ProofOutcome::kUnknown) {
              pass_idx = static_cast<int>(i);
              break;
            }
          }
        }
        if (pass_idx >= 0) {
          force_expand_pass_idx = pass_idx;
          cur_pn = 1U;
          cur_dn = std::max(1U, children[static_cast<size_t>(pass_idx)].dn);
        } else {
          ++frontier.widening_level;
          ++report_.widening_upgrades;
          continue;
        }
      } else {
        cur_pn = ClampSat(
            sum_pn +
            ((unexpanded_u > 0 || lazy_outside_count > 0) ? 1ULL : 0ULL));
        cur_dn = min_dn;
      }
    }

    // Check asymmetric decisive completion conditions (FR-4.2).
    if (cur_pn == 0 || cur_dn == 0) {
      // Full coverage required for OR->Loss (cur_dn == 0) and AND->Win (cur_pn == 0).
      if (((is_or_node && cur_dn == 0) || (!is_or_node && cur_pn == 0)) &&
          (unexpanded_u > 0 || lazy_outside_count > 0)) {
        if (lazy_outside_count > 0) {
          for (size_t i = 0; i < total_legal; ++i) {
            if (is_lazy_outside_rz(children[i])) {
              try_prune_child_outside_rz(children[i]);
            }
          }
        } else {
          ++frontier.widening_level;
          ++report_.widening_upgrades;
        }
        continue;
      }

      const ProofOutcome target_outcome =
          (cur_pn == 0) ? ProofOutcome::kProvenWin : ProofOutcome::kProvenLoss;
      const bool is_existential =
          (is_or_node && cur_pn == 0) || (!is_or_node && cur_dn == 0);

      std::vector<uint32_t> proven_child_ids;
      std::vector<int16_t> proven_child_moves;
      bool node_has_capture = false;

      if (is_existential) {
        int witness_idx = -1;
        for (size_t i = 0; i < children.size(); ++i) {
          const auto& ch = children[i];
          const bool metric_zero = is_or_node ? (ch.pn == 0) : (ch.dn == 0);
          if (metric_zero && ch.outcome == target_outcome && !ch.ko_dependent &&
              ch.dag_node_id != kInvalidDagNodeId &&
              ch.dag_node_id < report_.proof_dag_nodes.size()) {
            witness_idx = static_cast<int>(i);
            break;
          }
        }
        if (witness_idx < 0) {
          *out_pn = 1;
          *out_dn = 1;
          *out_outcome = ProofOutcome::kUnknown;
          *out_dag_node_id = kInvalidDagNodeId;
          break;
        }
        const auto& w = children[static_cast<size_t>(witness_idx)];
        node_has_capture = w.move_captured || w.subtree_has_capture;
        if (is_or_node) {
          *out_proof_rz =
              rz_engine_.ComputeSingleWitnessRZ(pos, w.move, w.proof_rz);
        } else {
          *out_disproof_rz =
              rz_engine_.ComputeSingleWitnessRZ(pos, w.move, w.disproof_rz);
        }
        if (depth == 0) report_.best_move = w.move;
        proven_child_ids.push_back(w.dag_node_id);
        proven_child_moves.push_back(w.move);
      } else {
        bool all_valid = true;
        std::vector<ProofCertificateRZ<N>> child_rzs;
        child_rzs.reserve(children.size());
        proven_child_ids.reserve(children.size());
        proven_child_moves.reserve(children.size());
        for (const auto& ch : children) {
          if (ch.outcome != target_outcome ||
              ch.dag_node_id == kInvalidDagNodeId ||
              ch.dag_node_id >= report_.proof_dag_nodes.size()) {
            all_valid = false;
            break;
          }
          if (ch.move_captured || ch.subtree_has_capture) {
            node_has_capture = true;
          }
          child_rzs.push_back(is_or_node ? ch.disproof_rz : ch.proof_rz);
          proven_child_ids.push_back(ch.dag_node_id);
          proven_child_moves.push_back(ch.move);
        }
        if (!all_valid) {
          *out_pn = 1;
          *out_dn = 1;
          *out_outcome = ProofOutcome::kUnknown;
          *out_dag_node_id = kInvalidDagNodeId;
          break;
        }
        if (is_or_node) {
          *out_disproof_rz =
              rz_engine_.ComputeAllChildrenUnionRZ(pos, child_rzs);
        } else {
          *out_proof_rz = rz_engine_.ComputeAllChildrenUnionRZ(pos, child_rzs);
        }
        // Guarantee a verified root bestMove on universal proven roots (LP-R02).
        if (depth == 0 && !proven_child_moves.empty()) {
          int16_t chosen_mv = proven_child_moves[0];
          for (int16_t mv : proven_child_moves) {
            if (mv != kPassMove) {
              chosen_mv = mv;
              break;
            }
          }
          report_.best_move = chosen_mv;
        }
      }

      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = target_outcome;
      *out_has_capture = node_has_capture;

      ProofDagNode<N> dag_node;
      dag_node.node_id = static_cast<uint32_t>(report_.proof_dag_nodes.size());
      dag_node.is_or_node = is_or_node;
      dag_node.to_play = pos.ToPlay();
      dag_node.incoming_move = incoming_move;
      dag_node.pn = *out_pn;
      dag_node.dn = *out_dn;
      dag_node.outcome = *out_outcome;
      dag_node.proof_rz = *out_proof_rz;
      dag_node.disproof_rz = *out_disproof_rz;
      dag_node.child_node_ids = std::move(proven_child_ids);
      dag_node.child_moves = std::move(proven_child_moves);
      report_.proof_dag_nodes.push_back(dag_node);
      dag_has_capture_.push_back(node_has_capture);
      *out_dag_node_id = dag_node.node_id;

      tt_store_.StoreBoardTT(pos, context, *out_pn, *out_dn, *out_outcome,
                             *out_ko_dependent, true, *out_dag_node_id,
                             *out_proof_rz, *out_disproof_rz,
                             node_has_capture);
      if (config_.enable_pattern_tt) {
        const ProofCertificateRZ<N>& active_rz =
            (*out_outcome == ProofOutcome::kProvenWin) ? *out_proof_rz
                                                       : *out_disproof_rz;
        tt_store_.StorePatternTT(pos, context, active_rz, *out_pn, *out_dn,
                                 *out_outcome, *out_dag_node_id, true,
                                 node_has_capture);
      }
      // Once proven, free the frontier entry to reclaim memory immediately.
      node_frontier_cache_.erase(node_path_id);
      break;
    }

    // Threshold cutoff & resource checks (FR-4.3: OR condition).
    if (IsMemoryBudgetExceeded(depth)) {
      report_.resource_exhausted = true;
      report_.unknown_reason = UnknownReason::kMemoryBudget;
      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = ProofOutcome::kUnknown;
      break;
    }
    if (cur_pn >= th_pn || cur_dn >= th_dn ||
        report_.num_nodes >= config_.max_nodes) {
      if (report_.num_nodes >= config_.max_nodes) {
        report_.resource_exhausted = true;
        report_.unknown_reason = UnknownReason::kNodeLimit;
      }
      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = ProofOutcome::kUnknown;
      break;
    }

    // At compact AND nodes (where all legal moves already fit in window_size)
    // with 0 consecutive passes and no sibling RZ yet, probe PASS at most ONCE
    // (`!frontier.pass_probed`) to seed OutsideRZRevalidated pruning, then
    // immediately resume normal df-pn scheduling if inconclusive.
    if (force_expand_pass_idx < 0 && config_.enable_rz_pruning && !is_or_node &&
        unexpanded_u == 0 && pos.ConsecutivePasses() == 0 &&
        !frontier.has_null_move_rz && !frontier.pass_probed &&
        children.size() > 1U) {
      for (size_t idx : active_indices) {
        if (children[idx].move == kPassMove && !children[idx].probed &&
            !children[idx].ko_dependent &&
            children[idx].outcome == ProofOutcome::kUnknown) {
          force_expand_pass_idx = static_cast<int>(idx);
          break;
        }
      }
    }

    // Select most-proving child within active set (skipping ko_dependent barriers).
    int best_idx = -1;
    uint32_t best_metric = kPnDnSaturation;
    uint32_t second_best_metric = kPnDnSaturation;

    if (force_expand_pass_idx >= 0) {
      best_idx = force_expand_pass_idx;
      best_metric = children[static_cast<size_t>(best_idx)].dn;
      second_best_metric = kPnDnSaturation;
    } else {
      for (size_t idx : active_indices) {
        if (children[idx].ko_dependent) continue;
        const uint32_t m = is_or_node ? children[idx].pn : children[idx].dn;
        if (m < best_metric) {
          second_best_metric = best_metric;
          best_metric = m;
          best_idx = static_cast<int>(idx);
        } else if (m < second_best_metric) {
          second_best_metric = m;
        }
      }

      // Progressive Widening upgrade condition (FR-4.4).
      if (unexpanded_u > 0) {
        if (best_idx < 0 || best_metric >= widen_trigger) {
          ++frontier.widening_level;
          ++report_.widening_upgrades;
          continue;
        }
        second_best_metric = std::min(second_best_metric, widen_trigger);
      }
    }

    if (best_idx < 0 || best_metric >= kPnDnSaturation) {
      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = ProofOutcome::kUnknown;
      break;
    }

    if (children[static_cast<size_t>(best_idx)].move == kPassMove) {
      frontier.pass_probed = true;
    }

    const int16_t chosen_move = children[static_cast<size_t>(best_idx)].move;
    const uint64_t chosen_path_id =
        children[static_cast<size_t>(best_idx)].child_path_id;
    const uint32_t chosen_pn = children[static_cast<size_t>(best_idx)].pn;
    const uint32_t chosen_dn = children[static_cast<size_t>(best_idx)].dn;
    if (depth == 0) report_.best_move = chosen_move;

    // 1+epsilon df-pn with >= +4 & 1.65x margin so child thresholds sustain
    // deep tactical reading without bouncing at depths 2..4.
    const uint32_t eps_bound = ClampSat(std::max<uint64_t>(
        static_cast<uint64_t>(second_best_metric) + 4ULL,
        (static_cast<uint64_t>(second_best_metric) * 165ULL + 99ULL) / 100ULL +
            4ULL));
    uint32_t child_th_pn = th_pn;
    uint32_t child_th_dn = th_dn;
    if (is_or_node) {
      child_th_pn = std::min(th_pn, eps_bound);
      const uint64_t other_dn =
          (cur_dn > chosen_dn) ? static_cast<uint64_t>(cur_dn - chosen_dn)
                               : 0ULL;
      child_th_dn =
          (th_dn >= kPnDnSaturation)
              ? kPnDnSaturation
              : ((th_dn > other_dn)
                     ? std::max(2U, static_cast<uint32_t>(th_dn - other_dn))
                     : 1U);
    } else {
      const uint64_t other_pn =
          (cur_pn > chosen_pn) ? static_cast<uint64_t>(cur_pn - chosen_pn)
                               : 0ULL;
      child_th_pn =
          (th_pn >= kPnDnSaturation)
              ? kPnDnSaturation
              : ((th_pn > other_pn)
                     ? std::max(2U, static_cast<uint32_t>(th_pn - other_pn))
                     : 1U);
      child_th_dn = std::min(th_dn, eps_bound);
    }

    const int prev_opp_stones =
        pos.Stones(OppositeColor(pos.ToPlay())).Count();
    bool is_ko_capture = false;
    if (!pos.PlayMove(chosen_move, &is_ko_capture)) {
      *out_pn = 1;
      *out_dn = 1;
      *out_outcome = ProofOutcome::kUnknown;
      *out_dag_node_id = kInvalidDagNodeId;
      break;
    }
    const bool move_captured =
        pos.Stones(pos.ToPlay()).Count() < prev_opp_stones;

    uint32_t c_pn = 1;
    uint32_t c_dn = 1;
    ProofOutcome c_outcome = ProofOutcome::kUnknown;
    bool child_ko_dep = false;
    bool child_has_capture = false;
    ProofCertificateRZ<N> c_proof_rz{};
    ProofCertificateRZ<N> c_disproof_rz{};
    uint32_t c_dag_id = kInvalidDagNodeId;

    MidSearch(pos, context, region_hint, child_th_pn, child_th_dn, depth + 1U,
              chosen_path_id, in_path_hashes, &c_pn, &c_dn, &c_outcome,
              &child_ko_dep, &child_has_capture, &c_proof_rz, &c_disproof_rz,
              &c_dag_id, chosen_move);
    pos.UndoMove();

    // Re-fetch frontier & child reference safely after recursive MidSearch.
    CachedNodeFrontier& post_frontier = node_frontier_cache_.at(node_path_id);
    auto& mpc = post_frontier.children[static_cast<size_t>(best_idx)];
    mpc.pn = c_pn;
    mpc.dn = c_dn;
    mpc.outcome = c_outcome;
    mpc.move_captured = move_captured;
    mpc.subtree_has_capture = child_has_capture;
    mpc.proof_rz = c_proof_rz;
    mpc.disproof_rz = c_disproof_rz;
    mpc.dag_node_id = c_dag_id;

    mpc.probed = true;
    if (mpc.move == kPassMove) {
      post_frontier.pass_probed = true;
    }

    // FR-5.7: KoDependent witness barrier check (propagates child_ko_dep too;
    // reuses loop-scoped `restricted_side`).
    if ((is_ko_capture || child_ko_dep) && restricted_side &&
        ((is_or_node && mpc.pn == 0) || (!is_or_node && mpc.dn == 0))) {
      mpc.ko_dependent = true;
      mpc.outcome = ProofOutcome::kUnknown;
      mpc.pn = kPnDnSaturation / 2;
      mpc.dn = kPnDnSaturation / 2;
      mpc.dag_node_id = kInvalidDagNodeId;
      mpc.has_decisive_dag = false;
      *out_ko_dependent = true;
    } else {
      mpc.has_decisive_dag = (mpc.outcome != ProofOutcome::kUnknown &&
                              mpc.dag_node_id != kInvalidDagNodeId);
    }

    // Record compact sibling certificate RZ for OutsideRZRevalidated pruning (FR-5.5).
    // Prefer PASS_MOVE (Null-Move) representative at AND nodes because no stone
    // is added on sourcePos, guaranteeing queryLegalMoves <= sourceLegalMoves.
    // Never seed OR-node active_null_move_rz from PASS_MOVE (DOUBLE_PASS_RESOLUTION)!
    if (!is_or_node && mpc.pn == 0 && mpc.has_decisive_dag &&
        mpc.proof_rz.Size() > 0 &&
        (!post_frontier.has_null_move_rz ||
         (mpc.move == kPassMove &&
          post_frontier.representative_move != kPassMove) ||
         ((mpc.move == kPassMove) ==
              (post_frontier.representative_move == kPassMove) &&
          mpc.proof_rz.Size() < post_frontier.active_null_move_rz.Size()))) {
      post_frontier.active_null_move_rz = mpc.proof_rz;
      post_frontier.has_null_move_rz = true;
      post_frontier.representative_move = mpc.move;
      post_frontier.representative_dag_id = mpc.dag_node_id;
      post_frontier.representative_outcome = ProofOutcome::kProvenWin;
    } else if (is_or_node && mpc.move != kPassMove && mpc.dn == 0 &&
               mpc.has_decisive_dag && mpc.disproof_rz.Size() > 0 &&
               (!post_frontier.has_null_move_rz ||
                mpc.disproof_rz.Size() <
                    post_frontier.active_null_move_rz.Size())) {
      post_frontier.active_null_move_rz = mpc.disproof_rz;
      post_frontier.has_null_move_rz = true;
      post_frontier.representative_move = mpc.move;
      post_frontier.representative_dag_id = mpc.dag_node_id;
      post_frontier.representative_outcome = ProofOutcome::kProvenLoss;
    }
  }

  in_path_hashes.erase(pos.ZobristHash());
}

template class DfpnSolver<5>;
template class DfpnSolver<7>;
template class DfpnSolver<19>;

}  // namespace ldprover
