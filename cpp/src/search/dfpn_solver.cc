// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/search/dfpn_solver.cc
// Description: Implementation of DfpnSolver<N> (FR-4.1..FR-4.10, FR-5.5, FR-5.7).

#include "ldprover/search/dfpn_solver.h"

#include <algorithm>
#include <limits>

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

  // Build local tactical attention mask (Chebyshev radius 2 around non-immortal
  // stones inside the declared region, plus crucial tokens).
  attention_mask_.reset();
  if (region_hint.has_value()) {
    BitBoard<N> seeds =
        (initial_pos.Stones(Color::kBlack) | initial_pos.Stones(Color::kWhite)) &
        (~initial_pos.ImmortalWall()) & (*region_hint);
    for (const auto& tok : context.initial_tokens) {
      if (tok.initial_coord >= 0 && tok.initial_coord < N * N) {
        seeds.Set(tok.initial_coord, true);
      }
    }
    if (seeds.Any()) {
      BitBoard<N> att;
      for (int sc : seeds.ToCoords()) {
        const int sr = sc / N;
        const int sc_col = sc % N;
        for (int dr = -2; dr <= 2; ++dr) {
          for (int dc = -2; dc <= 2; ++dc) {
            const int nr = sr + dr;
            const int nc = sc_col + dc;
            if (nr >= 0 && nr < N && nc >= 0 && nc < N) {
              const int coord = nr * N + nc;
              if (region_hint->Get(coord)) att.Set(coord, true);
            }
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
  const int board_pts = N * N;
  ctx.crucial_lib_bonus.assign(static_cast<size_t>(board_pts), 0);
  ctx.enemy_min_lib.assign(static_cast<size_t>(board_pts), 99);
  ctx.friendly_min_lib.assign(static_cast<size_t>(board_pts), 99);

  // Precompute crucial stone chain liberties once per frontier node.
  BitBoard<N> visited_crucial;
  for (size_t i = 0; i < context.initial_tokens.size() && i < 64; ++i) {
    if ((pos.SurvivingTargetTokensMask() & (1ULL << i)) == 0) continue;
    const int t_coord = context.initial_tokens[i].initial_coord;
    if (t_coord < 0 || t_coord >= board_pts) continue;
    ctx.target_coords.Set(t_coord, true);
    if (visited_crucial.Get(t_coord)) continue;
    BitBoard<N> libs;
    const BitBoard<N> chain = pos.FloodFillChain(t_coord, &libs);
    visited_crucial |= chain;
    const int lib_cnt = libs.Count();
    int bonus = 560;
    if (lib_cnt == 1) bonus += 1400;
    else if (lib_cnt == 2) bonus += 740;
    else if (lib_cnt == 3) bonus += 260;
    for (int lc : libs.ToCoords()) {
      ctx.crucial_lib_bonus[static_cast<size_t>(lc)] =
          std::max(ctx.crucial_lib_bonus[static_cast<size_t>(lc)], bonus);
    }
  }

  // Precompute liberty counts for all non-immortal chains once per node.
  const Color us = pos.ToPlay();
  const Color enemy = OppositeColor(us);
  BitBoard<N> seen_chains;
  const BitBoard<N> wall = pos.ImmortalWall();
  const BitBoard<N> non_wall_stones =
      (pos.Stones(Color::kBlack) | pos.Stones(Color::kWhite)) & (~wall);

  for (int sc : non_wall_stones.ToCoords()) {
    if (seen_chains.Get(sc)) continue;
    const Color c = pos.StoneAt(sc);
    if (c == Color::kEmpty) continue;
    BitBoard<N> libs;
    const BitBoard<N> chain = pos.FloodFillChain(sc, &libs);
    seen_chains |= chain;
    if ((chain & wall).Any()) continue;
    const int lib_cnt = libs.Count();
    for (int lc : libs.ToCoords()) {
      if (c == enemy) {
        ctx.enemy_min_lib[static_cast<size_t>(lc)] =
            std::min(ctx.enemy_min_lib[static_cast<size_t>(lc)], lib_cnt);
      } else {
        ctx.friendly_min_lib[static_cast<size_t>(lc)] =
            std::min(ctx.friendly_min_lib[static_cast<size_t>(lc)], lib_cnt);
      }
    }
  }
  return ctx;
}

template <int N>
int32_t DfpnSolver<N>::ScoreMoveFastCapture(const Position<N>& pos,
                                            const ProofContext& context,
                                            const NodeTacticalContext& tctx,
                                            int16_t move,
                                            bool is_or_node) const {
  if (move == kPassMove) {
    // At AND nodes (defender to play) with 0 consecutive passes, rank PASS
    // below immediate tactical captures/refutations so bad attacker moves are
    // refuted first, while still keeping PASS near the top for null-move RZ.
    if (!is_or_node && pos.ConsecutivePasses() == 0) {
      return config_.enable_rz_pruning ? 1050 : 360;
    }
    return -2000;
  }
  int32_t score = tctx.crucial_lib_bonus[static_cast<size_t>(move)];

  // Penalize outer-moat moves outside local tactical attention zone.
  if (attention_mask_.has_value() && !attention_mask_->Get(move)) {
    score -= 950;
  }

  // Atari / capture / rescue bonuses from precomputed chain liberties.
  const int e_min = tctx.enemy_min_lib[static_cast<size_t>(move)];
  const int f_min = tctx.friendly_min_lib[static_cast<size_t>(move)];
  if (e_min == 1) score += 1550;       // immediate capture
  else if (e_min == 2) score += 540;   // puts enemy in atari
  if (f_min == 1) score += 720;        // rescues own atari chain
  else if (f_min == 2) score += 260;

  // Symmetric local eye-vitality & connection geometry (no stone simulation needed
  // unless capture/atari is plausible).
  const Color us = pos.ToPlay();
  const Color enemy = OppositeColor(us);
  int friendly_ortho = 0;
  int enemy_ortho = 0;
  int empty_ortho = 0;
  int wall_ortho = 0;
  const auto ortho = pos.OrthogonalNeighbors(move);
  for (int nb : ortho) {
    if (pos.ImmortalWall().Get(nb)) ++wall_ortho;
    const Color s = pos.StoneAt(nb);
    if (s == us) ++friendly_ortho;
    else if (s == enemy) ++enemy_ortho;
    else ++empty_ortho;
  }
  int friendly_diag = 0;
  int enemy_diag = 0;
  for (int d : pos.DiagonalNeighbors(move)) {
    const Color s = pos.StoneAt(d);
    if (s == us) ++friendly_diag;
    else if (s == enemy) ++enemy_diag;
  }

  const int deg = static_cast<int>(ortho.size());
  // Vital point of enemy eye shape (surrounded by enemy stones -> nakade/vital).
  if (enemy_ortho >= deg - 1 && enemy_ortho >= 2) {
    score += 640;
  }
  // Vital point of own eye shape (e.g. straight-three / bulky-five center).
  if (friendly_ortho >= 2 && empty_ortho >= 1 && enemy_ortho == 0) {
    score += 290;
  }
  // Contact / hane / cut / wedge moves.
  if (friendly_ortho >= 1 && enemy_ortho >= 1) score += 420;
  if (friendly_ortho >= 1 && enemy_diag >= 1) score += 320;
  if (enemy_ortho >= 1 && enemy_diag >= 2) score += 310;

  // Penalize obvious self-eye-fill (surrounded exclusively by own stones + diagonals).
  if (friendly_ortho == deg && enemy_ortho == 0 && enemy_diag == 0 &&
      e_min > 1) {
    score -= 680;
  } else if (friendly_ortho >= 1 && friendly_diag >= 2 && enemy_ortho == 0 &&
             enemy_diag == 0 && empty_ortho <= 1) {
    score -= 260;
  }

  // Slight preference for 1st/2nd line corner/edge vital points near target stones.
  const int r = move / N;
  const int c = move % N;
  const int edge_r = std::min(r, N - 1 - r);
  const int edge_c = std::min(c, N - 1 - c);
  if ((edge_r == 1 && edge_c == 1) || (edge_r == 0 && edge_c <= 2) ||
      (edge_c == 0 && edge_r <= 2)) {
    score += 110;
  }

  // Exact capture / self-atari check only when contact or capture is possible.
  if (e_min == 1 || (empty_ortho == 0 && friendly_ortho > 0) ||
      (empty_ortho <= 1 && enemy_ortho > 0)) {
    Position<N> next = pos;
    const int prev_enemy_count = pos.Stones(enemy).Count();
    if (next.PlayMove(move)) {
      const int captured = prev_enemy_count - next.Stones(enemy).Count();
      if (captured > 0) score += 900 + captured * 260;
      BitBoard<N> our_libs;
      (void)next.FloodFillChain(move, &our_libs);
      if (our_libs.Count() == 1 && captured == 0) score -= 420;
      else if (our_libs.Count() >= 3) score += 180;
    }
  }
  (void)context;
  (void)wall_ortho;
  return score;
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
    std::vector<int16_t> legal_moves = pos.GenerateLegalMoves(region_hint);
    fresh.children.reserve(legal_moves.size());
    const NodeTacticalContext tctx =
        config_.enable_fast_capture_ordering
            ? BuildNodeTacticalContext(pos, context)
            : NodeTacticalContext{};
    for (int16_t mv : legal_moves) {
      SearchChild ch;
      ch.move = mv;
      ch.child_path_id = next_path_id_++;
      ch.tactical_score =
          config_.enable_fast_capture_ordering
              ? ScoreMoveFastCapture(pos, context, tctx, mv, is_or_node)
              : 0;
      fresh.children.push_back(ch);
    }
    if (config_.enable_fast_capture_ordering) {
      std::stable_sort(
          fresh.children.begin(), fresh.children.end(),
          [](const SearchChild& a, const SearchChild& b) {
            return a.tactical_score > b.tactical_score;
          });
      for (size_t idx = 0; idx < fresh.children.size(); ++idx) {
        const uint32_t rank_metric =
            (idx == 0) ? 1U : (idx <= 2 ? 2U : static_cast<uint32_t>(idx + 1));
        if (is_or_node) {
          fresh.children[idx].pn =
              (fresh.children[idx].move == kPassMove) ? 220U : rank_metric;
          fresh.children[idx].dn = 1U;
        } else {
          fresh.children[idx].pn = 1U;
          fresh.children[idx].dn =
              (fresh.children[idx].move == kPassMove) ? 4U : rank_metric;
        }
      }
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
              ? static_cast<size_t>(config_.widening_base_k)
              : std::max<size_t>(4U,
                                 static_cast<size_t>(config_.widening_base_k) /
                                     2U);
      const size_t cap = base_k << frontier.widening_level;
      if (cap < total_legal) window_size = cap;
    }

    // FR-5.5: Try Outside-RZ null-move certificate pruning on undecided moves
    // inside the active window (per-child stamp so newly widened moves are
    // checked immediately without repeating failed revalidations).
    if (config_.enable_rz_pruning && frontier.has_null_move_rz &&
        frontier.representative_dag_id != kInvalidDagNodeId) {
      const bool restricted_side =
          (pos.ToPlay() == context.root_attacker &&
           !context.attacker_allow_ko) ||
          (pos.ToPlay() != context.root_attacker &&
           !context.defender_allow_ko);
      const bool rep_has_cap =
          frontier.representative_dag_id < dag_has_capture_.size() &&
          dag_has_capture_[frontier.representative_dag_id];
      const int prev_opp_cnt =
          pos.Stones(OppositeColor(pos.ToPlay())).Count();

      for (size_t i = 0; i < window_size; ++i) {
        auto& ch = children[i];
        if (ch.has_decisive_dag || ch.outcome != ProofOutcome::kUnknown ||
            ch.checked_null_move_dag_id == frontier.representative_dag_id) {
          continue;
        }
        ch.checked_null_move_dag_id = frontier.representative_dag_id;
        if (rz_engine_.IsOutsideRZCandidate(ch.move,
                                            frontier.active_null_move_rz)) {
          Position<N> next_pos = pos;
          bool is_ko_cap = false;
          if (next_pos.PlayMove(ch.move, &is_ko_cap) &&
              !(is_ko_cap && restricted_side) &&
              RevalidateSourceProofOnQueryState(
                  next_pos, context, region_hint,
                  frontier.representative_dag_id,
                  frontier.representative_outcome)) {
            const bool did_cap =
                next_pos.Stones(OppositeColor(pos.ToPlay())).Count() <
                prev_opp_cnt;
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
            dag_has_capture_.push_back(rep_has_cap);

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
          }
        }
      }
    }

    // FR-4.1: Frontier PN/DN aggregation without breadth-exploding sum inflation.
    const size_t unexpanded_u =
        (total_legal > window_size) ? (total_legal - window_size) : 0;
    const uint32_t widen_trigger =
        (unexpanded_u > 0)
            ? std::max(is_or_node ? children[window_size].pn
                                  : children[window_size].dn,
                       (is_or_node ? 14U : 10U) *
                           (frontier.widening_level + 1U))
            : kPnDnSaturation;
    uint32_t cur_pn = 1;
    uint32_t cur_dn = 1;
    int force_expand_pass_idx = -1;

    if (is_or_node) {
      uint32_t min_pn = kPnDnSaturation;
      uint64_t sum_dn = 0;
      for (size_t i = 0; i < window_size; ++i) {
        min_pn = std::min(min_pn, children[i].pn);
        sum_dn += children[i].dn;
      }
      if (unexpanded_u > 0) {
        min_pn = std::min(min_pn, widen_trigger);
      }
      if (sum_dn == 0 && window_size < total_legal) {
        frontier.widening_level =
            frontier.has_null_move_rz ? 6U : (frontier.widening_level + 1U);
        ++report_.widening_upgrades;
        continue;
      }
      cur_pn = min_pn;
      cur_dn = ClampSat(sum_dn + (unexpanded_u > 0 ? 1ULL : 0ULL));
    } else {
      uint64_t sum_pn = 0;
      uint32_t min_dn = kPnDnSaturation;
      for (size_t i = 0; i < window_size; ++i) {
        sum_pn += children[i].pn;
        min_dn = std::min(min_dn, children[i].dn);
      }
      // Also honor any already-probed PASS outside the current window that
      // produced a decisive refutation (dn == 0).
      for (size_t i = window_size; i < total_legal; ++i) {
        if (children[i].has_decisive_dag && !children[i].ko_dependent &&
            children[i].dn == 0) {
          min_dn = 0;
          break;
        }
      }
      if (unexpanded_u > 0) {
        min_dn = std::min(min_dn, widen_trigger);
      }
      if (min_dn > 0 && sum_pn == 0 && window_size < total_legal) {
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
          frontier.widening_level =
              frontier.has_null_move_rz ? 6U : (frontier.widening_level + 1U);
          ++report_.widening_upgrades;
          continue;
        }
      } else {
        cur_pn = ClampSat(sum_pn + (unexpanded_u > 0 ? 1ULL : 0ULL));
        cur_dn = min_dn;
      }
    }

    // Check asymmetric decisive completion conditions (FR-4.2).
    if (cur_pn == 0 || cur_dn == 0) {
      // Full coverage required for OR->Loss (cur_dn == 0) and AND->Win (cur_pn == 0).
      if (((is_or_node && cur_dn == 0) || (!is_or_node && cur_pn == 0)) &&
          window_size < total_legal) {
        ++frontier.widening_level;
        ++report_.widening_upgrades;
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
        window_size == total_legal && pos.ConsecutivePasses() == 0 &&
        !frontier.has_null_move_rz && !frontier.pass_probed &&
        children.size() > 1U) {
      for (size_t i = 0; i < window_size; ++i) {
        if (children[i].move == kPassMove && !children[i].probed &&
            !children[i].ko_dependent &&
            children[i].outcome == ProofOutcome::kUnknown) {
          force_expand_pass_idx = static_cast<int>(i);
          break;
        }
      }
    }

    // Select most-proving child within current window (skipping ko_dependent barriers).
    int best_idx = -1;
    uint32_t best_metric = kPnDnSaturation;
    uint32_t second_best_metric = kPnDnSaturation;

    if (force_expand_pass_idx >= 0) {
      best_idx = force_expand_pass_idx;
      best_metric = children[static_cast<size_t>(best_idx)].dn;
      second_best_metric = kPnDnSaturation;
    } else {
      for (size_t i = 0; i < window_size; ++i) {
        if (children[i].ko_dependent) continue;
        const uint32_t m = is_or_node ? children[i].pn : children[i].dn;
        if (m < best_metric) {
          second_best_metric = best_metric;
          best_metric = m;
          best_idx = static_cast<int>(i);
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

    const uint32_t eps_bound = ClampSat(std::max<uint64_t>(
        static_cast<uint64_t>(second_best_metric) + 1ULL,
        static_cast<uint64_t>(second_best_metric) * 5ULL / 4ULL + 2ULL));
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

    // FR-5.7: KoDependent witness barrier check (propagates child_ko_dep too!).
    const bool restricted_side =
        (pos.ToPlay() == context.root_attacker && !context.attacker_allow_ko) ||
        (pos.ToPlay() != context.root_attacker && !context.defender_allow_ko);
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
