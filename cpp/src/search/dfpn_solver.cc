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

}  // namespace

template <int N>
bool DfpnSolver<N>::IsMemoryBudgetExceeded() const noexcept {
  if (config_.memory_budget_bytes == 0ULL) return false;
  const uint64_t approx_bytes =
      static_cast<uint64_t>(report_.proof_dag_nodes.size()) * 768ULL +
      static_cast<uint64_t>(tt_store_.EstimatedEntryCount()) * 1024ULL;
  return approx_bytes > config_.memory_budget_bytes;
}

template <int N>
SolveReport<N> DfpnSolver<N>::Solve(
    const Position<N>& initial_pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint,
    const std::string& problem_id) {
  // FR-6.2: Clear BoardTT and PatternTT at the start of every problem.
  tt_store_.ClearAll();
  report_ = SolveReport<N>{};
  report_.problem_id = problem_id;
  report_.input_hash = initial_pos.ZobristHash();
  report_.region_hint = region_hint;

  Position<N> work_pos = initial_pos;
  std::unordered_set<uint64_t> in_path_hashes;
  bool ko_dep = false;

  MidSearch(work_pos, context, region_hint, kPnDnSaturation, kPnDnSaturation,
            0, in_path_hashes, &report_.root_pn, &report_.root_dn,
            &report_.root_status, &ko_dep, &report_.root_proof_rz,
            &report_.root_disproof_rz, &report_.root_dag_node_id, kPassMove);

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
int32_t DfpnSolver<N>::ScoreMoveFastCapture(const Position<N>& pos,
                                            const ProofContext& context,
                                            int16_t move,
                                            bool is_or_node) const {
  if (move == kPassMove) {
    return (!is_or_node && pos.ConsecutivePasses() == 0) ? 450 : -2000;
  }
  int32_t score = 0;

  // Prioritize moves adjacent to crucial stones or their liberties.
  for (size_t i = 0; i < context.initial_tokens.size() && i < 64; ++i) {
    if ((pos.SurvivingTargetTokensMask() & (1ULL << i)) == 0) continue;
    int t_coord = context.initial_tokens[i].initial_coord;
    BitBoard<N> libs;
    (void)pos.FloodFillChain(t_coord, &libs);
    if (libs.Get(move)) {
      score += 550;
      if (libs.Count() == 1) score += 1350;
      else if (libs.Count() == 2) score += 720;
    }
  }

  // Simulate move to evaluate captures and tactical atari.
  Position<N> next = pos;
  const int prev_enemy_count =
      pos.Stones(OppositeColor(pos.ToPlay())).Count();
  if (next.PlayMove(move)) {
    const int new_enemy_count =
        next.Stones(pos.ToPlay() == Color::kBlack ? Color::kWhite
                                                  : Color::kBlack)
            .Count();
    const int captured = prev_enemy_count - new_enemy_count;
    if (captured > 0) score += 1250 + captured * 300;

    BitBoard<N> our_libs;
    next.FloodFillChain(move, &our_libs);
    if (our_libs.Count() == 1) score -= 350;
    if (our_libs.Count() >= 3) score += 200;
  }

  // Distinguish border-expanding blocks from pure internal eye-space self-fills.
  const Color enemy = OppositeColor(pos.ToPlay());
  int friendly_ortho = 0;
  int enemy_ortho = 0;
  for (int nb : pos.OrthogonalNeighbors(move)) {
    if (pos.StoneAt(nb) == pos.ToPlay()) ++friendly_ortho;
    else if (pos.StoneAt(nb) == enemy) ++enemy_ortho;
  }
  int friendly_diag = 0;
  int enemy_diag = 0;
  for (int d : pos.DiagonalNeighbors(move)) {
    if (pos.StoneAt(d) == pos.ToPlay()) ++friendly_diag;
    else if (pos.StoneAt(d) == enemy) ++enemy_diag;
  }
  if (friendly_ortho >= 1 && enemy_ortho >= 1) score += 380;
  if (friendly_ortho >= 1 && enemy_diag >= 1) score += 320;
  if (friendly_ortho >= 1 && friendly_diag >= 2 && enemy_ortho == 0 &&
      enemy_diag == 0) {
    score -= 240;
  }
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

  const auto term = terminal_eval_.EvaluateTerminal(query_pos, context);
  if (term.status == TerminalStatus::kWin) {
    return expected_outcome == ProofOutcome::kProvenWin;
  }
  if (term.status == TerminalStatus::kLoss) {
    return expected_outcome == ProofOutcome::kProvenLoss;
  }

  if (node.child_node_ids.empty()) return false;
  const bool is_or = (query_pos.ToPlay() == context.root_attacker);
  const bool restricted_side =
      (query_pos.ToPlay() == context.root_attacker && !context.attacker_allow_ko) ||
      (query_pos.ToPlay() != context.root_attacker && !context.defender_allow_ko);

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
              next, context, region_hint, cid,
              expected_outcome, guard_depth + 1)) {
        return true;
      }
    }
    return false;
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
    if (found_idx < 0) return false;
    const uint32_t cid = node.child_node_ids[found_idx];
    if (cid >= report_.proof_dag_nodes.size() ||
        report_.proof_dag_nodes[cid].outcome != expected_outcome) {
      return false;
    }
    Position<N> next = query_pos;
    if (!next.PlayMove(mv)) return false;
    if (!RevalidateSourceProofOnQueryState(
            next, context, region_hint, cid,
            expected_outcome, guard_depth + 1)) {
      return false;
    }
  }
  return true;
}

template <int N>
void DfpnSolver<N>::MidSearch(
    Position<N>& pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint, uint32_t th_pn,
    uint32_t th_dn, uint32_t depth,
    std::unordered_set<uint64_t>& in_path_hashes, uint32_t* out_pn,
    uint32_t* out_dn, ProofOutcome* out_outcome, bool* out_ko_dependent,
    ProofCertificateRZ<N>* out_proof_rz,
    ProofCertificateRZ<N>* out_disproof_rz, uint32_t* out_dag_node_id,
    int16_t incoming_move) {
  ++report_.num_nodes;
  *out_ko_dependent = false;
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
  if (IsMemoryBudgetExceeded()) {
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
                              const ProofCertificateRZ<N>& d_rz) {
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
    return tt_node.node_id;
  };

  // Step 4 (FR-6.1, FR-6.3, FR-6.9): History-safe BoardTT & PatternTT lookup.
  if (auto hit = tt_store_.LookupBoardTT(pos, context); hit.has_value()) {
    if (hit->outcome != ProofOutcome::kUnknown &&
        hit->proof_closure_available &&
        hit->proof_dag_node_id < report_.proof_dag_nodes.size()) {
      *out_pn = hit->pn;
      *out_dn = hit->dn;
      *out_outcome = hit->outcome;
      *out_proof_rz = hit->proof_rz;
      *out_disproof_rz = hit->disproof_rz;
      *out_dag_node_id = emit_tt_hit_node(
          hit->proof_dag_node_id, hit->pn, hit->dn, hit->outcome,
          hit->proof_rz, hit->disproof_rz);
      return;
    }
  }

  if (config_.enable_pattern_tt) {
    RadixPatternRecord<N> pat_rec;
    const PatternHitGrade grade =
        tt_store_.LookupPatternTT(pos, context, &pat_rec);
    if (grade == PatternHitGrade::kProofReusable &&
        pat_rec.proof_dag_node_id < report_.proof_dag_nodes.size()) {
      *out_pn = pat_rec.pn;
      *out_dn = pat_rec.dn;
      *out_outcome = pat_rec.outcome;
      *out_proof_rz = pat_rec.stored_rz;
      *out_disproof_rz = pat_rec.stored_rz;
      *out_dag_node_id = emit_tt_hit_node(
          pat_rec.proof_dag_node_id, pat_rec.pn, pat_rec.dn, pat_rec.outcome,
          pat_rec.stored_rz, pat_rec.stored_rz);
      return;
    }
    if (grade == PatternHitGrade::kHeuristicOnly &&
        pat_rec.proof_closure_available &&
        pat_rec.proof_dag_node_id < report_.proof_dag_nodes.size() &&
        RevalidateSourceProofOnQueryState(
            pos, context, region_hint, pat_rec.proof_dag_node_id,
            pat_rec.outcome)) {
      *out_pn = pat_rec.pn;
      *out_dn = pat_rec.dn;
      *out_outcome = pat_rec.outcome;
      *out_proof_rz = pat_rec.stored_rz;
      *out_disproof_rz = pat_rec.stored_rz;
      *out_dag_node_id = emit_tt_hit_node(
          pat_rec.proof_dag_node_id, pat_rec.pn, pat_rec.dn, pat_rec.outcome,
          pat_rec.stored_rz, pat_rec.stored_rz);
      return;
    }
  }

  // Step 5: Generate legal moves and apply deterministic FastCapture ordering.
  std::vector<int16_t> legal_moves = pos.GenerateLegalMoves(region_hint);
  std::vector<SearchChild> children;
  children.reserve(legal_moves.size());
  for (int16_t mv : legal_moves) {
    SearchChild ch;
    ch.move = mv;
    ch.tactical_score =
        config_.enable_fast_capture_ordering
            ? ScoreMoveFastCapture(pos, context, mv, is_or_node)
            : 0;
    children.push_back(ch);
  }
  if (config_.enable_fast_capture_ordering) {
    std::stable_sort(
        children.begin(), children.end(),
        [](const SearchChild& a, const SearchChild& b) {
          return a.tactical_score > b.tactical_score;
        });
    for (size_t idx = 0; idx < children.size(); ++idx) {
      const uint32_t rank_metric =
          (idx == 0) ? 1U : (idx <= 2 ? 2U : static_cast<uint32_t>(idx + 1));
      if (is_or_node) {
        children[idx].pn =
            (children[idx].move == kPassMove) ? 120U : rank_metric;
        children[idx].dn = 1U;
      } else {
        children[idx].pn = 1U;
        children[idx].dn =
            (children[idx].move == kPassMove) ? 2U : rank_metric;
      }
    }
  }

  in_path_hashes.insert(pos.ZobristHash());

  uint32_t widening_level = 0;
  ProofCertificateRZ<N> active_null_move_rz;
  bool has_null_move_rz = false;
  uint32_t representative_dag_id = kInvalidDagNodeId;
  ProofOutcome representative_outcome = ProofOutcome::kUnknown;

  while (true) {
    const size_t total_legal = children.size();
    size_t window_size = total_legal;
    if (config_.enable_progressive_widening && widening_level < 4) {
      const size_t cap =
          static_cast<size_t>(config_.widening_base_k) << widening_level;
      if (cap < total_legal) window_size = cap;
    }

    // FR-5.5: Try Outside-RZ null-move certificate pruning on unexpanded moves
    // when an active sibling certificate RZ exists.
    if (config_.enable_rz_pruning && has_null_move_rz) {
      const bool restricted_side =
          (pos.ToPlay() == context.root_attacker && !context.attacker_allow_ko) ||
          (pos.ToPlay() != context.root_attacker && !context.defender_allow_ko);
      for (size_t i = 0; i < window_size; ++i) {
        auto& ch = children[i];
        if (ch.expanded || ch.outcome != ProofOutcome::kUnknown) continue;
        if (rz_engine_.IsOutsideRZCandidate(ch.move, active_null_move_rz)) {
          Position<N> next_pos = pos;
          bool is_ko_cap = false;
          if (next_pos.PlayMove(ch.move, &is_ko_cap) &&
              !(is_ko_cap && restricted_side) &&
              RevalidateSourceProofOnQueryState(
                  next_pos, context, region_hint, representative_dag_id,
                  representative_outcome)) {
            ProofDagNode<N> pruned_node;
            pruned_node.node_id =
                static_cast<uint32_t>(report_.proof_dag_nodes.size());
            pruned_node.is_or_node = !is_or_node;
            pruned_node.to_play = next_pos.ToPlay();
            pruned_node.incoming_move = ch.move;
            pruned_node.pn =
                (representative_outcome == ProofOutcome::kProvenWin)
                    ? 0
                    : kPnDnSaturation;
            pruned_node.dn =
                (representative_outcome == ProofOutcome::kProvenWin)
                    ? kPnDnSaturation
                    : 0;
            pruned_node.outcome = representative_outcome;
            pruned_node.is_pruned_outside_rz = true;
            pruned_node.source_proof_node_id = representative_dag_id;
            pruned_node.proof_rz = active_null_move_rz;
            pruned_node.disproof_rz = active_null_move_rz;
            report_.proof_dag_nodes.push_back(pruned_node);

            ch.expanded = true;
            ch.pruned_outside_rz = true;
            ch.outcome = representative_outcome;
            ch.pn = pruned_node.pn;
            ch.dn = pruned_node.dn;
            ch.proof_rz = active_null_move_rz;
            ch.disproof_rz = active_null_move_rz;
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
                       8U * (widening_level + 1U))
            : kPnDnSaturation;
    uint32_t cur_pn = 1;
    uint32_t cur_dn = 1;

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
        ++widening_level;
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
      if (unexpanded_u > 0) {
        min_dn = std::min(min_dn, widen_trigger);
      }
      if (sum_pn == 0 && window_size < total_legal) {
        ++widening_level;
        ++report_.widening_upgrades;
        continue;
      }
      cur_pn = ClampSat(sum_pn + (unexpanded_u > 0 ? 1ULL : 0ULL));
      cur_dn = min_dn;
    }

    // Check asymmetric decisive completion conditions (FR-4.2).
    if (cur_pn == 0 || cur_dn == 0) {
      // Full coverage required for OR->Loss (cur_dn == 0) and AND->Win (cur_pn == 0).
      if (((is_or_node && cur_dn == 0) || (!is_or_node && cur_pn == 0)) &&
          window_size < total_legal) {
        ++widening_level;
        ++report_.widening_upgrades;
        continue;
      }

      const ProofOutcome target_outcome =
          (cur_pn == 0) ? ProofOutcome::kProvenWin : ProofOutcome::kProvenLoss;
      const bool is_existential =
          (is_or_node && cur_pn == 0) || (!is_or_node && cur_dn == 0);

      std::vector<uint32_t> proven_child_ids;
      std::vector<int16_t> proven_child_moves;

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
        const auto& w = children[witness_idx];
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
      }

      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = target_outcome;

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
      *out_dag_node_id = dag_node.node_id;

      tt_store_.StoreBoardTT(pos, context, *out_pn, *out_dn, *out_outcome,
                             *out_ko_dependent, true, *out_dag_node_id,
                             *out_proof_rz, *out_disproof_rz);
      if (config_.enable_pattern_tt) {
        const ProofCertificateRZ<N>& active_rz =
            (*out_outcome == ProofOutcome::kProvenWin) ? *out_proof_rz
                                                       : *out_disproof_rz;
        tt_store_.StorePatternTT(pos, context, active_rz, *out_pn, *out_dn,
                                 *out_outcome, *out_dag_node_id, true);
      }
      break;
    }

    // Threshold cutoff check (FR-4.3: OR condition).
    if (IsMemoryBudgetExceeded()) {
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

    // Select most-proving child within current window (skipping ko_dependent barriers).
    int best_idx = -1;
    uint32_t best_metric = kPnDnSaturation;
    uint32_t second_best_metric = kPnDnSaturation;

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
        ++widening_level;
        ++report_.widening_upgrades;
        continue;
      }
      second_best_metric = std::min(second_best_metric, widen_trigger);
    }

    if (best_idx < 0 || best_metric >= kPnDnSaturation) {
      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = ProofOutcome::kUnknown;
      break;
    }

    auto& mpc = children[best_idx];
    if (depth == 0) report_.best_move = mpc.move;
    const uint32_t eps_bound = ClampSat(std::max<uint64_t>(
        static_cast<uint64_t>(second_best_metric) + 1ULL,
        static_cast<uint64_t>(second_best_metric) * 5ULL / 4ULL + 2ULL));
    uint32_t child_th_pn = th_pn;
    uint32_t child_th_dn = th_dn;
    if (is_or_node) {
      child_th_pn = std::min(th_pn, eps_bound);
      const uint64_t other_dn = cur_dn - mpc.dn;
      child_th_dn = (th_dn >= kPnDnSaturation)
                        ? kPnDnSaturation
                        : ((th_dn > other_dn)
                               ? std::max(2U, static_cast<uint32_t>(th_dn - other_dn))
                               : 1U);
    } else {
      const uint64_t other_pn = cur_pn - mpc.pn;
      child_th_pn = (th_pn >= kPnDnSaturation)
                        ? kPnDnSaturation
                        : ((th_pn > other_pn)
                               ? std::max(2U, static_cast<uint32_t>(th_pn - other_pn))
                               : 1U);
      child_th_dn = std::min(th_dn, eps_bound);
    }

    bool is_ko_capture = false;
    if (!pos.PlayMove(mpc.move, &is_ko_capture)) {
      *out_pn = 1;
      *out_dn = 1;
      *out_outcome = ProofOutcome::kUnknown;
      *out_dag_node_id = kInvalidDagNodeId;
      break;
    }

    bool child_ko_dep = false;
    MidSearch(pos, context, region_hint, child_th_pn, child_th_dn, depth + 1,
              in_path_hashes, &mpc.pn, &mpc.dn, &mpc.outcome, &child_ko_dep,
              &mpc.proof_rz, &mpc.disproof_rz, &mpc.dag_node_id, mpc.move);
    pos.UndoMove();

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
      mpc.expanded = false;
      *out_ko_dependent = true;
    } else {
      mpc.expanded = (mpc.outcome != ProofOutcome::kUnknown &&
                      mpc.dag_node_id != kInvalidDagNodeId);
    }

    // Record compact sibling certificate RZ for OutsideRZRevalidated pruning (FR-5.5).
    // Never seed OR-node active_null_move_rz from PASS_MOVE (DOUBLE_PASS_RESOLUTION)!
    if (!is_or_node && mpc.pn == 0 && mpc.dag_node_id != kInvalidDagNodeId &&
        mpc.proof_rz.Size() > 0 &&
        (!has_null_move_rz || mpc.proof_rz.Size() < active_null_move_rz.Size())) {
      active_null_move_rz = mpc.proof_rz;
      has_null_move_rz = true;
      representative_dag_id = mpc.dag_node_id;
      representative_outcome = ProofOutcome::kProvenWin;
    } else if (is_or_node && mpc.move != kPassMove && mpc.dn == 0 &&
               mpc.dag_node_id != kInvalidDagNodeId &&
               mpc.disproof_rz.Size() > 0 &&
               (!has_null_move_rz ||
                mpc.disproof_rz.Size() < active_null_move_rz.Size())) {
      active_null_move_rz = mpc.disproof_rz;
      has_null_move_rz = true;
      representative_dag_id = mpc.dag_node_id;
      representative_outcome = ProofOutcome::kProvenLoss;
    }
  }

  in_path_hashes.erase(pos.ZobristHash());
}

template class DfpnSolver<5>;
template class DfpnSolver<7>;
template class DfpnSolver<19>;

}  // namespace ldprover
