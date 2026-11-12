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
SolveReport<N> DfpnSolver<N>::Solve(
    const Position<N>& initial_pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint) {
  // FR-6.2: Clear BoardTT and PatternTT at the start of every problem.
  tt_store_.ClearAll();
  report_ = SolveReport<N>{};

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

  report_.board_tt_hits = tt_store_.BoardHits();
  report_.pattern_tt_hits = tt_store_.PatternHits();
  report_.pattern_proof_reusable = tt_store_.PatternProofReusableHits();
  report_.rz_size_at_root = report_.root_proof_rz.Size();
  return report_;
}

template <int N>
int32_t DfpnSolver<N>::ScoreMoveFastCapture(const Position<N>& pos,
                                            const ProofContext& context,
                                            int16_t move) const {
  if (move == kPassMove) return -1000;
  int32_t score = 0;

  // Prioritize moves adjacent to crucial stones or their liberties.
  for (size_t i = 0; i < context.initial_tokens.size() && i < 64; ++i) {
    if ((pos.SurvivingTargetTokensMask() & (1ULL << i)) == 0) continue;
    int t_coord = context.initial_tokens[i].initial_coord;
    BitBoard<N> libs;
    BitBoard<N> ch = pos.FloodFillChain(t_coord, &libs);
    if (libs.Get(move)) {
      score += 400;
      if (libs.Count() <= 2) score += 600;
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
    if (captured > 0) score += 1000 + captured * 250;

    BitBoard<N> our_libs;
    next.FloodFillChain(move, &our_libs);
    if (our_libs.Count() == 1) score -= 350;  // Self-atari penalty
    if (our_libs.Count() >= 3) score += 120;
  }
  return score;
}

template <int N>
bool DfpnSolver<N>::RevalidateSourceProofOnQueryState(
    const Position<N>& query_pos, const ProofContext& context,
    uint32_t source_dag_node_id, ProofOutcome expected_outcome) const {
  if (source_dag_node_id >= report_.proof_dag_nodes.size()) return false;
  const auto& node = report_.proof_dag_nodes[source_dag_node_id];
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

  if ((is_or && expected_outcome == ProofOutcome::kProvenWin) ||
      (!is_or && expected_outcome == ProofOutcome::kProvenLoss)) {
    // Witness replay: at least one recorded child witness must be legal and
    // replay cleanly on query_pos + HistorySet.
    for (size_t i = 0; i < node.child_node_ids.size(); ++i) {
      Position<N> next = query_pos;
      if (!next.PlayMove(node.child_moves[i])) continue;
      if (RevalidateSourceProofOnQueryState(
              next, context, node.child_node_ids[i], expected_outcome)) {
        return true;
      }
    }
    return false;
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

  // Step 4 (FR-6.1, FR-6.9): History-safe BoardTT lookup.
  if (auto hit = tt_store_.LookupBoardTT(pos, context); hit.has_value()) {
    if (hit->outcome != ProofOutcome::kUnknown && hit->proof_closure_available) {
      *out_pn = hit->pn;
      *out_dn = hit->dn;
      *out_outcome = hit->outcome;
      *out_proof_rz = hit->proof_rz;
      *out_disproof_rz = hit->disproof_rz;
      *out_dag_node_id = hit->proof_dag_node_id;
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
            ? ScoreMoveFastCapture(pos, context, mv)
            : 0;
    children.push_back(ch);
  }
  if (config_.enable_fast_capture_ordering) {
    std::stable_sort(
        children.begin(), children.end(),
        [](const SearchChild& a, const SearchChild& b) {
          return a.tactical_score > b.tactical_score;
        });
  }

  in_path_hashes.insert(pos.ZobristHash());

  uint32_t widening_level = 0;
  ProofCertificateRZ<N> active_null_move_rz;
  bool has_null_move_rz = false;
  uint32_t representative_dag_id = 0;
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
      for (size_t i = 0; i < window_size; ++i) {
        auto& ch = children[i];
        if (ch.expanded || ch.outcome != ProofOutcome::kUnknown) continue;
        if (rz_engine_.IsOutsideRZCandidate(ch.move, active_null_move_rz)) {
          Position<N> next_pos = pos;
          if (next_pos.PlayMove(ch.move) &&
              RevalidateSourceProofOnQueryState(
                  next_pos, context, representative_dag_id,
                  representative_outcome)) {
            ch.expanded = true;
            ch.pruned_outside_rz = true;
            ch.outcome = representative_outcome;
            ch.pn = (representative_outcome == ProofOutcome::kProvenWin)
                        ? 0
                        : kPnDnSaturation;
            ch.dn = (representative_outcome == ProofOutcome::kProvenWin)
                        ? kPnDnSaturation
                        : 0;
            ch.proof_rz = active_null_move_rz;
            ch.disproof_rz = active_null_move_rz;
            ch.dag_node_id = representative_dag_id;
            ++report_.pruned_outside_rz_count;
          }
        }
      }
    }

    // FR-4.1: Frontier PN/DN aggregation with implicit unexpanded cost U.
    const size_t unexpanded_u =
        (total_legal > window_size) ? (total_legal - window_size) : 0;
    uint32_t cur_pn = 1;
    uint32_t cur_dn = 1;

    if (is_or_node) {
      uint32_t min_pn =
          (unexpanded_u > 0) ? 1U : kPnDnSaturation;  // Implicit child = 1
      uint64_t sum_dn = unexpanded_u;
      for (size_t i = 0; i < window_size; ++i) {
        min_pn = std::min(min_pn, children[i].pn);
        sum_dn += children[i].dn;
      }
      cur_pn = min_pn;
      cur_dn = ClampSat(sum_dn);
    } else {
      uint64_t sum_pn = unexpanded_u;
      uint32_t min_dn =
          (unexpanded_u > 0) ? 1U : kPnDnSaturation;  // Implicit child = 1
      for (size_t i = 0; i < window_size; ++i) {
        sum_pn += children[i].pn;
        min_dn = std::min(min_dn, children[i].dn);
      }
      cur_pn = ClampSat(sum_pn);
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

      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome =
          (cur_pn == 0) ? ProofOutcome::kProvenWin : ProofOutcome::kProvenLoss;

      // Backpropagate dual-chain Relevance Zone (FR-5.2, FR-5.3).
      if (is_or_node && cur_pn == 0) {
        for (const auto& ch : children) {
          if (ch.pn == 0) {
            *out_proof_rz = rz_engine_.ComputeSingleWitnessRZ(
                pos, ch.move, ch.proof_rz);
            if (depth == 0) report_.best_move = ch.move;
            break;
          }
        }
      } else if (!is_or_node && cur_dn == 0) {
        for (const auto& ch : children) {
          if (ch.dn == 0) {
            *out_disproof_rz = rz_engine_.ComputeSingleWitnessRZ(
                pos, ch.move, ch.disproof_rz);
            if (depth == 0) report_.best_move = ch.move;
            break;
          }
        }
      } else if (is_or_node && cur_dn == 0) {
        std::vector<ProofCertificateRZ<N>> child_rzs;
        for (const auto& ch : children) child_rzs.push_back(ch.disproof_rz);
        *out_disproof_rz =
            rz_engine_.ComputeAllChildrenUnionRZ(pos, child_rzs);
      } else {
        std::vector<ProofCertificateRZ<N>> child_rzs;
        for (const auto& ch : children) child_rzs.push_back(ch.proof_rz);
        *out_proof_rz = rz_engine_.ComputeAllChildrenUnionRZ(pos, child_rzs);
      }

      ProofDagNode<N> dag_node;
      dag_node.node_id = static_cast<uint32_t>(report_.proof_dag_nodes.size());
      dag_node.is_or_node = is_or_node;
      dag_node.incoming_move = incoming_move;
      dag_node.pn = *out_pn;
      dag_node.dn = *out_dn;
      dag_node.outcome = *out_outcome;
      dag_node.proof_rz = *out_proof_rz;
      dag_node.disproof_rz = *out_disproof_rz;
      for (const auto& ch : children) {
        if (ch.expanded) {
          dag_node.child_node_ids.push_back(ch.dag_node_id);
          dag_node.child_moves.push_back(ch.move);
        }
      }
      report_.proof_dag_nodes.push_back(dag_node);
      *out_dag_node_id = dag_node.node_id;

      tt_store_.StoreBoardTT(pos, context, *out_pn, *out_dn, *out_outcome,
                             *out_ko_dependent, true, *out_dag_node_id,
                             *out_proof_rz, *out_disproof_rz);
      break;
    }

    // Threshold cutoff check (FR-4.3: OR condition).
    if (cur_pn >= th_pn || cur_dn >= th_dn ||
        report_.num_nodes >= config_.max_nodes) {
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

    // If implicit unexpanded child has smaller metric (1), widen window (FR-4.4).
    if (unexpanded_u > 0 && best_metric > 1) {
      ++widening_level;
      ++report_.widening_upgrades;
      continue;
    }

    if (best_idx < 0 || best_metric >= kPnDnSaturation) {
      *out_pn = cur_pn;
      *out_dn = cur_dn;
      *out_outcome = ProofOutcome::kUnknown;
      break;
    }

    auto& mpc = children[best_idx];
    uint32_t child_th_pn = th_pn;
    uint32_t child_th_dn = th_dn;
    if (is_or_node) {
      child_th_pn = std::min(th_pn, ClampSat(static_cast<uint64_t>(second_best_metric) + 1));
      const uint64_t other_dn = cur_dn - mpc.dn;
      child_th_dn = (th_dn > other_dn) ? static_cast<uint32_t>(th_dn - other_dn) : 1U;
    } else {
      const uint64_t other_pn = cur_pn - mpc.pn;
      child_th_pn = (th_pn > other_pn) ? static_cast<uint32_t>(th_pn - other_pn) : 1U;
      child_th_dn = std::min(th_dn, ClampSat(static_cast<uint64_t>(second_best_metric) + 1));
    }

    bool is_ko_capture = false;
    if (!pos.PlayMove(mpc.move, &is_ko_capture)) {
      mpc.pn = is_or_node ? kPnDnSaturation : 0;
      mpc.dn = is_or_node ? 0 : kPnDnSaturation;
      continue;
    }

    bool child_ko_dep = false;
    MidSearch(pos, context, region_hint, child_th_pn, child_th_dn, depth + 1,
              in_path_hashes, &mpc.pn, &mpc.dn, &mpc.outcome, &child_ko_dep,
              &mpc.proof_rz, &mpc.disproof_rz, &mpc.dag_node_id, mpc.move);
    pos.UndoMove();
    mpc.expanded = true;

    // FR-5.7: KoDependent witness barrier check.
    if (is_ko_capture) {
      const bool restricted_side =
          (pos.ToPlay() == context.root_attacker && !context.attacker_allow_ko) ||
          (pos.ToPlay() != context.root_attacker && !context.defender_allow_ko);
      if (restricted_side &&
          ((is_or_node && mpc.pn == 0) || (!is_or_node && mpc.dn == 0))) {
        mpc.ko_dependent = true;
        mpc.outcome = ProofOutcome::kUnknown;
        mpc.pn = kPnDnSaturation / 2;
        mpc.dn = kPnDnSaturation / 2;
        *out_ko_dependent = true;
      }
    }

    // Record sibling certificate RZ for OutsideRZRevalidated pruning (FR-5.5).
    if (!is_or_node && mpc.pn == 0 && mpc.proof_rz.Size() > 0) {
      active_null_move_rz = mpc.proof_rz;
      has_null_move_rz = true;
      representative_dag_id = mpc.dag_node_id;
      representative_outcome = ProofOutcome::kProvenWin;
    } else if (is_or_node && mpc.dn == 0 && mpc.disproof_rz.Size() > 0) {
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
