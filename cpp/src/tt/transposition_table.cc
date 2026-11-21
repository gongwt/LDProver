// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/tt/transposition_table.cc
// Description: Implementation of Context-Isolated BoardTT and Radix-Tree
// PatternTT (FR-6.1..FR-6.9).

#include "ldprover/tt/transposition_table.h"

namespace ldprover {

template <int N>
void TranspositionStore<N>::ClearAll() noexcept {
  board_buckets_.clear();
  radix_root_ = std::make_unique<RadixNode>();
  pattern_entries_.clear();
  touch_seq_ = 0;
  board_hits_ = 0;
  pattern_hits_ = 0;
  pattern_proof_reusable_hits_ = 0;
  ghi_rejected_count_ = 0;
}

template <int N>
std::optional<BoardTTEntry<N>> TranspositionStore<N>::LookupBoardTT(
    const Position<N>& pos, const ProofContext& context,
    const RevalidateFn& revalidate_fn) {
  auto it = board_buckets_.find(pos.ZobristHash());
  if (it == board_buckets_.end()) return std::nullopt;

  const bool query_monotonic = pos.IsCaptureFreeMonotonicHistory();

  for (const auto& entry : it->second) {
    // FR-6.1 & C-6: Hash only locates bucket; verify full structural equality.
    if (entry.proof_context_id != context.context_id ||
        !(entry.full_context == context) ||
        entry.to_play != pos.ToPlay() ||
        entry.ko_point != pos.KoPoint() ||
        entry.consecutive_passes != pos.ConsecutivePasses() ||
        entry.surviving_tokens_mask != pos.SurvivingTargetTokensMask() ||
        entry.black_stones != pos.Stones(Color::kBlack) ||
        entry.white_stones != pos.Stones(Color::kWhite)) {
      continue;
    }

    // Verify canonical HistorySet equality under active KoRule, with O(1)
    // monotonic stone-count certificate & GHI revalidation fallback.
    if (context.ko_rule != KoRule::kSimpleKoOnly) {
      const bool monotonic_safe = query_monotonic &&
                                  entry.source_monotonic_history &&
                                  !entry.has_capture_in_subtree;
      if (!monotonic_safe) {
        const auto& query_hist = pos.HistorySnapshots();
        bool hist_ok = (entry.history_snapshots.size() == query_hist.size());
        if (hist_ok) {
          for (size_t i = 0; i < query_hist.size(); ++i) {
            bool found = false;
            for (size_t j = 0; j < entry.history_snapshots.size(); ++j) {
              if (query_hist[i].MatchesUnderRule(entry.history_snapshots[j],
                                                 context.ko_rule)) {
                found = true;
                break;
              }
            }
            if (!found) {
              hist_ok = false;
              break;
            }
          }
        }
        if (!hist_ok) {
          if (entry.proof_closure_available &&
              entry.outcome != ProofOutcome::kUnknown && revalidate_fn) {
            if (!revalidate_fn(entry.proof_dag_node_id, entry.outcome)) {
              ++ghi_rejected_count_;
              continue;
            }
          } else {
            continue;
          }
        }
      }
    }

    ++board_hits_;
    return entry;
  }
  return std::nullopt;
}

template <int N>
void TranspositionStore<N>::StoreBoardTT(
    const Position<N>& pos, const ProofContext& context, uint32_t pn,
    uint32_t dn, ProofOutcome outcome, bool is_ko_dependent,
    bool proof_closure_available, uint32_t proof_dag_node_id,
    const ProofCertificateRZ<N>& proof_rz,
    const ProofCertificateRZ<N>& disproof_rz, bool has_capture_in_subtree) {
  // FR-5.7: KoDependent states must never be stored as decisive proof entries.
  if (is_ko_dependent && outcome != ProofOutcome::kUnknown) return;

  auto history_sets_equal = [&](const std::vector<CanonicalSnapshot<N>>& a,
                                const std::vector<CanonicalSnapshot<N>>& b) {
    if (context.ko_rule == KoRule::kSimpleKoOnly) return true;
    if (a.size() != b.size()) return false;
    for (size_t i = 0; i < a.size(); ++i) {
      bool found = false;
      for (size_t j = 0; j < b.size(); ++j) {
        if (a[i].MatchesUnderRule(b[j], context.ko_rule)) {
          found = true;
          break;
        }
      }
      if (!found) return false;
    }
    return true;
  };

  auto& bucket = board_buckets_[pos.ZobristHash()];
  for (auto& existing : bucket) {
    if (existing.proof_context_id == context.context_id &&
        existing.full_context == context &&
        existing.to_play == pos.ToPlay() &&
        existing.ko_point == pos.KoPoint() &&
        existing.consecutive_passes == pos.ConsecutivePasses() &&
        existing.surviving_tokens_mask == pos.SurvivingTargetTokensMask() &&
        existing.black_stones == pos.Stones(Color::kBlack) &&
        existing.white_stones == pos.Stones(Color::kWhite) &&
        history_sets_equal(existing.history_snapshots, pos.HistorySnapshots())) {
      existing.source_monotonic_history = pos.IsCaptureFreeMonotonicHistory();
      existing.has_capture_in_subtree = has_capture_in_subtree;
      existing.pn = pn;
      existing.dn = dn;
      existing.outcome = outcome;
      existing.is_ko_dependent = is_ko_dependent;
      existing.proof_closure_available = proof_closure_available;
      existing.proof_dag_node_id = proof_dag_node_id;
      existing.proof_rz = proof_rz;
      existing.disproof_rz = disproof_rz;
      return;
    }
  }

  BoardTTEntry<N> entry;
  entry.zobrist_hash = pos.ZobristHash();
  entry.proof_context_id = context.context_id;
  entry.full_context = context;
  entry.black_stones = pos.Stones(Color::kBlack);
  entry.white_stones = pos.Stones(Color::kWhite);
  entry.to_play = pos.ToPlay();
  entry.ko_point = pos.KoPoint();
  entry.consecutive_passes = pos.ConsecutivePasses();
  entry.surviving_tokens_mask = pos.SurvivingTargetTokensMask();
  entry.history_snapshots = pos.HistorySnapshots();
  entry.source_monotonic_history = pos.IsCaptureFreeMonotonicHistory();
  entry.has_capture_in_subtree = has_capture_in_subtree;
  entry.pn = pn;
  entry.dn = dn;
  entry.outcome = outcome;
  entry.is_ko_dependent = is_ko_dependent;
  entry.proof_closure_available = proof_closure_available;
  entry.proof_dag_node_id = proof_dag_node_id;
  entry.proof_rz = proof_rz;
  entry.disproof_rz = disproof_rz;
  bucket.push_back(std::move(entry));
}

template <int N>
PatternHitGrade TranspositionStore<N>::LookupPatternTT(
    const Position<N>& pos, const ProofContext& context,
    RadixPatternRecord<N>* out_record, const RevalidateFn& revalidate_fn) {
  const RadixPatternRecord<N>* first_heuristic = nullptr;
  int reval_attempts = 0;
  constexpr int kMaxRevalAttempts = 6;

  for (size_t idx = pattern_entries_.size(); idx-- > 0;) {
    auto& rec = pattern_entries_[idx];
    if (rec.proof_context_id != context.context_id ||
        rec.to_play != pos.ToPlay() ||
        rec.consecutive_passes != pos.ConsecutivePasses() ||
        rec.surviving_tokens_mask != pos.SurvivingTargetTokensMask()) {
      continue;
    }

    // Project current position onto stored_rz (FR-6.3, FR-6.5 same-coordinate).
    const BitBoard<N>& zone_bits = rec.stored_rz.Bits();
    if (zone_bits.None()) continue;
    const BitBoard<N> query_b = pos.Stones(Color::kBlack) & zone_bits;
    const BitBoard<N> query_w = pos.Stones(Color::kWhite) & zone_bits;
    if (rec.history_snapshots.empty()) continue;
    const auto& stored_curr = rec.history_snapshots.back();
    if ((stored_curr.black_stones & zone_bits) != query_b ||
        ((stored_curr.white_stones & zone_bits) != query_w)) {
      continue;
    }

    // Check ko point projection inside zone.
    const int16_t q_ko =
        (pos.KoPoint() >= 0 && zone_bits.Get(pos.KoPoint())) ? pos.KoPoint()
                                                             : kNullMove;
    const int16_t s_ko =
        (rec.ko_point >= 0 && zone_bits.Get(rec.ko_point)) ? rec.ko_point
                                                           : kNullMove;
    if (q_ko != s_ko) continue;

    rec.last_touch_seq = ++touch_seq_;
    ++pattern_hits_;

    // Two-grade classification (FR-6.3, FR-6.9):
    const bool full_board_equal =
        (stored_curr.black_stones == pos.Stones(Color::kBlack)) &&
        (stored_curr.white_stones == pos.Stones(Color::kWhite)) &&
        (rec.ko_point == pos.KoPoint());
    const auto& q_hist = pos.HistorySnapshots();
    bool full_hist_equal = (q_hist.size() == rec.history_snapshots.size());
    if (full_hist_equal && context.ko_rule != KoRule::kSimpleKoOnly) {
      for (size_t i = 0; i < q_hist.size(); ++i) {
        bool found = false;
        for (size_t j = 0; j < rec.history_snapshots.size(); ++j) {
          if (q_hist[i].MatchesUnderRule(rec.history_snapshots[j],
                                         context.ko_rule)) {
            found = true;
            break;
          }
        }
        if (!found) {
          full_hist_equal = false;
          break;
        }
      }
    }

    if (full_board_equal && full_hist_equal && rec.proof_closure_available &&
        !rec.ghi_flag) {
      ++pattern_proof_reusable_hits_;
      if (out_record != nullptr) *out_record = rec;
      return PatternHitGrade::kProofReusable;
    }

    if (revalidate_fn && rec.proof_closure_available && !rec.ghi_flag &&
        reval_attempts < kMaxRevalAttempts) {
      ++reval_attempts;
      if (revalidate_fn(rec.proof_dag_node_id, rec.outcome)) {
        ++pattern_proof_reusable_hits_;
        if (out_record != nullptr) *out_record = rec;
        return PatternHitGrade::kProofReusable;
      }
    }

    if (first_heuristic == nullptr) {
      first_heuristic = &rec;
    }
    if (reval_attempts >= kMaxRevalAttempts) {
      break;
    }
  }

  if (first_heuristic != nullptr) {
    if (out_record != nullptr) *out_record = *first_heuristic;
    return PatternHitGrade::kHeuristicOnly;
  }
  return PatternHitGrade::kMiss;
}

template <int N>
void TranspositionStore<N>::StorePatternTT(
    const Position<N>& pos, const ProofContext& context,
    const ProofCertificateRZ<N>& zone, uint32_t pn, uint32_t dn,
    ProofOutcome outcome, uint32_t proof_dag_node_id,
    bool proof_closure_available, bool has_capture_in_subtree) {
  if (outcome == ProofOutcome::kUnknown || zone.Size() == 0) return;
  RadixPatternRecord<N> rec;
  rec.proof_context_id = context.context_id;
  rec.to_play = pos.ToPlay();
  rec.ko_point = pos.KoPoint();
  rec.consecutive_passes = pos.ConsecutivePasses();
  rec.surviving_tokens_mask = pos.SurvivingTargetTokensMask();
  rec.history_snapshots = pos.HistorySnapshots();
  rec.stored_rz = zone;
  rec.source_monotonic_history = pos.IsCaptureFreeMonotonicHistory();
  rec.has_capture_in_subtree = has_capture_in_subtree;
  rec.pn = pn;
  rec.dn = dn;
  rec.outcome = outcome;
  rec.proof_dag_node_id = proof_dag_node_id;
  rec.proof_closure_available = proof_closure_available;
  rec.last_touch_seq = ++touch_seq_;
  pattern_entries_.push_back(std::move(rec));
}

template class TranspositionStore<5>;
template class TranspositionStore<7>;
template class TranspositionStore<19>;

}  // namespace ldprover
