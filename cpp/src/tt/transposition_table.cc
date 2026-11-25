// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/tt/transposition_table.cc
// Description: Implementation of Context-Isolated BoardTT and Radix-Tree
// PatternTT (FR-6.1..FR-6.9).

#include "ldprover/tt/transposition_table.h"

#include <chrono>

namespace ldprover {

namespace {

using SteadyClock = std::chrono::steady_clock;

uint64_t ElapsedNs(SteadyClock::time_point t0,
                   SteadyClock::time_point t1) noexcept {
  const auto diff =
      std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0).count();
  return diff > 0 ? static_cast<uint64_t>(diff) : 0ULL;
}

}  // namespace

template <int N>
TTProfileStats TranspositionStore<N>::ProfileStats() const noexcept {
  TTProfileStats out = profile_stats_;
  out.board_bucket_count = static_cast<uint64_t>(board_buckets_.size());
  uint64_t total_board = 0;
  for (const auto& kv : board_buckets_) {
    total_board += static_cast<uint64_t>(kv.second.size());
  }
  out.board_total_entries = total_board;
  out.pattern_entry_count = static_cast<uint64_t>(pattern_entries_.size());
  return out;
}

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
  profile_stats_ = TTProfileStats{};
}

template <int N>
std::optional<BoardTTEntry<N>> TranspositionStore<N>::LookupBoardTT(
    const Position<N>& pos, const ProofContext& context,
    const RevalidateFn& revalidate_fn) {
  const bool prof = profiling_enabled_;
  const SteadyClock::time_point fn_t0 =
      prof ? SteadyClock::now() : SteadyClock::time_point{};
  uint64_t scanned = 0;
  uint64_t reval_cb_ns = 0;
  struct Guard {
    bool enabled;
    SteadyClock::time_point t0;
    uint64_t* scanned_ptr;
    uint64_t* cb_ns_ptr;
    TTProfileStats* stats;
    ~Guard() {
      if (!enabled) return;
      const uint64_t total_ns = ElapsedNs(t0, SteadyClock::now());
      stats->board_entries_scanned += *scanned_ptr;
      stats->board_lookup_exclusive_ns +=
          (total_ns > *cb_ns_ptr) ? (total_ns - *cb_ns_ptr) : 0ULL;
    }
  } guard{prof, fn_t0, &scanned, &reval_cb_ns, &profile_stats_};

  if (prof) ++profile_stats_.board_queries;

  auto it = board_buckets_.find(pos.ZobristHash());
  if (it == board_buckets_.end()) return std::nullopt;
  if (prof) ++profile_stats_.board_bucket_hits;

  const bool query_monotonic = pos.IsCaptureFreeMonotonicHistory();

  for (const auto& entry : it->second) {
    if (prof) ++scanned;
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
    bool via_reval = false;
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
            bool reval_ok = false;
            if (prof) {
              ++profile_stats_.board_reval_entered;
              const auto r0 = SteadyClock::now();
              reval_ok = revalidate_fn(entry.proof_dag_node_id, entry.outcome);
              reval_cb_ns += ElapsedNs(r0, SteadyClock::now());
            } else {
              reval_ok = revalidate_fn(entry.proof_dag_node_id, entry.outcome);
            }
            if (!reval_ok) {
              ++ghi_rejected_count_;
              continue;
            }
            via_reval = true;
          } else {
            continue;
          }
        }
      }
    }

    if (prof) {
      if (via_reval) {
        ++profile_stats_.board_reval_succeeded;
      } else {
        ++profile_stats_.board_exact_or_monotonic_hits;
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

  const bool prof = profiling_enabled_;
  const SteadyClock::time_point fn_t0 =
      prof ? SteadyClock::now() : SteadyClock::time_point{};
  struct StoreGuard {
    bool enabled;
    SteadyClock::time_point t0;
    TTProfileStats* stats;
    ~StoreGuard() {
      if (!enabled) return;
      ++stats->board_store_calls;
      stats->board_store_ns += ElapsedNs(t0, SteadyClock::now());
    }
  } guard{prof, fn_t0, &profile_stats_};

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
  const bool prof = profiling_enabled_;
  const SteadyClock::time_point fn_t0 =
      prof ? SteadyClock::now() : SteadyClock::time_point{};
  uint64_t scanned = 0;
  uint64_t ctx_matched = 0;
  uint64_t reval_cb_ns = 0;
  struct Guard {
    bool enabled;
    SteadyClock::time_point t0;
    uint64_t* scanned_ptr;
    uint64_t* ctx_ptr;
    uint64_t* cb_ns_ptr;
    TTProfileStats* stats;
    ~Guard() {
      if (!enabled) return;
      const uint64_t total_ns = ElapsedNs(t0, SteadyClock::now());
      stats->pattern_entries_scanned += *scanned_ptr;
      stats->pattern_context_matched += *ctx_ptr;
      stats->pattern_scan_exclusive_ns +=
          (total_ns > *cb_ns_ptr) ? (total_ns - *cb_ns_ptr) : 0ULL;
    }
  } guard{prof, fn_t0, &scanned, &ctx_matched, &reval_cb_ns, &profile_stats_};

  if (prof) ++profile_stats_.pattern_queries;

  const RadixPatternRecord<N>* first_heuristic = nullptr;
  int reval_attempts = 0;
  constexpr int kMaxRevalAttempts = 6;

  for (size_t idx = pattern_entries_.size(); idx-- > 0;) {
    if (prof) ++scanned;
    auto& rec = pattern_entries_[idx];
    if (rec.proof_context_id != context.context_id ||
        rec.to_play != pos.ToPlay() ||
        rec.consecutive_passes != pos.ConsecutivePasses() ||
        rec.surviving_tokens_mask != pos.SurvivingTargetTokensMask()) {
      continue;
    }
    if (prof) ++ctx_matched;

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
    if (prof) ++profile_stats_.pattern_geom_matched;

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
      if (prof) ++profile_stats_.pattern_direct_exact_hits;
      if (out_record != nullptr) *out_record = rec;
      return PatternHitGrade::kProofReusable;
    }

    if (revalidate_fn && rec.proof_closure_available && !rec.ghi_flag &&
        reval_attempts < kMaxRevalAttempts) {
      ++reval_attempts;
      bool reval_ok = false;
      if (prof) {
        ++profile_stats_.pattern_reval_entered;
        const auto r0 = SteadyClock::now();
        reval_ok = revalidate_fn(rec.proof_dag_node_id, rec.outcome);
        reval_cb_ns += ElapsedNs(r0, SteadyClock::now());
      } else {
        reval_ok = revalidate_fn(rec.proof_dag_node_id, rec.outcome);
      }
      if (reval_ok) {
        ++pattern_proof_reusable_hits_;
        if (prof) ++profile_stats_.pattern_reval_succeeded;
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
    if (prof) ++profile_stats_.pattern_heuristic_hits;
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
  const bool prof = profiling_enabled_;
  const SteadyClock::time_point fn_t0 =
      prof ? SteadyClock::now() : SteadyClock::time_point{};
  struct StoreGuard {
    bool enabled;
    SteadyClock::time_point t0;
    TTProfileStats* stats;
    ~StoreGuard() {
      if (!enabled) return;
      ++stats->pattern_store_calls;
      stats->pattern_store_ns += ElapsedNs(t0, SteadyClock::now());
    }
  } guard{prof, fn_t0, &profile_stats_};
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
