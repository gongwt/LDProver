// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/tt/transposition_table.h
// Description: Context-isolated BoardTT and Radix-Tree PatternTT (RZS-PT)
// conforming to FR-6.1..FR-6.9 and research notes Section 6.

#ifndef LDPROVER_TT_TRANSPOSITION_TABLE_H_
#define LDPROVER_TT_TRANSPOSITION_TABLE_H_

#include <array>
#include <cstdint>
#include <functional>
#include <memory>
#include <optional>
#include <unordered_map>
#include <vector>

#include "ldprover/core/position.h"
#include "ldprover/core/types.h"
#include "ldprover/rz/relevance_zone.h"

namespace ldprover {

template <int N = kDefaultBoardSize>
struct BoardTTEntry {
  uint64_t zobrist_hash = 0;
  uint64_t proof_context_id = 0;
  ProofContext full_context{};
  BitBoard<N> black_stones{};
  BitBoard<N> white_stones{};
  Color to_play = Color::kBlack;
  int16_t ko_point = kNullMove;
  uint8_t consecutive_passes = 0;
  uint64_t surviving_tokens_mask = 0;
  std::vector<CanonicalSnapshot<N>> history_snapshots;
  bool source_monotonic_history = false;
  bool has_capture_in_subtree = false;

  uint32_t pn = 1;
  uint32_t dn = 1;
  ProofOutcome outcome = ProofOutcome::kUnknown;
  bool is_ko_dependent = false;
  bool proof_closure_available = false;
  uint32_t proof_dag_node_id = 0;
  ProofCertificateRZ<N> proof_rz{};
  ProofCertificateRZ<N> disproof_rz{};
};

enum class PatternHitGrade : uint8_t {
  kMiss = 0,
  kHeuristicOnly = 1,   // Different history or non-closed: sorting hint only
  kProofReusable = 2,   // Identical HistorySet + ProofClosureAvailable (FR-6.3, FR-6.9)
};

// High-performance 4-branch Radix Tree for RZS-PT local pattern matching
// (0: EMPTY, 1: BLACK, 2: WHITE, 3: WILDCARD_OUTSIDE_RZ).
template <int N = kDefaultBoardSize>
struct RadixPatternRecord {
  uint64_t proof_context_id = 0;
  Color to_play = Color::kBlack;
  int16_t ko_point = kNullMove;
  uint8_t consecutive_passes = 0;
  uint64_t surviving_tokens_mask = 0;
  std::vector<CanonicalSnapshot<N>> history_snapshots;
  ProofCertificateRZ<N> stored_rz{};
  bool source_monotonic_history = false;
  bool has_capture_in_subtree = false;
  uint32_t pn = 1;
  uint32_t dn = 1;
  ProofOutcome outcome = ProofOutcome::kUnknown;
  uint32_t proof_dag_node_id = 0;
  bool proof_closure_available = false;
  bool ghi_flag = false;
  uint64_t last_touch_seq = 0;
};

struct TTProfileStats {
  uint64_t board_queries = 0;
  uint64_t board_bucket_hits = 0;
  uint64_t board_entries_scanned = 0;
  uint64_t board_exact_or_monotonic_hits = 0;
  uint64_t board_reval_entered = 0;
  uint64_t board_reval_succeeded = 0;
  uint64_t board_lookup_exclusive_ns = 0;
  uint64_t board_store_calls = 0;
  uint64_t board_store_ns = 0;

  uint64_t pattern_queries = 0;
  uint64_t pattern_entries_scanned = 0;
  uint64_t pattern_context_matched = 0;
  uint64_t pattern_geom_matched = 0;
  uint64_t pattern_direct_exact_hits = 0;
  uint64_t pattern_heuristic_hits = 0;
  uint64_t pattern_reval_entered = 0;
  uint64_t pattern_reval_succeeded = 0;
  uint64_t pattern_scan_exclusive_ns = 0;
  uint64_t pattern_store_calls = 0;
  uint64_t pattern_store_ns = 0;

  uint64_t board_bucket_count = 0;
  uint64_t board_total_entries = 0;
  uint64_t pattern_entry_count = 0;
};

template <int N = kDefaultBoardSize>
class TranspositionStore {
 public:
  using RevalidateFn = std::function<bool(uint32_t, ProofOutcome)>;

  TranspositionStore() = default;

  void SetProfilingEnabled(bool enabled) noexcept {
    profiling_enabled_ = enabled;
  }
  bool ProfilingEnabled() const noexcept { return profiling_enabled_; }
  TTProfileStats ProfileStats() const noexcept;

  // FR-6.2: Clear both tables at the start of every problem (no cross-problem TT).
  void ClearAll() noexcept;

  // FR-6.1: BoardTT lookup with monotonic history fast-path + GHI revalidation.
  std::optional<BoardTTEntry<N>> LookupBoardTT(
      const Position<N>& pos, const ProofContext& context,
      const RevalidateFn& revalidate_fn = {});

  void StoreBoardTT(const Position<N>& pos, const ProofContext& context,
                    uint32_t pn, uint32_t dn, ProofOutcome outcome,
                    bool is_ko_dependent, bool proof_closure_available,
                    uint32_t proof_dag_node_id,
                    const ProofCertificateRZ<N>& proof_rz,
                    const ProofCertificateRZ<N>& disproof_rz,
                    bool has_capture_in_subtree = false);

  // FR-6.3, FR-6.4, FR-6.6: Two-grade PatternTT lookup with multi-candidate revalidation.
  PatternHitGrade LookupPatternTT(
      const Position<N>& pos, const ProofContext& context,
      RadixPatternRecord<N>* out_record,
      const RevalidateFn& revalidate_fn = {});

  void StorePatternTT(const Position<N>& pos, const ProofContext& context,
                      const ProofCertificateRZ<N>& zone, uint32_t pn,
                      uint32_t dn, ProofOutcome outcome,
                      uint32_t proof_dag_node_id,
                      bool proof_closure_available,
                      bool has_capture_in_subtree = false);

  uint64_t BoardHits() const noexcept { return board_hits_; }
  uint64_t PatternHits() const noexcept { return pattern_hits_; }
  uint64_t PatternProofReusableHits() const noexcept {
    return pattern_proof_reusable_hits_;
  }
  uint64_t GhiRejectedCount() const noexcept { return ghi_rejected_count_; }
  size_t EstimatedEntryCount() const noexcept {
    return board_buckets_.size() + pattern_entries_.size();
  }

 private:
  struct RadixNode {
    std::vector<RadixPatternRecord<N>> terminal_records;
    std::array<std::unique_ptr<RadixNode>, 4> children{};
  };

  std::unordered_map<uint64_t, std::vector<BoardTTEntry<N>>> board_buckets_;
  std::unique_ptr<RadixNode> radix_root_ = std::make_unique<RadixNode>();
  std::vector<RadixPatternRecord<N>> pattern_entries_;
  uint64_t touch_seq_ = 0;
  uint64_t board_hits_ = 0;
  uint64_t pattern_hits_ = 0;
  uint64_t pattern_proof_reusable_hits_ = 0;
  uint64_t ghi_rejected_count_ = 0;
  bool profiling_enabled_ = false;
  TTProfileStats profile_stats_{};
};

}  // namespace ldprover

#endif  // LDPROVER_TT_TRANSPOSITION_TABLE_H_
