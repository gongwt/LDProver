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
  uint32_t pn = 1;
  uint32_t dn = 1;
  ProofOutcome outcome = ProofOutcome::kUnknown;
  uint32_t proof_dag_node_id = 0;
  bool proof_closure_available = false;
  bool ghi_flag = false;
  uint64_t last_touch_seq = 0;
};

template <int N = kDefaultBoardSize>
class TranspositionStore {
 public:
  TranspositionStore() = default;

  // FR-6.2: Clear both tables at the start of every problem (no cross-problem TT).
  void ClearAll() noexcept;

  // FR-6.1: BoardTT lookup with full canonical HistorySet + ProofContext equality.
  std::optional<BoardTTEntry<N>> LookupBoardTT(
      const Position<N>& pos, const ProofContext& context);

  void StoreBoardTT(const Position<N>& pos, const ProofContext& context,
                    uint32_t pn, uint32_t dn, ProofOutcome outcome,
                    bool is_ko_dependent, bool proof_closure_available,
                    uint32_t proof_dag_node_id,
                    const ProofCertificateRZ<N>& proof_rz,
                    const ProofCertificateRZ<N>& disproof_rz);

  // FR-6.3, FR-6.4, FR-6.6: Two-grade PatternTT lookup via Radix Tree.
  PatternHitGrade LookupPatternTT(
      const Position<N>& pos, const ProofContext& context,
      RadixPatternRecord<N>* out_record);

  void StorePatternTT(const Position<N>& pos, const ProofContext& context,
                      const ProofCertificateRZ<N>& zone, uint32_t pn,
                      uint32_t dn, ProofOutcome outcome,
                      uint32_t proof_dag_node_id,
                      bool proof_closure_available);

  uint64_t BoardHits() const noexcept { return board_hits_; }
  uint64_t PatternHits() const noexcept { return pattern_hits_; }
  uint64_t PatternProofReusableHits() const noexcept {
    return pattern_proof_reusable_hits_;
  }
  uint64_t GhiRejectedCount() const noexcept { return ghi_rejected_count_; }

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
};

}  // namespace ldprover

#endif  // LDPROVER_TT_TRANSPOSITION_TABLE_H_
