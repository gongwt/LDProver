// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/core/position.h
// Description: Go board Position<N> with incremental Play/Undo, Zobrist hash
// (including side-to-move and simple ko), SSK/PSK canonical HistorySet,
// consecutivePasses, and non-revivable surviving_target_tokens (FR-2.1..FR-2.6).

#ifndef LDPROVER_CORE_POSITION_H_
#define LDPROVER_CORE_POSITION_H_

#include <cstdint>
#include <optional>
#include <vector>

#include "ldprover/core/types.h"

namespace ldprover {

template <int N = kDefaultBoardSize>
struct UndoRecord {
  int16_t move = kPassMove;
  Color played_color = Color::kBlack;
  int16_t prev_ko_point = kNullMove;
  uint8_t prev_consecutive_passes = 0;
  uint64_t prev_zobrist_hash = 0;
  uint64_t prev_surviving_tokens_mask = 0;
  BitBoard<N> prev_black;
  BitBoard<N> prev_white;
  bool captured_Via_ko = false;
};

template <int N = kDefaultBoardSize>
class Position {
 public:
  Position() noexcept;
  explicit Position(const ProofContext& context) noexcept;

  static constexpr int CoordFromRowCol(int row, int col) noexcept {
    return row * N + col;
  }
  static constexpr int RowOf(int coord) noexcept { return coord / N; }
  static constexpr int ColOf(int coord) noexcept { return coord % N; }

  void Clear(const ProofContext& context) noexcept;
  void SetupInitialStone(int coord, Color color) noexcept;
  void SetImmortalWall(const BitBoard<N>& wall) noexcept {
    immortal_wall_ = wall;
  }
  void FinalizeInitialPosition(Color first_to_play) noexcept;

  Color StoneAt(int coord) const noexcept;
  Color ToPlay() const noexcept { return to_play_; }
  int16_t KoPoint() const noexcept { return ko_point_; }
  uint8_t ConsecutivePasses() const noexcept { return consecutive_passes_; }
  bool IsAtDoublePass() const noexcept { return consecutive_passes_ >= 2; }
  uint64_t ZobristHash() const noexcept { return zobrist_hash_; }
  uint64_t SurvivingTargetTokensMask() const noexcept {
    return surviving_target_tokens_mask_;
  }
  const BitBoard<N>& ImmortalWall() const noexcept { return immortal_wall_; }

  const BitBoard<N>& Stones(Color color) const noexcept {
    return color == Color::kBlack ? black_stones_ : white_stones_;
  }
  BitBoard<N> EmptyPoints() const noexcept {
    return ~(black_stones_ | white_stones_);
  }

  // FR-2.1, FR-2.2, FR-2.5: Legal move & Superko checks.
  bool IsLegalMove(int16_t move) const noexcept;
  bool ViolatesSuperko(int16_t move) const noexcept;
  std::vector<int16_t> GenerateLegalMoves(
      const std::optional<BitBoard<N>>& region_filter = std::nullopt) const;

  // FR-2.4, FR-2.6: Incremental Play and Undo with full history & token tracking.
  bool PlayMove(int16_t move, bool* out_is_ko_capture = nullptr) noexcept;
  void UndoMove() noexcept;

  // FR-6.1, FR-6.3: Exact canonical HistorySet equality verification.
  const std::vector<CanonicalSnapshot<N>>& HistorySnapshots() const noexcept {
    return history_snapshots_;
  }
  bool HasIdenticalHistorySet(const Position<N>& other) const noexcept;

  CanonicalSnapshot<N> CurrentCanonicalSnapshot() const noexcept {
    return CanonicalSnapshot<N>{black_stones_, white_stones_, to_play_,
                                zobrist_hash_};
  }

  std::vector<int> OrthogonalNeighbors(int coord) const;
  BitBoard<N> FloodFillChain(int start_coord, BitBoard<N>* out_liberties) const;

 private:
  uint64_t ComputeZobrist() const noexcept;

  ProofContext context_{};
  BitBoard<N> black_stones_{};
  BitBoard<N> white_stones_{};
  BitBoard<N> immortal_wall_{};
  Color to_play_ = Color::kBlack;
  int16_t ko_point_ = kNullMove;
  uint8_t consecutive_passes_ = 0;
  uint64_t zobrist_hash_ = 0;
  uint64_t surviving_target_tokens_mask_ = 0;
  std::vector<CanonicalSnapshot<N>> history_snapshots_;
  std::vector<UndoRecord<N>> undo_stack_;
};

}  // namespace ldprover

#endif  // LDPROVER_CORE_POSITION_H_
