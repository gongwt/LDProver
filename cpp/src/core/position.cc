// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/core/position.cc
// Description: Implementation of Position<N> board state, Zobrist hashing,
// Situational Superko (SSK) / Positional Superko (PSK) canonical history verification,
// and non-revivable target token maintenance (FR-2.1..FR-2.6).

#include "ldprover/core/position.h"

#include <array>
#include <queue>

namespace ldprover {

namespace {

// Deterministic SplitMix64 Zobrist table generator (NFR-4 reproducibility).
constexpr uint64_t SplitMix64(uint64_t seed) noexcept {
  uint64_t z = seed + 0x9E3779B97F4A7C15ULL;
  z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
  z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
  return z ^ (z >> 31);
}

struct ZobristTable {
  std::array<std::array<uint64_t, kMaxBoardPoints>, 3> stone_keys{};
  std::array<uint64_t, kMaxBoardPoints> ko_keys{};
  uint64_t white_to_play_key = 0;

  constexpr ZobristTable() noexcept {
    // Aligned 1:1 with TypeScript src/engine/position.ts Zobrist table (R3 F5).
    for (int p = 0; p < kMaxBoardPoints; ++p) {
      stone_keys[1][p] = SplitMix64(1000ULL + static_cast<uint64_t>(p));
      stone_keys[2][p] = SplitMix64(2000ULL + static_cast<uint64_t>(p));
      ko_keys[p] = SplitMix64(3000ULL + static_cast<uint64_t>(p));
    }
    white_to_play_key = SplitMix64(9999ULL);
  }
};

constexpr ZobristTable kZobrist{};

template <int N>
struct OrthoNeighborTable {
  std::array<typename Position<N>::OrthoNeighborList, N * N> entries{};

  constexpr OrthoNeighborTable() noexcept {
    for (int coord = 0; coord < N * N; ++coord) {
      const int r = coord / N;
      const int c = coord % N;
      auto& e = entries[coord];
      uint8_t k = 0;
      if (r > 0) e.coords[k++] = static_cast<int16_t>((r - 1) * N + c);
      if (r + 1 < N) e.coords[k++] = static_cast<int16_t>((r + 1) * N + c);
      if (c > 0) e.coords[k++] = static_cast<int16_t>(r * N + (c - 1));
      if (c + 1 < N) e.coords[k++] = static_cast<int16_t>(r * N + (c + 1));
      e.count = k;
    }
  }
};

template <int N>
inline constexpr OrthoNeighborTable<N> kOrthoNeighbors{};

}  // namespace

template <int N>
Position<N>::Position() noexcept {
  Clear(ProofContext{});
}

template <int N>
Position<N>::Position(const ProofContext& context) noexcept {
  Clear(context);
}

template <int N>
void Position<N>::Clear(const ProofContext& context) noexcept {
  context_ = context;
  black_stones_.Clear();
  white_stones_.Clear();
  immortal_wall_.Clear();
  to_play_ = Color::kBlack;
  ko_point_ = kNullMove;
  consecutive_passes_ = 0;
  surviving_target_tokens_mask_ = 0;
  for (size_t i = 0; i < context_.initial_tokens.size() && i < 64; ++i) {
    surviving_target_tokens_mask_ |= (1ULL << i);
  }
  history_snapshots_.clear();
  undo_stack_.clear();
  origin_black_.Clear();
  origin_white_.Clear();
  origin_to_play_ = Color::kBlack;
  played_move_trace_.clear();
  zobrist_hash_ = ComputeZobrist();
}

template <int N>
void Position<N>::SetupInitialStone(int coord, Color color) noexcept {
  if (coord < 0 || coord >= N * N) return;
  black_stones_.Reset(coord);
  white_stones_.Reset(coord);
  if (color == Color::kBlack) black_stones_.Set(coord, true);
  if (color == Color::kWhite) white_stones_.Set(coord, true);
}

template <int N>
void Position<N>::FinalizeInitialPosition(Color first_to_play) noexcept {
  to_play_ = first_to_play;
  ko_point_ = kNullMove;
  consecutive_passes_ = 0;
  surviving_target_tokens_mask_ = 0;
  for (size_t i = 0; i < context_.initial_tokens.size() && i < 64; ++i) {
    const auto& tok = context_.initial_tokens[i];
    if (StoneAt(tok.initial_coord) == tok.stone_color) {
      surviving_target_tokens_mask_ |= (1ULL << i);
    }
  }
  origin_black_ = black_stones_;
  origin_white_ = white_stones_;
  origin_to_play_ = first_to_play;
  played_move_trace_.clear();
  zobrist_hash_ = ComputeZobrist();
  history_snapshots_.clear();
  history_snapshots_.push_back(CurrentCanonicalSnapshot());
}

template <int N>
Color Position<N>::StoneAt(int coord) const noexcept {
  if (black_stones_.Get(coord)) return Color::kBlack;
  if (white_stones_.Get(coord)) return Color::kWhite;
  return Color::kEmpty;
}

template <int N>
uint64_t Position<N>::ComputeZobrist() const noexcept {
  uint64_t h = 0;
  for (int i = 0; i < N * N; ++i) {
    if (black_stones_.Get(i)) h ^= kZobrist.stone_keys[1][i];
    if (white_stones_.Get(i)) h ^= kZobrist.stone_keys[2][i];
  }
  if (to_play_ == Color::kWhite) h ^= kZobrist.white_to_play_key;
  if (ko_point_ >= 0 && ko_point_ < N * N) h ^= kZobrist.ko_keys[ko_point_];
  return h;
}

template <int N>
typename Position<N>::OrthoNeighborList
Position<N>::PrecomputedOrthogonalNeighborsForTest(int coord) noexcept {
  if (coord < 0 || coord >= N * N) return OrthoNeighborList{};
  return kOrthoNeighbors<N>.entries[coord];
}

template <int N>
std::vector<int> Position<N>::OrthogonalNeighbors(int coord) const {
  std::vector<int> nb;
  nb.reserve(4);
  const int r = RowOf(coord);
  const int c = ColOf(coord);
  if (r > 0) nb.push_back(CoordFromRowCol(r - 1, c));
  if (r + 1 < N) nb.push_back(CoordFromRowCol(r + 1, c));
  if (c > 0) nb.push_back(CoordFromRowCol(r, c - 1));
  if (c + 1 < N) nb.push_back(CoordFromRowCol(r, c + 1));
  return nb;
}

template <int N>
std::vector<int> Position<N>::DiagonalNeighbors(int coord) const {
  std::vector<int> nb;
  nb.reserve(4);
  const int r = RowOf(coord);
  const int c = ColOf(coord);
  if (r > 0 && c > 0) nb.push_back(CoordFromRowCol(r - 1, c - 1));
  if (r > 0 && c + 1 < N) nb.push_back(CoordFromRowCol(r - 1, c + 1));
  if (r + 1 < N && c > 0) nb.push_back(CoordFromRowCol(r + 1, c - 1));
  if (r + 1 < N && c + 1 < N) nb.push_back(CoordFromRowCol(r + 1, c + 1));
  return nb;
}

template <int N>
BitBoard<N> Position<N>::FloodFillChain(int start_coord,
                                        BitBoard<N>* out_liberties) const {
  BitBoard<N> chain;
  if (out_liberties != nullptr) out_liberties->Clear();
  if (start_coord < 0 || start_coord >= N * N) return chain;
  const Color color = StoneAt(start_coord);
  if (color == Color::kEmpty) return chain;

  std::queue<int> q;
  q.push(start_coord);
  chain.Set(start_coord, true);

  while (!q.empty()) {
    const int cur = q.front();
    q.pop();
    const auto& nbs = kOrthoNeighbors<N>.entries[cur];
    for (uint8_t i = 0; i < nbs.count; ++i) {
      const int nb = nbs.coords[i];
      const Color nb_color = StoneAt(nb);
      if (nb_color == Color::kEmpty) {
        if (out_liberties != nullptr) out_liberties->Set(nb, true);
      } else if (nb_color == color && !chain.Get(nb)) {
        chain.Set(nb, true);
        q.push(nb);
      }
    }
  }
  return chain;
}

template <int N>
bool Position<N>::ViolatesSuperko(int16_t move) const noexcept {
  if (move == kPassMove || context_.ko_rule == KoRule::kSimpleKoOnly) {
    return false;
  }
  Position<N> probe = *this;
  if (!probe.PlayMove(move)) return true;
  const CanonicalSnapshot<N> next_snap = probe.CurrentCanonicalSnapshot();
  // Compare against all prior canonical snapshots (exclude the one just pushed).
  for (size_t i = 0; i + 1 < probe.history_snapshots_.size(); ++i) {
    if (probe.history_snapshots_[i].MatchesUnderRule(next_snap,
                                                     context_.ko_rule)) {
      return true;
    }
  }
  return false;
}

template <int N>
bool Position<N>::IsLegalMove(int16_t move) const noexcept {
  if (move == kPassMove) return !IsAtDoublePass();
  if (move < 0 || move >= N * N) return false;
  if (StoneAt(move) != Color::kEmpty) return false;
  if (move == ko_point_) return false;

  Position<N> scratch = *this;
  return scratch.PlayMove(move);
}

template <int N>
bool Position<N>::PlayMove(int16_t move, bool* out_is_ko_capture) noexcept {
  if (out_is_ko_capture != nullptr) *out_is_ko_capture = false;
  if (IsAtDoublePass()) return false;

  UndoRecord<N> undo{
      move,
      to_play_,
      ko_point_,
      consecutive_passes_,
      zobrist_hash_,
      surviving_target_tokens_mask_,
      black_stones_,
      white_stones_,
      false,
  };

  if (move == kPassMove) {
    uint64_t next_hash = zobrist_hash_;
    if (undo.prev_ko_point >= 0 && undo.prev_ko_point < N * N) {
      next_hash ^= kZobrist.ko_keys[undo.prev_ko_point];
    }
    next_hash ^= kZobrist.white_to_play_key;
    ko_point_ = kNullMove;
    ++consecutive_passes_;
    to_play_ = OppositeColor(to_play_);
    zobrist_hash_ = next_hash;
    undo_stack_.push_back(undo);
    played_move_trace_.push_back(kPassMove);
    history_snapshots_.push_back(CurrentCanonicalSnapshot());
    return true;
  }

  if (move < 0 || move >= N * N || StoneAt(move) != Color::kEmpty ||
      move == ko_point_) {
    return false;
  }

  const Color us = to_play_;
  const Color them = OppositeColor(us);
  const int us_idx = (us == Color::kBlack) ? 1 : 2;
  const int them_idx = (them == Color::kBlack) ? 1 : 2;
  uint64_t next_hash = zobrist_hash_;
  if (undo.prev_ko_point >= 0 && undo.prev_ko_point < N * N) {
    next_hash ^= kZobrist.ko_keys[undo.prev_ko_point];
  }
  next_hash ^= kZobrist.stone_keys[us_idx][move];
  if (us == Color::kBlack) {
    black_stones_.Set(move, true);
  } else {
    white_stones_.Set(move, true);
  }

  BitBoard<N> captured_stones;
  int last_captured_coord = kNullMove;
  const auto& move_nbs = kOrthoNeighbors<N>.entries[move];
  for (uint8_t i = 0; i < move_nbs.count; ++i) {
    const int nb = move_nbs.coords[i];
    if (StoneAt(nb) == them && !captured_stones.Get(nb)) {
      BitBoard<N> liberties;
      BitBoard<N> enemy_chain = FloodFillChain(nb, &liberties);
      if (liberties.None() && !(enemy_chain & immortal_wall_).Any()) {
        captured_stones |= enemy_chain;
      }
    }
  }

  const int num_captured = captured_stones.Count();
  if (num_captured > 0) {
    for (int coord : captured_stones.ToCoords()) {
      last_captured_coord = coord;
      black_stones_.Reset(coord);
      white_stones_.Reset(coord);
      next_hash ^= kZobrist.stone_keys[them_idx][coord];
      // FR-2.6: Permanently clear captured target tokens (non-revivable).
      for (size_t t = 0; t < context_.initial_tokens.size() && t < 64; ++t) {
        if (context_.initial_tokens[t].initial_coord == coord) {
          surviving_target_tokens_mask_ &= ~(1ULL << t);
        }
      }
    }
  }

  BitBoard<N> our_liberties;
  BitBoard<N> our_chain = FloodFillChain(move, &our_liberties);
  if (our_liberties.None()) {
    // Suicide is strictly forbidden (FR-2.1, C-2). Restore state.
    black_stones_ = undo.prev_black;
    white_stones_ = undo.prev_white;
    surviving_target_tokens_mask_ = undo.prev_surviving_tokens_mask;
    return false;
  }

  // Detect simple ko point.
  int16_t next_ko = kNullMove;
  if (num_captured == 1 && our_chain.Count() == 1 &&
      our_liberties.Count() == 1) {
    next_ko = static_cast<int16_t>(last_captured_coord);
    undo.captured_Via_ko = true;
    if (out_is_ko_capture != nullptr) *out_is_ko_capture = true;
  }

  if (next_ko >= 0 && next_ko < N * N) {
    next_hash ^= kZobrist.ko_keys[next_ko];
  }
  next_hash ^= kZobrist.white_to_play_key;

  ko_point_ = next_ko;
  consecutive_passes_ = 0;
  to_play_ = them;
  zobrist_hash_ = next_hash;

  // FR-2.2: Enforce SSK/PSK against full canonical history snapshots.
  if (context_.ko_rule != KoRule::kSimpleKoOnly) {
    const CanonicalSnapshot<N> next_snap = CurrentCanonicalSnapshot();
    for (const auto& past : history_snapshots_) {
      if (past.MatchesUnderRule(next_snap, context_.ko_rule)) {
        black_stones_ = undo.prev_black;
        white_stones_ = undo.prev_white;
        to_play_ = undo.played_color;
        ko_point_ = undo.prev_ko_point;
        consecutive_passes_ = undo.prev_consecutive_passes;
        zobrist_hash_ = undo.prev_zobrist_hash;
        surviving_target_tokens_mask_ = undo.prev_surviving_tokens_mask;
        return false;
      }
    }
  }

  undo_stack_.push_back(undo);
  played_move_trace_.push_back(move);
  history_snapshots_.push_back(CurrentCanonicalSnapshot());
  return true;
}

template <int N>
void Position<N>::UndoMove() noexcept {
  if (undo_stack_.empty()) return;
  const UndoRecord<N> rec = undo_stack_.back();
  undo_stack_.pop_back();
  if (!played_move_trace_.empty()) played_move_trace_.pop_back();
  if (!history_snapshots_.empty()) history_snapshots_.pop_back();

  black_stones_ = rec.prev_black;
  white_stones_ = rec.prev_white;
  to_play_ = rec.played_color;
  ko_point_ = rec.prev_ko_point;
  consecutive_passes_ = rec.prev_consecutive_passes;
  zobrist_hash_ = rec.prev_zobrist_hash;
  surviving_target_tokens_mask_ = rec.prev_surviving_tokens_mask;
}

template <int N>
std::vector<int16_t> Position<N>::GenerateLegalMoves(
    const std::optional<BitBoard<N>>& region_filter) const {
  std::vector<int16_t> moves;
  if (IsAtDoublePass()) return moves;

  Position<N> scratch = *this;
  for (int coord = 0; coord < N * N; ++coord) {
    if (region_filter.has_value() && !region_filter->Get(coord)) continue;
    if (scratch.StoneAt(coord) != Color::kEmpty) continue;
    if (coord == scratch.ko_point_) continue;
    if (scratch.PlayMove(static_cast<int16_t>(coord))) {
      moves.push_back(static_cast<int16_t>(coord));
      scratch.UndoMove();
    }
  }
  moves.push_back(kPassMove);  // FR-2.3: pass is always legal before double-pass
  return moves;
}

template <int N>
bool Position<N>::HasIdenticalHistorySet(
    const Position<N>& other) const noexcept {
  if (history_snapshots_.size() != other.history_snapshots_.size()) {
    return false;
  }
  for (size_t i = 0; i < history_snapshots_.size(); ++i) {
    bool found = false;
    for (size_t j = 0; j < other.history_snapshots_.size(); ++j) {
      if (history_snapshots_[i].MatchesUnderRule(other.history_snapshots_[j],
                                                 context_.ko_rule)) {
        found = true;
        break;
      }
    }
    if (!found) return false;
  }
  return true;
}

template class Position<5>;
template class Position<7>;
template class Position<19>;

}  // namespace ldprover
