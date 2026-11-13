// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: include/ldprover/core/types.h
// Description: Core value types, BitBoard<N> template, Ruleset, TargetToken,
// and ProofContext definitions conforming to LDProver SRS v1.8 (FR-2, FR-4, C-6, C-7)
// and Google C++ Style Guide.

#ifndef LDPROVER_CORE_TYPES_H_
#define LDPROVER_CORE_TYPES_H_

#include <array>
#include <bitset>
#include <cstdint>
#include <optional>
#include <string>
#include <vector>

namespace ldprover {

inline constexpr int kDefaultBoardSize = 19;
inline constexpr int kMaxBoardPoints = kDefaultBoardSize * kDefaultBoardSize;
inline constexpr int16_t kPassMove = -1;
inline constexpr int16_t kNullMove = -2;
inline constexpr uint32_t kPnDnSaturation = 1073741823U;  // SAT constant per §4.1

enum class Color : uint8_t {
  kEmpty = 0,
  kBlack = 1,
  kWhite = 2,
};

constexpr Color OppositeColor(Color color) noexcept {
  if (color == Color::kBlack) return Color::kWhite;
  if (color == Color::kWhite) return Color::kBlack;
  return Color::kEmpty;
}

enum class KoRule : uint8_t {
  kSituationalSuperko = 0,  // Default SSK (FR-2.2, C-2)
  kPositionalSuperko = 1,   // Internal experiment switch (PSK)
  kSimpleKoOnly = 2,        // Internal experiment switch (None)
};

enum class SearchGoal : uint8_t {
  kToLive = 0,  // TOLIVE: target group achieves Benson UCA or survives double-pass
  kToKill = 1,  // TOKILL: dual of TOLIVE
};

enum class LogicalOp : uint8_t {
  kSingle = 0,
  kConjunction = 1,  // '&' all target token groups must satisfy goal
  kDisjunction = 2,  // '|' at least one target token group must satisfy goal
};

// Four-valued terminal evaluation outcome (FR-3.2).
// Note: Does NOT emit domain labels like DEAD/ALIVE/SEKI.
enum class TerminalStatus : uint8_t {
  kWin = 0,
  kLoss = 1,
  kNonTerminal = 2,
  kUnsupported = 3,
};

// Root proposition three-valued result (FR-4.8).
enum class ProofOutcome : uint8_t {
  kProvenWin = 0,
  kProvenLoss = 1,
  kUnknown = 2,
};

// Explicit non-decisive barrier and budget reasons (FR-4.7, FR-4.8, FR-5.7).
enum class UnknownReason : uint8_t {
  kNone = 0,
  kTimeout = 1,
  kNodeLimit = 2,
  kMemoryBudget = 3,
  kDepthLimit = 4,
  kCycle = 5,
  kKoDependent = 6,
  kWideningStalled = 7,
  kInternalError = 8,
};

// Templated BitBoard<N> supporting <= 19 board sizes (Constraint C-7).
template <int N = kDefaultBoardSize>
class BitBoard {
 public:
  static constexpr int kNumPoints = N * N;

  constexpr BitBoard() noexcept = default;

  bool Get(int idx) const noexcept { return bits_.test(static_cast<size_t>(idx)); }
  void Set(int idx, bool val = true) noexcept {
    bits_.set(static_cast<size_t>(idx), val);
  }
  void Reset(int idx) noexcept { bits_.reset(static_cast<size_t>(idx)); }
  void Clear() noexcept { bits_.reset(); }

  int Count() const noexcept { return static_cast<int>(bits_.count()); }
  bool Any() const noexcept { return bits_.any(); }
  bool None() const noexcept { return bits_.none(); }

  bool IsSubsetOf(const BitBoard<N>& other) const noexcept {
    return (bits_ & ~other.bits_).none();
  }
  bool Intersects(const BitBoard<N>& other) const noexcept {
    return (bits_ & other.bits_).any();
  }

  BitBoard<N> operator|(const BitBoard<N>& rhs) const noexcept {
    BitBoard<N> out;
    out.bits_ = bits_ | rhs.bits_;
    return out;
  }
  BitBoard<N> operator&(const BitBoard<N>& rhs) const noexcept {
    BitBoard<N> out;
    out.bits_ = bits_ & rhs.bits_;
    return out;
  }
  BitBoard<N> operator~() const noexcept {
    BitBoard<N> out;
    out.bits_ = ~bits_;
    return out;
  }
  BitBoard<N>& operator|=(const BitBoard<N>& rhs) noexcept {
    bits_ |= rhs.bits_;
    return *this;
  }
  BitBoard<N>& operator&=(const BitBoard<N>& rhs) noexcept {
    bits_ &= rhs.bits_;
    return *this;
  }
  bool operator==(const BitBoard<N>& rhs) const noexcept {
    return bits_ == rhs.bits_;
  }
  bool operator!=(const BitBoard<N>& rhs) const noexcept {
    return bits_ != rhs.bits_;
  }

  std::vector<int> ToCoords() const {
    std::vector<int> coords;
    coords.reserve(Count());
    for (int i = 0; i < kNumPoints; ++i) {
      if (bits_.test(static_cast<size_t>(i))) coords.push_back(i);
    }
    return coords;
  }

 private:
  std::bitset<kNumPoints> bits_{};
};

// Canonical board snapshot for exact SSK/PSK history comparison (FR-2.2).
// Hash is used strictly as an index; equality requires full BitBoard comparison.
template <int N = kDefaultBoardSize>
struct CanonicalSnapshot {
  BitBoard<N> black_stones;
  BitBoard<N> white_stones;
  Color to_play = Color::kBlack;
  uint64_t zobrist_hash = 0;

  bool MatchesUnderRule(const CanonicalSnapshot<N>& other,
                        KoRule rule) const noexcept {
    if (black_stones != other.black_stones ||
        white_stones != other.white_stones) {
      return false;
    }
    if (rule == KoRule::kSituationalSuperko) {
      return to_play == other.to_play;
    }
    return true;  // PSK compares only B/W bitmaps
  }
};

// Non-revivable initial target stone token (FR-2.6).
// Encoded by initial coordinate; once captured, permanently removed.
struct TargetToken {
  uint16_t token_id = 0;
  int16_t initial_coord = 0;
  uint8_t group_index = 0;
  Color stone_color = Color::kBlack;

  bool operator==(const TargetToken& other) const noexcept {
    return token_id == other.token_id &&
           initial_coord == other.initial_coord &&
           group_index == other.group_index &&
           stone_color == other.stone_color;
  }
};

// Structured ProofContext (C-6, FR-6.1, FR-6.2, FR-9.1).
// context_id is a fast 64-bit fingerprint; hits must verify full equality.
struct ProofContext {
  uint64_t context_id = 0;
  Color root_attacker = Color::kBlack;
  SearchGoal attacker_goal = SearchGoal::kToLive;
  LogicalOp crucial_stone_op = LogicalOp::kSingle;
  KoRule ko_rule = KoRule::kSituationalSuperko;
  bool attacker_allow_ko = false;
  bool defender_allow_ko = false;
  std::vector<TargetToken> initial_tokens;

  bool operator==(const ProofContext& other) const noexcept {
    return context_id == other.context_id &&
           root_attacker == other.root_attacker &&
           attacker_goal == other.attacker_goal &&
           crucial_stone_op == other.crucial_stone_op &&
           ko_rule == other.ko_rule &&
           attacker_allow_ko == other.attacker_allow_ko &&
           defender_allow_ko == other.defender_allow_ko &&
           initial_tokens == other.initial_tokens;
  }
};

}  // namespace ldprover

#endif  // LDPROVER_CORE_TYPES_H_
