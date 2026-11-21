// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/core/problem_parser.cc
// Description: Implementation of strict tsumego/*.json contract parser
// (FR-1.1..FR-1.3) loading AB/AW stones, region masks, immortal boundary walls,
// and validated crucial_stone target tokens.

#include "ldprover/core/problem_parser.h"

#include <cctype>
#include <cstdint>
#include <map>
#include <string>
#include <vector>

namespace ldprover {

namespace {

std::string TrimAscii(const std::string& s) {
  size_t b = 0;
  while (b < s.size() && std::isspace(static_cast<unsigned char>(s[b]))) ++b;
  size_t e = s.size();
  while (e > b && std::isspace(static_cast<unsigned char>(s[e - 1]))) --e;
  return s.substr(b, e - b);
}

std::string UpperAscii(std::string s) {
  for (char& c : s) {
    c = static_cast<char>(std::toupper(static_cast<unsigned char>(c)));
  }
  return s;
}

uint64_t Fnv1a64String(const std::string& s) noexcept {
  uint64_t h = 14695981039346656037ULL;
  for (unsigned char c : s) {
    h ^= static_cast<uint64_t>(c);
    h *= 1099511628211ULL;
  }
  return h;
}

int ParseSgfCoord(const std::string& tok, int board_size) noexcept {
  if (tok.size() != 2) return -1;
  const int col = static_cast<int>(tok[0]) - static_cast<int>('a');
  const int row = static_cast<int>(tok[1]) - static_cast<int>('a');
  if (col < 0 || col >= board_size || row < 0 || row >= board_size) return -1;
  return row * board_size + col;
}

void ExtractSgfPropertyCoords(const std::string& sgf, const std::string& prop,
                              int board_size, std::vector<int>* out_coords) {
  size_t pos = 0;
  while (pos < sgf.size()) {
    const size_t found = sgf.find(prop + "[", pos);
    if (found == std::string::npos) break;
    if (found > 0 &&
        std::isupper(static_cast<unsigned char>(sgf[found - 1]))) {
      pos = found + prop.size();
      continue;
    }
    size_t cur = found + prop.size();
    while (cur < sgf.size()) {
      while (cur < sgf.size() &&
             std::isspace(static_cast<unsigned char>(sgf[cur]))) {
        ++cur;
      }
      if (cur >= sgf.size() || sgf[cur] != '[') break;
      const size_t close = sgf.find(']', cur + 1);
      if (close == std::string::npos) break;
      const std::string inner = TrimAscii(sgf.substr(cur + 1, close - cur - 1));
      const int coord = ParseSgfCoord(inner, board_size);
      if (coord >= 0) out_coords->push_back(coord);
      cur = close + 1;
    }
    pos = cur;
  }
}

bool ValidateSgfStructureAndSize(const std::string& sgf, int expected_size,
                                 std::string* out_err_code,
                                 std::string* out_err_msg) {
  const std::string trimmed = TrimAscii(sgf);
  if (trimmed.size() < 3U || trimmed.substr(0U, 2U) != "(;" ||
      trimmed.back() != ')') {
    *out_err_code = "FR1-INVALID-SGF";
    *out_err_msg = "masked_sgf_str must start with '(;' and end with ')'.";
    return false;
  }
  int paren_depth = 0;
  bool in_bracket = false;
  bool escaped = false;
  for (size_t i = 0; i < trimmed.size(); ++i) {
    const char ch = trimmed[i];
    if (in_bracket) {
      if (escaped) {
        escaped = false;
      } else if (ch == '\\') {
        escaped = true;
      } else if (ch == ']') {
        in_bracket = false;
      }
      continue;
    }
    if (ch == '[') {
      in_bracket = true;
    } else if (ch == ']') {
      *out_err_code = "FR1-INVALID-SGF";
      *out_err_msg = "Unmatched ']' in masked_sgf_str.";
      return false;
    } else if (ch == '(') {
      ++paren_depth;
    } else if (ch == ')') {
      --paren_depth;
      if (paren_depth < 0) {
        *out_err_code = "FR1-INVALID-SGF";
        *out_err_msg = "Unbalanced parentheses in masked_sgf_str.";
        return false;
      }
    }
  }
  if (in_bracket || paren_depth != 0) {
    *out_err_code = "FR1-INVALID-SGF";
    *out_err_msg = "Unclosed bracket or parenthesis in masked_sgf_str.";
    return false;
  }

  // Validate SZ[...] if present matches expected board size N.
  size_t sz_pos = 0;
  while ((sz_pos = trimmed.find("SZ[", sz_pos)) != std::string::npos) {
    if (sz_pos > 0 &&
        std::isupper(static_cast<unsigned char>(trimmed[sz_pos - 1U]))) {
      sz_pos += 3U;
      continue;
    }
    const size_t close = trimmed.find(']', sz_pos + 3U);
    if (close == std::string::npos) {
      *out_err_code = "FR1-INVALID-SGF";
      *out_err_msg = "Unclosed SZ[...] property in masked_sgf_str.";
      return false;
    }
    const std::string sz_str = TrimAscii(trimmed.substr(sz_pos + 3U, close - sz_pos - 3U));
    if (sz_str.empty()) {
      *out_err_code = "FR1-INVALID-BOARD-SIZE";
      *out_err_msg = "Empty SZ[] property in masked_sgf_str.";
      return false;
    }
    int parsed_sz = 0;
    for (char ch : sz_str) {
      if (!std::isdigit(static_cast<unsigned char>(ch))) {
        *out_err_code = "FR1-INVALID-BOARD-SIZE";
        *out_err_msg = "Non-numeric SZ property: " + sz_str;
        return false;
      }
      parsed_sz = parsed_sz * 10 + static_cast<int>(ch - '0');
    }
    if (parsed_sz != expected_size) {
      *out_err_code = "FR1-BOARD-SIZE-MISMATCH";
      *out_err_msg = "SGF SZ[" + sz_str + "] does not match solver board size " +
                     std::to_string(expected_size) + ".";
      return false;
    }
    break;
  }

  // Validate AB[...], AW[...], and MA[...] coordinate tokens fall within expected_size.
  for (const std::string& prop :
       {std::string("AB"), std::string("AW"), std::string("MA")}) {
    size_t p = 0;
    while (p < trimmed.size()) {
      const size_t found = trimmed.find(prop + "[", p);
      if (found == std::string::npos) break;
      if (found > 0 &&
          std::isupper(static_cast<unsigned char>(trimmed[found - 1U]))) {
        p = found + prop.size();
        continue;
      }
      size_t cur = found + prop.size();
      while (cur < trimmed.size()) {
        while (cur < trimmed.size() &&
               std::isspace(static_cast<unsigned char>(trimmed[cur]))) {
          ++cur;
        }
        if (cur >= trimmed.size() || trimmed[cur] != '[') break;
        const size_t close = trimmed.find(']', cur + 1U);
        if (close == std::string::npos) {
          *out_err_code = "FR1-INVALID-SGF";
          *out_err_msg = "Unclosed " + prop + "[...] property in masked_sgf_str.";
          return false;
        }
        const std::string inner =
            TrimAscii(trimmed.substr(cur + 1U, close - cur - 1U));
        if (ParseSgfCoord(inner, expected_size) < 0) {
          *out_err_code = "FR1-INVALID-SGF";
          *out_err_msg = "Invalid or out-of-bounds " + prop + " coordinate [" +
                         inner + "] for board size " +
                         std::to_string(expected_size) + ".";
          return false;
        }
        cur = close + 1U;
      }
      p = cur;
    }
  }
  return true;
}

// Strict RFC 8259 recursive-descent JSON parser for top-level problem objects (R3 F6.2).
class StrictProblemJsonParser {
 public:
  explicit StrictProblemJsonParser(const std::string& src) : src_(src) {}

  bool ParseTopLevelObject(std::map<std::string, std::string>* out_str_fields) {
    SkipWs();
    if (pos_ >= src_.size() || src_[pos_] != '{') return false;
    if (!ParseObject(out_str_fields, true)) return false;
    SkipWs();
    return pos_ == src_.size();
  }

 private:
  void SkipWs() {
    while (pos_ < src_.size() &&
           std::isspace(static_cast<unsigned char>(src_[pos_]))) {
      ++pos_;
    }
  }

  bool ParseString(std::string* out) {
    if (pos_ >= src_.size() || src_[pos_] != '"') return false;
    ++pos_;
    std::string res;
    while (pos_ < src_.size()) {
      const unsigned char uch = static_cast<unsigned char>(src_[pos_++]);
      if (uch < 0x20U) return false;  // Unescaped control char illegal in RFC 8259
      if (uch == '"') {
        if (out != nullptr) *out = std::move(res);
        return true;
      }
      if (uch == '\\') {
        if (pos_ >= src_.size()) return false;
        const char esc = src_[pos_++];
        switch (esc) {
          case '"':
          case '\\':
          case '/':
            res.push_back(esc);
            break;
          case 'b':
            res.push_back('\b');
            break;
          case 'f':
            res.push_back('\f');
            break;
          case 'n':
            res.push_back('\n');
            break;
          case 'r':
            res.push_back('\r');
            break;
          case 't':
            res.push_back('\t');
            break;
          case 'u': {
            if (pos_ + 4U > src_.size()) return false;
            uint32_t cp = 0;
            for (int k = 0; k < 4; ++k) {
              const char hc = src_[pos_++];
              cp <<= 4U;
              if (hc >= '0' && hc <= '9') cp |= static_cast<uint32_t>(hc - '0');
              else if (hc >= 'a' && hc <= 'f') cp |= static_cast<uint32_t>(hc - 'a' + 10);
              else if (hc >= 'A' && hc <= 'F') cp |= static_cast<uint32_t>(hc - 'A' + 10);
              else return false;
            }
            if (cp < 0x80U) {
              res.push_back(static_cast<char>(cp));
            } else if (cp < 0x800U) {
              res.push_back(static_cast<char>(0xC0U | (cp >> 6U)));
              res.push_back(static_cast<char>(0x80U | (cp & 0x3FU)));
            } else {
              res.push_back(static_cast<char>(0xE0U | (cp >> 12U)));
              res.push_back(static_cast<char>(0x80U | ((cp >> 6U) & 0x3FU)));
              res.push_back(static_cast<char>(0x80U | (cp & 0x3FU)));
            }
            break;
          }
          default:
            return false;
        }
      } else {
        res.push_back(static_cast<char>(uch));
      }
    }
    return false;
  }

  bool ParseNumber() {
    if (pos_ < src_.size() && src_[pos_] == '-') ++pos_;
    if (pos_ >= src_.size()) return false;
    if (src_[pos_] == '0') {
      ++pos_;
    } else if (src_[pos_] >= '1' && src_[pos_] <= '9') {
      while (pos_ < src_.size() &&
             std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
        ++pos_;
      }
    } else {
      return false;
    }
    if (pos_ < src_.size() && src_[pos_] == '.') {
      ++pos_;
      if (pos_ >= src_.size() ||
          !std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
        return false;
      }
      while (pos_ < src_.size() &&
             std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
        ++pos_;
      }
    }
    if (pos_ < src_.size() && (src_[pos_] == 'e' || src_[pos_] == 'E')) {
      ++pos_;
      if (pos_ < src_.size() && (src_[pos_] == '+' || src_[pos_] == '-')) {
        ++pos_;
      }
      if (pos_ >= src_.size() ||
          !std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
        return false;
      }
      while (pos_ < src_.size() &&
             std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
        ++pos_;
      }
    }
    return true;
  }

  bool ParseValue(std::string* out_if_string, bool* out_is_string) {
    if (out_is_string != nullptr) *out_is_string = false;
    SkipWs();
    if (pos_ >= src_.size()) return false;
    const char c = src_[pos_];
    if (c == '"') {
      std::string s;
      if (!ParseString(&s)) return false;
      if (out_if_string != nullptr) *out_if_string = std::move(s);
      if (out_is_string != nullptr) *out_is_string = true;
      return true;
    }
    if (c == '{') return ParseObject(nullptr, false);
    if (c == '[') return ParseArray();
    if (c == 't') {
      if (src_.compare(pos_, 4U, "true") != 0) return false;
      pos_ += 4U;
      return true;
    }
    if (c == 'f') {
      if (src_.compare(pos_, 5U, "false") != 0) return false;
      pos_ += 5U;
      return true;
    }
    if (c == 'n') {
      if (src_.compare(pos_, 4U, "null") != 0) return false;
      pos_ += 4U;
      return true;
    }
    if (c == '-' || std::isdigit(static_cast<unsigned char>(c))) {
      return ParseNumber();
    }
    return false;
  }

  bool ParseArray() {
    if (pos_ >= src_.size() || src_[pos_] != '[') return false;
    ++pos_;
    SkipWs();
    if (pos_ < src_.size() && src_[pos_] == ']') {
      ++pos_;
      return true;
    }
    while (pos_ < src_.size()) {
      if (!ParseValue(nullptr, nullptr)) return false;
      SkipWs();
      if (pos_ < src_.size() && src_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < src_.size() && src_[pos_] == ']') {
        ++pos_;
        return true;
      }
      return false;
    }
    return false;
  }

  bool ParseObject(std::map<std::string, std::string>* out_str_fields,
                   bool collect_strings) {
    if (pos_ >= src_.size() || src_[pos_] != '{') return false;
    ++pos_;
    SkipWs();
    if (pos_ < src_.size() && src_[pos_] == '}') {
      ++pos_;
      return true;
    }
    while (pos_ < src_.size()) {
      SkipWs();
      std::string key;
      if (!ParseString(&key)) return false;
      SkipWs();
      if (pos_ >= src_.size() || src_[pos_] != ':') return false;
      ++pos_;
      std::string str_val;
      bool is_str = false;
      if (!ParseValue(collect_strings ? &str_val : nullptr,
                      collect_strings ? &is_str : nullptr)) {
        return false;
      }
      if (collect_strings && out_str_fields != nullptr && is_str) {
        (*out_str_fields)[key] = std::move(str_val);
      }
      SkipWs();
      if (pos_ < src_.size() && src_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < src_.size() && src_[pos_] == '}') {
        ++pos_;
        return true;
      }
      return false;
    }
    return false;
  }

  const std::string& src_;
  size_t pos_ = 0;
};

bool HasMixedLogicalOps(const std::string& expr) {
  const bool has_and = expr.find('&') != std::string::npos;
  const bool has_or =
      (expr.find('|') != std::string::npos) ||
      (expr.find(',') != std::string::npos);
  return has_and && has_or;
}

std::vector<std::string> SplitCrucialTokens(const std::string& expr) {
  std::vector<std::string> out;
  std::string cur;
  for (char ch : expr) {
    if (ch == '&' || ch == '|' || ch == ',') {
      const std::string trimmed = TrimAscii(cur);
      if (!trimmed.empty()) out.push_back(trimmed);
      cur.clear();
    } else {
      cur.push_back(ch);
    }
  }
  const std::string last = TrimAscii(cur);
  if (!last.empty()) out.push_back(last);
  return out;
}

}  // namespace

template <int N>
ParsedProblem<N> ProblemContractParser<N>::ParseTsumegoJson(
    const std::string& problem_id, const std::string& masked_sgf_str,
    const std::string& winning_color, const std::string& black_search_goal,
    const std::string& white_search_goal,
    const std::string& black_crucial_stone,
    const std::string& white_crucial_stone, const std::string& turn_color,
    TurnConflictPolicy conflict_policy, const std::string& region_str,
    bool attacker_allow_ko, bool defender_allow_ko) const {
  ParsedProblem<N> out;
  out.problem_id = problem_id;

  const std::string win_col = UpperAscii(TrimAscii(winning_color));
  if (TrimAscii(masked_sgf_str).empty() || win_col.empty()) {
    out.valid = false;
    out.error_code = "FR1-MISSING-REQUIRED";
    out.error_message =
        "Required fields masked_sgf_str or winning_color missing.";
    return out;
  }

  if (!ValidateSgfStructureAndSize(masked_sgf_str, N, &out.error_code,
                                   &out.error_message)) {
    out.valid = false;
    return out;
  }

  if (win_col != "B" && win_col != "W") {
    out.valid = false;
    out.error_code = "FR1-INVALID-WINNING-COLOR";
    out.error_message = "winning_color must be 'B' or 'W' (FR-1.1).";
    return out;
  }

  // FR-1.3: Reject mixed '&' and '|' / ',' in crucial_stone expressions.
  if (HasMixedLogicalOps(black_crucial_stone) ||
      HasMixedLogicalOps(white_crucial_stone)) {
    out.valid = false;
    out.error_code = "FR1-MIXED-LOGICAL-OP";
    out.error_message =
        "Mixed '&' and '|'/, operators inside crucial_stone are forbidden "
        "(FR-1.3).";
    return out;
  }

  // Determine SGF PL property (FR-1.2: never insert pass to fix turn conflict).
  bool has_sgf_pl = false;
  Color sgf_pl = Color::kBlack;
  if (masked_sgf_str.find("PL[W]") != std::string::npos ||
      masked_sgf_str.find("PL[w]") != std::string::npos) {
    has_sgf_pl = true;
    sgf_pl = Color::kWhite;
  } else if (masked_sgf_str.find("PL[B]") != std::string::npos ||
             masked_sgf_str.find("PL[b]") != std::string::npos) {
    has_sgf_pl = true;
    sgf_pl = Color::kBlack;
  }

  const std::string meta_turn_str = UpperAscii(TrimAscii(turn_color));
  Color final_turn = sgf_pl;
  if (!meta_turn_str.empty()) {
    if (meta_turn_str != "B" && meta_turn_str != "W") {
      out.valid = false;
      out.error_code = "FR1-INVALID-TURN-COLOR";
      out.error_message = "turn_color must be 'B' or 'W' (FR-1.2).";
      return out;
    }
    const Color meta_turn =
        (meta_turn_str == "W") ? Color::kWhite : Color::kBlack;
    if (has_sgf_pl && meta_turn != sgf_pl) {
      if (conflict_policy == TurnConflictPolicy::kRejectStrict) {
        out.valid = false;
        out.error_code = "FR1-TURN-CONFLICT";
        out.error_message =
            "turn_color conflicts with SGF PL; rejected under strict policy "
            "(FR-1.2).";
        return out;
      }
      out.warning_message =
          "turn_color conflicts with SGF PL; using SGF PL under warn_ignore.";
      final_turn = sgf_pl;
    } else {
      final_turn = meta_turn;
    }
  }

  const std::string active_goal_str = UpperAscii(
      TrimAscii((win_col == "W") ? white_search_goal : black_search_goal));
  if (active_goal_str != "TOLIVE" && active_goal_str != "TOKILL") {
    out.valid = false;
    out.error_code = "FR1-INVALID-GOAL";
    out.error_message =
        "Active search_goal must be 'TOLIVE' or 'TOKILL' (FR-1.1).";
    return out;
  }

  out.proof_context.root_attacker =
      (win_col == "W") ? Color::kWhite : Color::kBlack;
  out.proof_context.attacker_goal =
      (active_goal_str == "TOKILL") ? SearchGoal::kToKill : SearchGoal::kToLive;
  out.proof_context.ko_rule = KoRule::kSituationalSuperko;
  out.proof_context.attacker_allow_ko = attacker_allow_ko;
  out.proof_context.defender_allow_ko = defender_allow_ko;

  const std::string target_expr = TrimAscii(
      (win_col == "W") ? white_crucial_stone : black_crucial_stone);
  if (target_expr.find('&') != std::string::npos) {
    out.proof_context.crucial_stone_op = LogicalOp::kConjunction;
  } else if (target_expr.find('|') != std::string::npos ||
             target_expr.find(',') != std::string::npos) {
    out.proof_context.crucial_stone_op = LogicalOp::kDisjunction;
  } else {
    out.proof_context.crucial_stone_op = LogicalOp::kSingle;
  }

  // Extract initial stones from masked_sgf_str (AB[...] and AW[...]).
  std::vector<int> black_coords;
  std::vector<int> white_coords;
  ExtractSgfPropertyCoords(masked_sgf_str, "AB", N, &black_coords);
  ExtractSgfPropertyCoords(masked_sgf_str, "AW", N, &white_coords);

  BitBoard<N> black_bits;
  BitBoard<N> white_bits;
  for (int c : black_coords) {
    black_bits.Set(c, true);
    white_bits.Reset(c);
  }
  for (int c : white_coords) {
    white_bits.Set(c, true);
    black_bits.Reset(c);
  }

  // Parse optional full search region (comma-separated SGF coords or MA[..]).
  BitBoard<N> region_bits;
  if (!TrimAscii(region_str).empty()) {
    for (const std::string& tok : SplitCrucialTokens(region_str)) {
      const int rc = ParseSgfCoord(tok, N);
      if (rc < 0) {
        out.valid = false;
        out.error_code = "FR1-INVALID-REGION-COORD";
        out.error_message = "Invalid coordinate in region mask: " + tok;
        return out;
      }
      region_bits.Set(rc, true);
    }
  } else {
    std::vector<int> ma_coords;
    ExtractSgfPropertyCoords(masked_sgf_str, "MA", N, &ma_coords);
    for (int rc : ma_coords) region_bits.Set(rc, true);
  }
  if (region_bits.Any()) {
    out.region_search_mask = region_bits;
  }

  // Parse and validate crucial_stone tokens on the actual initial board!
  const Color expected_token_color =
      (out.proof_context.attacker_goal == SearchGoal::kToLive)
          ? out.proof_context.root_attacker
          : OppositeColor(out.proof_context.root_attacker);

  if (target_expr.empty()) {
    if (out.warning_message.empty()) {
      out.warning_message =
          "FR1-EMPTY-CRUCIAL-WARN: empty crucial_stone evaluates to constant "
          "false.";
    }
  } else {
    const std::vector<std::string> raw_tokens = SplitCrucialTokens(target_expr);
    for (size_t i = 0; i < raw_tokens.size(); ++i) {
      const int tc = ParseSgfCoord(raw_tokens[i], N);
      if (tc < 0) {
        out.valid = false;
        out.error_code = "FR1-OUT-OF-RANGE-CRUCIAL";
        out.error_message =
            "Crucial stone coordinate invalid or out of range: " +
            raw_tokens[i];
        return out;
      }
      const bool present_on_board =
          (expected_token_color == Color::kBlack) ? black_bits.Get(tc)
                                                  : white_bits.Get(tc);
      if (!present_on_board) {
        out.valid = false;
        out.error_code = "FR1-MISSING-CRUCIAL-STONE";
        out.error_message =
            "Crucial stone absent or wrong color on initial board: " +
            raw_tokens[i];
        return out;
      }
      TargetToken tok;
      tok.token_id = static_cast<uint16_t>(i);
      tok.initial_coord = static_cast<int16_t>(tc);
      tok.group_index = static_cast<uint8_t>(i);
      tok.stone_color = expected_token_color;
      out.proof_context.initial_tokens.push_back(tok);
    }
  }

  const std::string ctx_sig =
      problem_id + "|" + win_col + "|" + active_goal_str + "|" + target_expr +
      "|" + (attacker_allow_ko ? "1" : "0") + "|" +
      (defender_allow_ko ? "1" : "0");
  out.proof_context.context_id = Fnv1a64String(ctx_sig);

  out.initial_position.Clear(out.proof_context);
  for (int c : black_bits.ToCoords()) {
    out.initial_position.SetupInitialStone(c, Color::kBlack);
  }
  for (int c : white_bits.ToCoords()) {
    out.initial_position.SetupInitialStone(c, Color::kWhite);
  }
  if (out.region_search_mask.has_value()) {
    const BitBoard<N> all_stones = black_bits | white_bits;
    out.initial_position.SetImmortalWall(all_stones &
                                         ~(*out.region_search_mask));
  }
  out.initial_position.FinalizeInitialPosition(final_turn);
  out.valid = true;
  return out;
}

template <int N>
ParsedProblem<N> ProblemContractParser<N>::ParseTsumegoJsonObject(
    const std::string& problem_id, const std::string& raw_json_text,
    TurnConflictPolicy conflict_policy) const {
  std::map<std::string, std::string> fields;
  StrictProblemJsonParser parser(raw_json_text);
  if (!parser.ParseTopLevelObject(&fields)) {
    ParsedProblem<N> err;
    err.problem_id = problem_id;
    err.valid = false;
    err.error_code = "FR1-INVALID-JSON";
    err.error_message =
        "Malformed or truncated JSON document (strict RFC 8259 check failed).";
    return err;
  }

  auto get_field = [&](const std::string& key) -> std::string {
    const auto it = fields.find(key);
    return (it == fields.end()) ? std::string{} : it->second;
  };

  const std::string masked_sgf_str = get_field("masked_sgf_str");
  const std::string winning_color = get_field("winning_color");
  if (masked_sgf_str.empty() || winning_color.empty()) {
    ParsedProblem<N> err;
    err.problem_id = problem_id;
    err.valid = false;
    err.error_code = "FR1-MISSING-REQUIRED";
    err.error_message =
        "Missing required string fields masked_sgf_str / winning_color.";
    return err;
  }

  const std::string black_search_goal = get_field("black_search_goal");
  const std::string white_search_goal = get_field("white_search_goal");
  const std::string black_crucial_stone = get_field("black_crucial_stone");
  const std::string white_crucial_stone = get_field("white_crucial_stone");
  const std::string turn_color = get_field("turn_color");
  const std::string region_str = get_field("region");
  const std::string black_ko_rule = get_field("black_ko_rule");
  const std::string white_ko_rule = get_field("white_ko_rule");

  const bool win_is_white = (UpperAscii(TrimAscii(winning_color)) == "W");
  const bool black_allow_ko = (TrimAscii(black_ko_rule) == "allow_ko");
  const bool white_allow_ko =
      white_ko_rule.empty() ? true : (TrimAscii(white_ko_rule) == "allow_ko");
  const bool attacker_allow_ko = win_is_white ? white_allow_ko : black_allow_ko;
  const bool defender_allow_ko = win_is_white ? black_allow_ko : white_allow_ko;

  return ParseTsumegoJson(problem_id, masked_sgf_str, winning_color,
                          black_search_goal, white_search_goal,
                          black_crucial_stone, white_crucial_stone, turn_color,
                          conflict_policy, region_str, attacker_allow_ko,
                          defender_allow_ko);
}

template class ProblemContractParser<5>;
template class ProblemContractParser<7>;
template class ProblemContractParser<19>;

}  // namespace ldprover
