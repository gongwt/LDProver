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

bool ExtractJsonStringField(const std::string& json, const std::string& key,
                            std::string* out_val) {
  const std::string needle = "\"" + key + "\"";
  size_t pos = 0;
  while ((pos = json.find(needle, pos)) != std::string::npos) {
    size_t cur = pos + needle.size();
    while (cur < json.size() &&
           std::isspace(static_cast<unsigned char>(json[cur]))) {
      ++cur;
    }
    if (cur >= json.size() || json[cur] != ':') {
      pos = cur;
      continue;
    }
    ++cur;
    while (cur < json.size() &&
           std::isspace(static_cast<unsigned char>(json[cur]))) {
      ++cur;
    }
    if (cur >= json.size() || json[cur] != '"') return false;
    ++cur;
    std::string val;
    while (cur < json.size()) {
      const char ch = json[cur++];
      if (ch == '\\' && cur < json.size()) {
        const char esc = json[cur++];
        if (esc == 'n') {
          val.push_back('\n');
        } else if (esc == 'r') {
          val.push_back('\r');
        } else if (esc == 't') {
          val.push_back('\t');
        } else {
          val.push_back(esc);
        }
      } else if (ch == '"') {
        *out_val = val;
        return true;
      } else {
        val.push_back(ch);
      }
    }
    return false;
  }
  return false;
}

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
  std::string masked_sgf_str;
  std::string winning_color;
  std::string black_search_goal;
  std::string white_search_goal;
  std::string black_crucial_stone;
  std::string white_crucial_stone;
  std::string turn_color;
  std::string region_str;
  std::string black_ko_rule;
  std::string white_ko_rule;

  const bool has_sgf =
      ExtractJsonStringField(raw_json_text, "masked_sgf_str", &masked_sgf_str);
  const bool has_win =
      ExtractJsonStringField(raw_json_text, "winning_color", &winning_color);
  if (!has_sgf || !has_win) {
    ParsedProblem<N> err;
    err.problem_id = problem_id;
    err.valid = false;
    err.error_code = "FR1-INVALID-JSON";
    err.error_message =
        "Malformed JSON or missing required string fields masked_sgf_str / "
        "winning_color.";
    return err;
  }

  ExtractJsonStringField(raw_json_text, "black_search_goal",
                         &black_search_goal);
  ExtractJsonStringField(raw_json_text, "white_search_goal",
                         &white_search_goal);
  ExtractJsonStringField(raw_json_text, "black_crucial_stone",
                         &black_crucial_stone);
  ExtractJsonStringField(raw_json_text, "white_crucial_stone",
                         &white_crucial_stone);
  ExtractJsonStringField(raw_json_text, "turn_color", &turn_color);
  ExtractJsonStringField(raw_json_text, "region", &region_str);
  ExtractJsonStringField(raw_json_text, "black_ko_rule", &black_ko_rule);
  ExtractJsonStringField(raw_json_text, "white_ko_rule", &white_ko_rule);

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
