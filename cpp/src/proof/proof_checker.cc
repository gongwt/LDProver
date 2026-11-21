// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/proof/proof_checker.cc
// Description: Implementation of self-contained lproof/1 Proof DAG serializer
// (RFC 8785 JCS + FIPS 180-4 SHA-256), SGF variation tree writer, standalone
// JSON verifier, and zero-trust full-DAG ProofChecker (FR-8.1..8.4, FR-9.1..9.3).

#include "ldprover/proof/proof_checker.h"

#include <algorithm>
#include <array>
#include <cctype>
#include <cstdint>
#include <iomanip>
#include <map>
#include <sstream>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include "ldprover/terminal/benson_uca.h"

namespace ldprover {

namespace {

constexpr std::array<uint32_t, 64> kSha256K = {
    0x428a2f98U, 0x71374491U, 0xb5c0fbcfU, 0xe9b5dba5U, 0x3956c25bU,
    0x59f111f1U, 0x923f82a4U, 0xab1c5ed5U, 0xd807aa98U, 0x12835b01U,
    0x243185beU, 0x550c7dc3U, 0x72be5d74U, 0x80deb1feU, 0x9bdc06a7U,
    0xc19bf174U, 0xe49b69c1U, 0xefbe4786U, 0x0fc19dc6U, 0x240ca1ccU,
    0x2de92c6fU, 0x4a7484aaU, 0x5cb0a9dcU, 0x76f988daU, 0x983e5152U,
    0xa831c66dU, 0xb00327c8U, 0xbf597fc7U, 0xc6e00bf3U, 0xd5a79147U,
    0x06ca6351U, 0x14292967U, 0x27b70a85U, 0x2e1b2138U, 0x4d2c6dfcU,
    0x53380d13U, 0x650a7354U, 0x766a0abbU, 0x81c2c92eU, 0x92722c85U,
    0xa2bfe8a1U, 0xa81a664bU, 0xc24b8b70U, 0xc76c51a3U, 0xd192e819U,
    0xd6990624U, 0xf40e3585U, 0x106aa070U, 0x19a4c116U, 0x1e376c08U,
    0x2748774cU, 0x34b0bcb5U, 0x391c0cb3U, 0x4ed8aa4aU, 0x5b9cca4fU,
    0x682e6ff3U, 0x748f82eeU, 0x78a5636fU, 0x84c87814U, 0x8cc70208U,
    0x90befffaU, 0xa4506cebU, 0xbef9a3f7U, 0xc67178f2U};

constexpr uint32_t Rotr32(uint32_t x, uint32_t n) noexcept {
  return (x >> n) | (x << (32U - n));
}

// Pure C++20 FIPS 180-4 SHA-256 digest (lowercase 64-char hex).
std::string Sha256Hex(const std::string& input) {
  const uint64_t bit_len = static_cast<uint64_t>(input.size()) * 8ULL;
  const size_t total_bytes = ((input.size() + 9U + 63U) / 64U) * 64U;
  std::vector<uint8_t> padded(total_bytes, 0U);
  for (size_t i = 0; i < input.size(); ++i) {
    padded[i] = static_cast<uint8_t>(input[i]);
  }
  padded[input.size()] = 0x80U;
  for (int b = 0; b < 8; ++b) {
    padded[total_bytes - 1U - static_cast<size_t>(b)] =
        static_cast<uint8_t>((bit_len >> (b * 8)) & 0xffULL);
  }

  uint32_t h0 = 0x6a09e667U;
  uint32_t h1 = 0xbb67ae85U;
  uint32_t h2 = 0x3c6ef372U;
  uint32_t h3 = 0xa54ff53aU;
  uint32_t h4 = 0x510e527fU;
  uint32_t h5 = 0x9b05688cU;
  uint32_t h6 = 0x1f83d9abU;
  uint32_t h7 = 0x5be0cd19U;

  std::array<uint32_t, 64> w{};
  for (size_t offset = 0; offset < total_bytes; offset += 64U) {
    for (size_t i = 0; i < 16U; ++i) {
      const size_t idx = offset + i * 4U;
      w[i] = (static_cast<uint32_t>(padded[idx]) << 24U) |
             (static_cast<uint32_t>(padded[idx + 1U]) << 16U) |
             (static_cast<uint32_t>(padded[idx + 2U]) << 8U) |
             static_cast<uint32_t>(padded[idx + 3U]);
    }
    for (size_t i = 16U; i < 64U; ++i) {
      const uint32_t s0 =
          Rotr32(w[i - 15U], 7U) ^ Rotr32(w[i - 15U], 18U) ^ (w[i - 15U] >> 3U);
      const uint32_t s1 =
          Rotr32(w[i - 2U], 17U) ^ Rotr32(w[i - 2U], 19U) ^ (w[i - 2U] >> 10U);
      w[i] = w[i - 16U] + s0 + w[i - 7U] + s1;
    }

    uint32_t a = h0;
    uint32_t b = h1;
    uint32_t c = h2;
    uint32_t d = h3;
    uint32_t e = h4;
    uint32_t f = h5;
    uint32_t g = h6;
    uint32_t h = h7;

    for (size_t i = 0; i < 64U; ++i) {
      const uint32_t big_s1 =
          Rotr32(e, 6U) ^ Rotr32(e, 11U) ^ Rotr32(e, 25U);
      const uint32_t ch = (e & f) ^ ((~e) & g);
      const uint32_t temp1 = h + big_s1 + ch + kSha256K[i] + w[i];
      const uint32_t big_s0 =
          Rotr32(a, 2U) ^ Rotr32(a, 13U) ^ Rotr32(a, 22U);
      const uint32_t maj = (a & b) ^ (a & c) ^ (b & c);
      const uint32_t temp2 = big_s0 + maj;

      h = g;
      g = f;
      f = e;
      e = d + temp1;
      d = c;
      c = b;
      b = a;
      a = temp1 + temp2;
    }

    h0 += a;
    h1 += b;
    h2 += c;
    h3 += d;
    h4 += e;
    h5 += f;
    h6 += g;
    h7 += h;
  }

  std::ostringstream oss;
  oss << std::hex << std::setfill('0') << std::setw(8) << h0 << std::setw(8)
      << h1 << std::setw(8) << h2 << std::setw(8) << h3 << std::setw(8) << h4
      << std::setw(8) << h5 << std::setw(8) << h6 << std::setw(8) << h7;
  return oss.str();
}

std::string HexU64(uint64_t val) {
  std::ostringstream oss;
  oss << std::hex << std::setw(16) << std::setfill('0') << val;
  return oss.str();
}

bool ParseHexU64(const std::string& hex_str, uint64_t* out_val) {
  if (hex_str.empty() || hex_str.size() > 16U) return false;
  uint64_t acc = 0;
  for (char c : hex_str) {
    acc <<= 4U;
    if (c >= '0' && c <= '9') {
      acc |= static_cast<uint64_t>(c - '0');
    } else if (c >= 'a' && c <= 'f') {
      acc |= static_cast<uint64_t>(c - 'a' + 10);
    } else if (c >= 'A' && c <= 'F') {
      acc |= static_cast<uint64_t>(c - 'A' + 10);
    } else {
      return false;
    }
  }
  *out_val = acc;
  return true;
}

std::string EscapeJsonString(const std::string& s) {
  std::ostringstream oss;
  oss << '"';
  for (unsigned char c : s) {
    switch (c) {
      case '"':
        oss << "\\\"";
        break;
      case '\\':
        oss << "\\\\";
        break;
      case '\b':
        oss << "\\b";
        break;
      case '\f':
        oss << "\\f";
        break;
      case '\n':
        oss << "\\n";
        break;
      case '\r':
        oss << "\\r";
        break;
      case '\t':
        oss << "\\t";
        break;
      default:
        if (c < 0x20U) {
          oss << "\\u00" << std::hex << std::setw(2) << std::setfill('0')
              << static_cast<int>(c) << std::dec;
        } else {
          oss << static_cast<char>(c);
        }
        break;
    }
  }
  oss << '"';
  return oss.str();
}

struct JsonValue {
  enum class Kind { kNull, kBool, kInt, kString, kArray, kObject };
  Kind kind = Kind::kNull;
  bool bool_val = false;
  int64_t int_val = 0;
  std::string str_val;
  std::vector<JsonValue> arr_val;
  std::map<std::string, JsonValue> obj_val;

  static JsonValue MakeNull() { return JsonValue{}; }
  static JsonValue MakeBool(bool b) {
    JsonValue v;
    v.kind = Kind::kBool;
    v.bool_val = b;
    return v;
  }
  static JsonValue MakeInt(int64_t n) {
    JsonValue v;
    v.kind = Kind::kInt;
    v.int_val = n;
    return v;
  }
  static JsonValue MakeStr(std::string s) {
    JsonValue v;
    v.kind = Kind::kString;
    v.str_val = std::move(s);
    return v;
  }
  static JsonValue MakeArr(std::vector<JsonValue> a = {}) {
    JsonValue v;
    v.kind = Kind::kArray;
    v.arr_val = std::move(a);
    return v;
  }
  static JsonValue MakeObj() {
    JsonValue v;
    v.kind = Kind::kObject;
    return v;
  }
};

// RFC 8785 JSON Canonicalization Scheme (JCS): sorted object keys, compact UTF-8.
std::string CanonicalizeJcs(const JsonValue& v) {
  switch (v.kind) {
    case JsonValue::Kind::kNull:
      return "null";
    case JsonValue::Kind::kBool:
      return v.bool_val ? "true" : "false";
    case JsonValue::Kind::kInt:
      return std::to_string(v.int_val);
    case JsonValue::Kind::kString:
      return EscapeJsonString(v.str_val);
    case JsonValue::Kind::kArray: {
      std::string out = "[";
      for (size_t i = 0; i < v.arr_val.size(); ++i) {
        if (i > 0) out.push_back(',');
        out += CanonicalizeJcs(v.arr_val[i]);
      }
      out.push_back(']');
      return out;
    }
    case JsonValue::Kind::kObject: {
      std::string out = "{";
      bool first = true;
      for (const auto& [k, val] : v.obj_val) {
        if (!first) out.push_back(',');
        first = false;
        out += EscapeJsonString(k);
        out.push_back(':');
        out += CanonicalizeJcs(val);
      }
      out.push_back('}');
      return out;
    }
  }
  return "null";
}

std::string PrettyPrintJson(const JsonValue& v, int indent = 0) {
  const std::string pad(static_cast<size_t>(indent), ' ');
  const std::string inner_pad(static_cast<size_t>(indent + 2), ' ');
  switch (v.kind) {
    case JsonValue::Kind::kNull:
      return "null";
    case JsonValue::Kind::kBool:
      return v.bool_val ? "true" : "false";
    case JsonValue::Kind::kInt:
      return std::to_string(v.int_val);
    case JsonValue::Kind::kString:
      return EscapeJsonString(v.str_val);
    case JsonValue::Kind::kArray: {
      if (v.arr_val.empty()) return "[]";
      bool all_scalar = true;
      for (const auto& item : v.arr_val) {
        if (item.kind == JsonValue::Kind::kArray ||
            item.kind == JsonValue::Kind::kObject) {
          all_scalar = false;
          break;
        }
      }
      if (all_scalar) {
        std::string out = "[";
        for (size_t i = 0; i < v.arr_val.size(); ++i) {
          if (i > 0) out += ", ";
          out += PrettyPrintJson(v.arr_val[i], 0);
        }
        out.push_back(']');
        return out;
      }
      std::string out = "[\n";
      for (size_t i = 0; i < v.arr_val.size(); ++i) {
        out += inner_pad + PrettyPrintJson(v.arr_val[i], indent + 2);
        if (i + 1U < v.arr_val.size()) out.push_back(',');
        out.push_back('\n');
      }
      out += pad + "]";
      return out;
    }
    case JsonValue::Kind::kObject: {
      if (v.obj_val.empty()) return "{}";
      std::string out = "{\n";
      size_t idx = 0;
      for (const auto& [k, val] : v.obj_val) {
        out += inner_pad + EscapeJsonString(k) + ": " +
               PrettyPrintJson(val, indent + 2);
        if (++idx < v.obj_val.size()) out.push_back(',');
        out.push_back('\n');
      }
      out += pad + "}";
      return out;
    }
  }
  return "null";
}

class JsonParser {
 public:
  explicit JsonParser(const std::string& src) : src_(src) {}

  bool ParseDocument(JsonValue* out) {
    SkipWs();
    if (!ParseValue(out)) return false;
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

  bool ParseValue(JsonValue* out) {
    SkipWs();
    if (pos_ >= src_.size()) return false;
    const char c = src_[pos_];
    if (c == '{') return ParseObject(out);
    if (c == '[') return ParseArray(out);
    if (c == '"') {
      std::string s;
      if (!ParseString(&s)) return false;
      *out = JsonValue::MakeStr(std::move(s));
      return true;
    }
    if (c == 't') {
      if (src_.compare(pos_, 4U, "true") != 0) return false;
      pos_ += 4U;
      *out = JsonValue::MakeBool(true);
      return true;
    }
    if (c == 'f') {
      if (src_.compare(pos_, 5U, "false") != 0) return false;
      pos_ += 5U;
      *out = JsonValue::MakeBool(false);
      return true;
    }
    if (c == 'n') {
      if (src_.compare(pos_, 4U, "null") != 0) return false;
      pos_ += 4U;
      *out = JsonValue::MakeNull();
      return true;
    }
    if (c == '-' || std::isdigit(static_cast<unsigned char>(c))) {
      return ParseInt(out);
    }
    return false;
  }

  bool ParseString(std::string* out) {
    if (pos_ >= src_.size() || src_[pos_] != '"') return false;
    ++pos_;
    std::string res;
    while (pos_ < src_.size()) {
      const char ch = src_[pos_++];
      if (ch == '"') {
        *out = std::move(res);
        return true;
      }
      if (ch == '\\') {
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
            uint32_t code = 0;
            for (int k = 0; k < 4; ++k) {
              const char hc = src_[pos_++];
              code <<= 4U;
              if (hc >= '0' && hc <= '9') {
                code |= static_cast<uint32_t>(hc - '0');
              } else if (hc >= 'a' && hc <= 'f') {
                code |= static_cast<uint32_t>(hc - 'a' + 10);
              } else if (hc >= 'A' && hc <= 'F') {
                code |= static_cast<uint32_t>(hc - 'A' + 10);
              } else {
                return false;
              }
            }
            if (code < 0x80U) {
              res.push_back(static_cast<char>(code));
            } else if (code < 0x800U) {
              res.push_back(static_cast<char>(0xC0U | (code >> 6U)));
              res.push_back(static_cast<char>(0x80U | (code & 0x3FU)));
            } else {
              res.push_back(static_cast<char>(0xE0U | (code >> 12U)));
              res.push_back(static_cast<char>(0x80U | ((code >> 6U) & 0x3FU)));
              res.push_back(static_cast<char>(0x80U | (code & 0x3FU)));
            }
            break;
          }
          default:
            return false;
        }
      } else if (static_cast<unsigned char>(ch) < 0x20U) {
        return false;
      } else {
        res.push_back(ch);
      }
    }
    return false;
  }

  bool ParseInt(JsonValue* out) {
    bool neg = false;
    if (src_[pos_] == '-') {
      neg = true;
      ++pos_;
    }
    if (pos_ >= src_.size() ||
        !std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
      return false;
    }
    if (src_[pos_] == '0' && pos_ + 1U < src_.size() &&
        std::isdigit(static_cast<unsigned char>(src_[pos_ + 1U]))) {
      return false;
    }
    int64_t val = 0;
    while (pos_ < src_.size() &&
           std::isdigit(static_cast<unsigned char>(src_[pos_]))) {
      val = val * 10 + static_cast<int64_t>(src_[pos_] - '0');
      ++pos_;
    }
    *out = JsonValue::MakeInt(neg ? -val : val);
    return true;
  }

  bool ParseArray(JsonValue* out) {
    ++pos_;  // '['
    SkipWs();
    JsonValue arr = JsonValue::MakeArr();
    if (pos_ < src_.size() && src_[pos_] == ']') {
      ++pos_;
      *out = std::move(arr);
      return true;
    }
    while (pos_ < src_.size()) {
      JsonValue elem;
      if (!ParseValue(&elem)) return false;
      arr.arr_val.push_back(std::move(elem));
      SkipWs();
      if (pos_ < src_.size() && src_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < src_.size() && src_[pos_] == ']') {
        ++pos_;
        *out = std::move(arr);
        return true;
      }
      return false;
    }
    return false;
  }

  bool ParseObject(JsonValue* out) {
    ++pos_;  // '{'
    SkipWs();
    JsonValue obj = JsonValue::MakeObj();
    if (pos_ < src_.size() && src_[pos_] == '}') {
      ++pos_;
      *out = std::move(obj);
      return true;
    }
    while (pos_ < src_.size()) {
      SkipWs();
      std::string key;
      if (!ParseString(&key)) return false;
      SkipWs();
      if (pos_ >= src_.size() || src_[pos_] != ':') return false;
      ++pos_;
      JsonValue val;
      if (!ParseValue(&val)) return false;
      obj.obj_val[key] = std::move(val);
      SkipWs();
      if (pos_ < src_.size() && src_[pos_] == ',') {
        ++pos_;
        continue;
      }
      if (pos_ < src_.size() && src_[pos_] == '}') {
        ++pos_;
        *out = std::move(obj);
        return true;
      }
      return false;
    }
    return false;
  }

  const std::string& src_;
  size_t pos_ = 0;
};

JsonValue MakeIntArray(const std::vector<int>& vals) {
  JsonValue arr = JsonValue::MakeArr();
  arr.arr_val.reserve(vals.size());
  for (int v : vals) arr.arr_val.push_back(JsonValue::MakeInt(v));
  return arr;
}

std::string OutcomeToStr(ProofOutcome outcome) {
  if (outcome == ProofOutcome::kProvenWin) return "PROVEN_WIN";
  if (outcome == ProofOutcome::kProvenLoss) return "PROVEN_LOSS";
  return "UNKNOWN";
}

bool StrToOutcome(const std::string& s, ProofOutcome* out) {
  if (s == "PROVEN_WIN") {
    *out = ProofOutcome::kProvenWin;
    return true;
  }
  if (s == "PROVEN_LOSS") {
    *out = ProofOutcome::kProvenLoss;
    return true;
  }
  if (s == "UNKNOWN") {
    *out = ProofOutcome::kUnknown;
    return true;
  }
  return false;
}

std::string CoordToSgf(int16_t move, int board_size) {
  if (move == kPassMove || move < 0 || move >= board_size * board_size) {
    return "";
  }
  const int r = move / board_size;
  const int c = move % board_size;
  std::string s;
  s.push_back(static_cast<char>('a' + c));
  s.push_back(static_cast<char>('a' + r));
  return s;
}

std::string MoveToSgfLabel(int16_t move, int board_size) {
  if (move == kPassMove) return "pass";
  return CoordToSgf(move, board_size);
}

std::string LogicalOpToStr(LogicalOp op) {
  switch (op) {
    case LogicalOp::kSingle:
      return "SINGLE";
    case LogicalOp::kConjunction:
      return "AND";
    case LogicalOp::kDisjunction:
      return "OR";
  }
  return "SINGLE";
}

bool ParseLogicalOp(const JsonValue& v, LogicalOp* out) {
  if (v.kind == JsonValue::Kind::kString) {
    if (v.str_val == "SINGLE") {
      *out = LogicalOp::kSingle;
      return true;
    }
    if (v.str_val == "AND") {
      *out = LogicalOp::kConjunction;
      return true;
    }
    if (v.str_val == "OR") {
      *out = LogicalOp::kDisjunction;
      return true;
    }
    return false;
  }
  if (v.kind == JsonValue::Kind::kInt && v.int_val >= 0 && v.int_val <= 2) {
    *out = static_cast<LogicalOp>(static_cast<uint8_t>(v.int_val));
    return true;
  }
  return false;
}

std::string KoRuleToStr(KoRule rule) {
  switch (rule) {
    case KoRule::kSituationalSuperko:
      return "SSK";
    case KoRule::kPositionalSuperko:
      return "PSK";
    case KoRule::kSimpleKoOnly:
      return "SIMPLE";
  }
  return "SSK";
}

bool ParseKoRule(const JsonValue& v, KoRule* out) {
  if (v.kind == JsonValue::Kind::kString) {
    if (v.str_val == "SSK") {
      *out = KoRule::kSituationalSuperko;
      return true;
    }
    if (v.str_val == "PSK") {
      *out = KoRule::kPositionalSuperko;
      return true;
    }
    if (v.str_val == "SIMPLE") {
      *out = KoRule::kSimpleKoOnly;
      return true;
    }
    return false;
  }
  if (v.kind == JsonValue::Kind::kInt && v.int_val >= 0 && v.int_val <= 2) {
    *out = static_cast<KoRule>(static_cast<uint8_t>(v.int_val));
    return true;
  }
  return false;
}

template <int N>
std::string EvidenceKindToStr(const ProofDagNode<N>& n) {
  switch (n.terminal_evidence) {
    case EvidenceKind::kBensonUca:
      return "BENSON_UCA";
    case EvidenceKind::kTokensCaptured:
      return "TOKENS_CAPTURED";
    case EvidenceKind::kDoublePassResolution:
      return "DOUBLE_PASS_RESOLUTION";
    case EvidenceKind::kEmptyTargetConstantFalse:
      return "EMPTY_TARGET_CONSTANT_FALSE";
    case EvidenceKind::kNone:
      if (n.is_pruned_outside_rz) return "OUTSIDE_RZ_REVALIDATED";
      if (n.is_tt_hit) return "TT_REVALIDATED_REUSE";
      if (!n.child_node_ids.empty()) return "INTERNAL_AGGREGATION";
      return "NONE";
  }
  return "NONE";
}

bool ParseEvidenceKind(const JsonValue& v, EvidenceKind* out) {
  if (v.kind == JsonValue::Kind::kString) {
    if (v.str_val == "BENSON_UCA") {
      *out = EvidenceKind::kBensonUca;
      return true;
    }
    if (v.str_val == "TOKENS_CAPTURED") {
      *out = EvidenceKind::kTokensCaptured;
      return true;
    }
    if (v.str_val == "DOUBLE_PASS_RESOLUTION") {
      *out = EvidenceKind::kDoublePassResolution;
      return true;
    }
    if (v.str_val == "EMPTY_TARGET_CONSTANT_FALSE") {
      *out = EvidenceKind::kEmptyTargetConstantFalse;
      return true;
    }
    if (v.str_val == "NONE" || v.str_val == "OUTSIDE_RZ_REVALIDATED" ||
        v.str_val == "TT_REVALIDATED_REUSE" ||
        v.str_val == "INTERNAL_AGGREGATION") {
      *out = EvidenceKind::kNone;
      return true;
    }
    return false;
  }
  if (v.kind == JsonValue::Kind::kInt && v.int_val >= 0 && v.int_val <= 4) {
    *out = static_cast<EvidenceKind>(static_cast<uint8_t>(v.int_val));
    return true;
  }
  return false;
}

bool ParseColorValue(const JsonValue& v, Color* out) {
  if (v.kind == JsonValue::Kind::kString) {
    if (v.str_val == "B" || v.str_val == "b") {
      *out = Color::kBlack;
      return true;
    }
    if (v.str_val == "W" || v.str_val == "w") {
      *out = Color::kWhite;
      return true;
    }
    return false;
  }
  if (v.kind == JsonValue::Kind::kInt) {
    if (v.int_val == 1) {
      *out = Color::kBlack;
      return true;
    }
    if (v.int_val == 2) {
      *out = Color::kWhite;
      return true;
    }
  }
  return false;
}

JsonValue EncodeSatJson(uint32_t val) {
  if (val >= kPnDnSaturation) return JsonValue::MakeStr("SAT");
  return JsonValue::MakeInt(static_cast<int64_t>(val));
}

bool ParseSatU32(const JsonValue& v, uint32_t* out) {
  if (v.kind == JsonValue::Kind::kString && v.str_val == "SAT") {
    *out = kPnDnSaturation;
    return true;
  }
  if (v.kind == JsonValue::Kind::kInt && v.int_val >= 0 &&
      v.int_val <= static_cast<int64_t>(kPnDnSaturation)) {
    *out = static_cast<uint32_t>(v.int_val);
    return true;
  }
  return false;
}

template <int N>
bool IsMoveInAllowedRegion(int16_t mv,
                           const std::optional<BitBoard<N>>& region_hint) {
  if (mv == kPassMove) return true;
  if (!region_hint.has_value()) return true;
  return mv >= 0 && mv < N * N && region_hint->Get(mv);
}

bool TargetTokensEqual(const std::vector<TargetToken>& a,
                       const std::vector<TargetToken>& b) {
  if (a.size() != b.size()) return false;
  auto sa = a;
  auto sb = b;
  auto cmp = [](const TargetToken& x, const TargetToken& y) {
    if (x.initial_coord != y.initial_coord) {
      return x.initial_coord < y.initial_coord;
    }
    if (x.group_index != y.group_index) return x.group_index < y.group_index;
    return static_cast<uint8_t>(x.stone_color) <
           static_cast<uint8_t>(y.stone_color);
  };
  std::sort(sa.begin(), sa.end(), cmp);
  std::sort(sb.begin(), sb.end(), cmp);
  for (size_t i = 0; i < sa.size(); ++i) {
    if (sa[i].initial_coord != sb[i].initial_coord ||
        sa[i].group_index != sb[i].group_index ||
        sa[i].stone_color != sb[i].stone_color) {
      return false;
    }
  }
  return true;
}

template <int N>
bool ReplaySourceSubgraphOnQueryState(
    const Position<N>& query_pos, const ProofContext& context,
    const std::optional<BitBoard<N>>& region_hint,
    const std::vector<ProofDagNode<N>>& dag_nodes, uint32_t source_node_id,
    ProofOutcome expected_outcome,
    const BensonTerminalEvaluator<N>& terminal_eval, uint32_t guard_depth) {
  if (guard_depth > 64U || source_node_id >= dag_nodes.size()) {
    return false;
  }

  uint32_t resolved_id = source_node_id;
  std::unordered_set<uint32_t> seen_redirects;
  while (true) {
    if (resolved_id >= dag_nodes.size() ||
        seen_redirects.find(resolved_id) != seen_redirects.end()) {
      return false;
    }
    seen_redirects.insert(resolved_id);
    const auto& cur = dag_nodes[resolved_id];
    if (!cur.is_pruned_outside_rz && !cur.is_tt_hit) break;
    if (cur.source_proof_node_id >= cur.node_id) return false;
    resolved_id = cur.source_proof_node_id;
  }

  const auto& src = dag_nodes[resolved_id];
  if (src.outcome != expected_outcome) return false;

  auto check_early_terminal = [&]() -> bool {
    const auto term = terminal_eval.EvaluateTerminal(query_pos, context);
    if (term.status == TerminalStatus::kWin) {
      return expected_outcome == ProofOutcome::kProvenWin;
    }
    if (term.status == TerminalStatus::kLoss) {
      return expected_outcome == ProofOutcome::kProvenLoss;
    }
    return false;
  };

  if (src.child_node_ids.empty() || query_pos.IsAtDoublePass()) {
    return check_early_terminal();
  }
  if (src.child_moves.size() != src.child_node_ids.size()) {
    return false;
  }

  const bool is_or = (query_pos.ToPlay() == context.root_attacker);
  const bool restricted_side =
      (query_pos.ToPlay() == context.root_attacker &&
       !context.attacker_allow_ko) ||
      (query_pos.ToPlay() != context.root_attacker &&
       !context.defender_allow_ko);

  // Existential node: OR -> ProvenWin or AND -> ProvenLoss.
  if ((is_or && expected_outcome == ProofOutcome::kProvenWin) ||
      (!is_or && expected_outcome == ProofOutcome::kProvenLoss)) {
    for (size_t i = 0; i < src.child_node_ids.size(); ++i) {
      const uint32_t cid = src.child_node_ids[i];
      if (cid >= src.node_id || cid >= dag_nodes.size()) continue;
      if (dag_nodes[cid].outcome != expected_outcome) continue;
      const int16_t mv = src.child_moves[i];
      if (!IsMoveInAllowedRegion<N>(mv, region_hint)) continue;
      Position<N> next_pos = query_pos;
      bool is_ko_cap = false;
      if (!next_pos.PlayMove(mv, &is_ko_cap)) continue;
      if (is_ko_cap && restricted_side) continue;
      if (ReplaySourceSubgraphOnQueryState<N>(
              next_pos, context, region_hint, dag_nodes, cid, expected_outcome,
              terminal_eval, guard_depth + 1U)) {
        return true;
      }
    }
    return check_early_terminal();
  }

  // Universal node: AND -> ProvenWin or OR -> ProvenLoss.
  // Every legal move on `query_pos` inside `region_hint` must exist and hold.
  std::unordered_map<int16_t, uint32_t> move_map;
  move_map.reserve(src.child_moves.size());
  for (size_t i = 0; i < src.child_moves.size(); ++i) {
    const uint32_t cid = src.child_node_ids[i];
    if (cid >= src.node_id || cid >= dag_nodes.size()) return false;
    move_map[src.child_moves[i]] = cid;
  }

  const std::vector<int16_t> query_legal =
      query_pos.GenerateLegalMoves(region_hint);
  for (int16_t lmv : query_legal) {
    const auto it = move_map.find(lmv);
    if (it == move_map.end()) return check_early_terminal();
    const uint32_t cid = it->second;
    if (dag_nodes[cid].outcome != expected_outcome) {
      return check_early_terminal();
    }
    Position<N> next_pos = query_pos;
    if (!next_pos.PlayMove(lmv)) return check_early_terminal();
    if (!ReplaySourceSubgraphOnQueryState<N>(
            next_pos, context, region_hint, dag_nodes, cid, expected_outcome,
            terminal_eval, guard_depth + 1U)) {
      return check_early_terminal();
    }
  }

  return true;
}

template <int N>
bool VerifySubgraphRecursive(const Position<N>& pos,
                             const ProofContext& context,
                             const SolveReport<N>& report, uint32_t node_id,
                             const BensonTerminalEvaluator<N>& terminal_eval,
                             uint32_t depth, VerificationReport* ver) {
  if (depth > 256U || node_id >= report.proof_dag_nodes.size()) {
    ver->failed_node_id = static_cast<int32_t>(node_id);
    ver->error_code = "LP-S01";
    ver->message = "Proof DAG recursion exceeded bound or invalid node_id.";
    return false;
  }

  const auto& node = report.proof_dag_nodes[node_id];
  ++ver->verified_states;
  ++ver->verified_histories;

  const bool expected_is_or = (pos.ToPlay() == context.root_attacker);
  if (node.to_play != pos.ToPlay() || node.is_or_node != expected_is_or) {
    ver->failed_node_id = static_cast<int32_t>(node_id);
    ver->error_code = "LP-N10";
    ver->message =
        "Node to_play / is_or_node disagrees with reachable board turn.";
    return false;
  }

  if (node.is_pruned_outside_rz || node.is_tt_hit) {
    if (node.source_proof_node_id >= node.node_id ||
        !ReplaySourceSubgraphOnQueryState<N>(
            pos, context, report.region_hint, report.proof_dag_nodes,
            node.source_proof_node_id, node.outcome, terminal_eval, 0U)) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-R02";
      ver->message =
          "OutsideRZRevalidated / TT certificate failed semantic replay on "
          "reachable QueryState + HistorySet.";
      return false;
    }
    ++ver->replayed_pruned_certificates;
    return true;
  }

  if (node.child_node_ids.empty()) {
    const auto term = terminal_eval.EvaluateTerminal(pos, context);
    const bool matches =
        (node.outcome == ProofOutcome::kProvenWin &&
         term.status == TerminalStatus::kWin) ||
        (node.outcome == ProofOutcome::kProvenLoss &&
         term.status == TerminalStatus::kLoss);
    if (!matches) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-L04";
      ver->message =
          "Reachable leaf failed independent Classic Benson / token capture "
          "verification.";
      return false;
    }
    return true;
  }

  // Every recorded child edge must be legal AND inside declared `region_hint`.
  for (size_t i = 0; i < node.child_moves.size(); ++i) {
    const int16_t mv = node.child_moves[i];
    if (!IsMoveInAllowedRegion<N>(mv, report.region_hint)) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-S11";
      ver->message =
          "Proof edge plays outside the declared regionCoords search domain.";
      return false;
    }
    if (!pos.IsLegalMove(mv)) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-S09";
      ver->message = "Illegal child move recorded in reachable ProofDagNode.";
      return false;
    }
  }

  const bool restricted_side =
      (pos.ToPlay() == context.root_attacker && !context.attacker_allow_ko) ||
      (pos.ToPlay() != context.root_attacker && !context.defender_allow_ko);

  const bool requires_witness =
      (node.is_or_node && node.outcome == ProofOutcome::kProvenWin) ||
      (!node.is_or_node && node.outcome == ProofOutcome::kProvenLoss);

  if (requires_witness) {
    for (size_t i = 0; i < node.child_node_ids.size(); ++i) {
      const uint32_t cid = node.child_node_ids[i];
      if (report.proof_dag_nodes[cid].outcome != node.outcome) continue;
      const int16_t mv = node.child_moves[i];
      if (!IsMoveInAllowedRegion<N>(mv, report.region_hint)) {
        ver->failed_node_id = static_cast<int32_t>(node_id);
        ver->error_code = "LP-S11";
        ver->message =
            "Existential witness plays outside declared regionCoords.";
        return false;
      }
      Position<N> next_pos = pos;
      bool is_ko_cap = false;
      if (!next_pos.PlayMove(mv, &is_ko_cap)) {
        ver->failed_node_id = static_cast<int32_t>(node_id);
        ver->error_code = "LP-S09";
        ver->message = "Illegal witness move in ProofDagNode.";
        return false;
      }
      if (is_ko_cap && restricted_side) continue;
      if (VerifySubgraphRecursive<N>(next_pos, context, report, cid,
                                     terminal_eval, depth + 1U, ver)) {
        return true;
      }
      return false;
    }
    ver->failed_node_id = static_cast<int32_t>(node_id);
    ver->error_code = "LP-N21";
    ver->message =
        "Existential node lacks a legal, region-valid, ko-compliant verified "
        "witness child.";
    return false;
  }

  // Universal obligation: EVERY legal move on `pos` inside `report.region_hint`
  // must be present in `node.child_moves` and recursively verified!
  std::unordered_map<int16_t, uint32_t> move_to_child;
  move_to_child.reserve(node.child_moves.size());
  for (size_t i = 0; i < node.child_moves.size(); ++i) {
    move_to_child[node.child_moves[i]] = node.child_node_ids[i];
  }

  const std::vector<int16_t> legal_moves =
      pos.GenerateLegalMoves(report.region_hint);
  for (int16_t lmv : legal_moves) {
    const auto it = move_to_child.find(lmv);
    if (it == move_to_child.end()) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-N22";
      ver->message =
          "Universal node omits legal response move from ProofDagNode.";
      return false;
    }
    const uint32_t cid = it->second;
    if (report.proof_dag_nodes[cid].outcome != node.outcome) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-N22";
      ver->message = "Universal node child disagrees with parent outcome.";
      return false;
    }
    Position<N> next_pos = pos;
    if (!next_pos.PlayMove(lmv)) {
      ver->failed_node_id = static_cast<int32_t>(node_id);
      ver->error_code = "LP-S09";
      ver->message = "Failed to replay legal move at universal node.";
      return false;
    }
    if (!VerifySubgraphRecursive<N>(next_pos, context, report, cid,
                                    terminal_eval, depth + 1U, ver)) {
      return false;
    }
  }

  return true;
}

}  // namespace

template <int N>
std::string ProofArtifactManager<N>::SerializeLProofJson(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report, std::string* out_checksum) const {
  JsonValue root = JsonValue::MakeObj();
  root.obj_val["magic"] = JsonValue::MakeStr("lproof/1");
  root.obj_val["problemId"] = JsonValue::MakeStr(report.problem_id);

  JsonValue ctx_obj = JsonValue::MakeObj();
  ctx_obj.obj_val["attackerAllowKo"] =
      JsonValue::MakeBool(context.attacker_allow_ko);
  ctx_obj.obj_val["attackerGoal"] = JsonValue::MakeStr(
      context.attacker_goal == SearchGoal::kToKill ? "TOKILL" : "TOLIVE");
  ctx_obj.obj_val["contextId"] = JsonValue::MakeStr(HexU64(context.context_id));
  ctx_obj.obj_val["crucialStoneOp"] =
      JsonValue::MakeStr(LogicalOpToStr(context.crucial_stone_op));
  ctx_obj.obj_val["defenderAllowKo"] =
      JsonValue::MakeBool(context.defender_allow_ko);
  ctx_obj.obj_val["koRule"] = JsonValue::MakeStr(KoRuleToStr(context.ko_rule));
  ctx_obj.obj_val["rootAttacker"] = JsonValue::MakeStr(
      context.root_attacker == Color::kWhite ? "W" : "B");

  JsonValue tok_arr = JsonValue::MakeArr();
  for (const auto& tok : context.initial_tokens) {
    JsonValue t = JsonValue::MakeObj();
    t.obj_val["groupIndex"] = JsonValue::MakeInt(tok.group_index);
    t.obj_val["initialCoord"] = JsonValue::MakeInt(tok.initial_coord);
    t.obj_val["stoneColor"] =
        JsonValue::MakeStr(tok.stone_color == Color::kWhite ? "W" : "B");
    t.obj_val["tokenId"] = JsonValue::MakeInt(tok.token_id);
    tok_arr.arr_val.push_back(std::move(t));
  }
  ctx_obj.obj_val["initialTokens"] = std::move(tok_arr);
  root.obj_val["context"] = std::move(ctx_obj);

  const bool is_traced = !initial_pos.PlayedMoveTrace().empty();
  const std::vector<int> region_coords =
      report.region_hint.has_value() ? report.region_hint->ToCoords()
                                     : std::vector<int>{};

  JsonValue setup = JsonValue::MakeObj();
  setup.obj_val["boardSize"] = JsonValue::MakeInt(N);
  setup.obj_val["rootKind"] =
      JsonValue::MakeStr(is_traced ? "traced_subposition" : "initial");
  setup.obj_val["firstToPlay"] =
      JsonValue::MakeStr(initial_pos.ToPlay() == Color::kWhite ? "W" : "B");
  setup.obj_val["koPoint"] = JsonValue::MakeInt(initial_pos.KoPoint());
  setup.obj_val["consecutivePasses"] =
      JsonValue::MakeInt(initial_pos.ConsecutivePasses());
  setup.obj_val["survivingTokensMask"] = JsonValue::MakeInt(
      static_cast<int64_t>(initial_pos.SurvivingTargetTokensMask()));
  setup.obj_val["zobristHex"] =
      JsonValue::MakeStr(HexU64(initial_pos.ZobristHash()));
  setup.obj_val["inputHash"] = JsonValue::MakeStr(HexU64(report.input_hash));
  setup.obj_val["blackInitialCoords"] =
      MakeIntArray(initial_pos.Stones(Color::kBlack).ToCoords());
  setup.obj_val["whiteInitialCoords"] =
      MakeIntArray(initial_pos.Stones(Color::kWhite).ToCoords());
  setup.obj_val["immortalWallCoords"] =
      MakeIntArray(initial_pos.ImmortalWall().ToCoords());
  setup.obj_val["hasRegionHint"] =
      JsonValue::MakeBool(report.region_hint.has_value());
  setup.obj_val["regionCoords"] = MakeIntArray(region_coords);
  setup.obj_val["rawRegionPointCount"] =
      JsonValue::MakeInt(static_cast<int64_t>(region_coords.size()));
  setup.obj_val["isFullRegionSearch"] = JsonValue::MakeBool(true);
  if (is_traced) {
    setup.obj_val["originFirstToPlay"] = JsonValue::MakeStr(
        initial_pos.OriginToPlay() == Color::kWhite ? "W" : "B");
    setup.obj_val["originBlackCoords"] =
        MakeIntArray(initial_pos.OriginBlack().ToCoords());
    setup.obj_val["originWhiteCoords"] =
        MakeIntArray(initial_pos.OriginWhite().ToCoords());
    JsonValue trace_arr = JsonValue::MakeArr();
    for (int16_t mv : initial_pos.PlayedMoveTrace()) {
      trace_arr.arr_val.push_back(JsonValue::MakeInt(mv));
    }
    setup.obj_val["initialTraceMoves"] = std::move(trace_arr);
  }
  root.obj_val["problemSetup"] = std::move(setup);

  root.obj_val["rootNode"] =
      (report.root_dag_node_id == kInvalidDagNodeId)
          ? JsonValue::MakeInt(-1)
          : JsonValue::MakeInt(report.root_dag_node_id);
  root.obj_val["rootOutcome"] =
      JsonValue::MakeStr(OutcomeToStr(report.root_status));
  root.obj_val["rootPn"] = EncodeSatJson(report.root_pn);
  root.obj_val["rootDn"] = EncodeSatJson(report.root_dn);
  root.obj_val["bestMove"] = JsonValue::MakeInt(report.best_move);
  root.obj_val["bestMoveSgf"] =
      JsonValue::MakeStr(MoveToSgfLabel(report.best_move, N));

  JsonValue nodes_arr = JsonValue::MakeArr();
  nodes_arr.arr_val.reserve(report.proof_dag_nodes.size());
  for (const auto& n : report.proof_dag_nodes) {
    JsonValue nj = JsonValue::MakeObj();
    JsonValue cm = JsonValue::MakeArr();
    for (int16_t mv : n.child_moves) cm.arr_val.push_back(JsonValue::MakeInt(mv));
    JsonValue ci = JsonValue::MakeArr();
    for (uint32_t cid : n.child_node_ids) {
      ci.arr_val.push_back(JsonValue::MakeInt(cid));
    }
    nj.obj_val["childMoves"] = std::move(cm);
    nj.obj_val["childNodeIds"] = std::move(ci);
    nj.obj_val["disproofRzCoords"] =
        MakeIntArray(n.disproof_rz.Bits().ToCoords());
    nj.obj_val["dn"] = EncodeSatJson(n.dn);
    nj.obj_val["incomingMove"] = JsonValue::MakeInt(n.incoming_move);
    nj.obj_val["incomingMoveSgf"] =
        JsonValue::MakeStr(MoveToSgfLabel(n.incoming_move, N));
    nj.obj_val["isKoDependentBarrier"] = JsonValue::MakeBool(false);
    nj.obj_val["isOrNode"] = JsonValue::MakeBool(n.is_or_node);
    nj.obj_val["isPrunedOutsideRz"] =
        JsonValue::MakeBool(n.is_pruned_outside_rz);
    nj.obj_val["isTtHit"] = JsonValue::MakeBool(n.is_tt_hit);
    nj.obj_val["nodeId"] = JsonValue::MakeInt(n.node_id);
    nj.obj_val["outcome"] = JsonValue::MakeStr(OutcomeToStr(n.outcome));
    nj.obj_val["pn"] = EncodeSatJson(n.pn);
    nj.obj_val["proofRzCoords"] = MakeIntArray(n.proof_rz.Bits().ToCoords());
    nj.obj_val["prunedCertificate"] = JsonValue::MakeNull();
    if ((n.is_pruned_outside_rz || n.is_tt_hit) &&
        n.source_proof_node_id != kInvalidDagNodeId) {
      nj.obj_val["sourceProofNodeId"] =
          JsonValue::MakeInt(n.source_proof_node_id);
    } else {
      nj.obj_val["sourceProofNodeId"] = JsonValue::MakeNull();
    }
    nj.obj_val["terminalEvidence"] = JsonValue::MakeStr(EvidenceKindToStr(n));
    nj.obj_val["toPlay"] =
        JsonValue::MakeStr(n.to_play == Color::kWhite ? "W" : "B");
    nodes_arr.arr_val.push_back(std::move(nj));
  }
  root.obj_val["nodes"] = std::move(nodes_arr);

  const std::string jcs_body = CanonicalizeJcs(root);
  const std::string checksum = "sha256-jcs:" + Sha256Hex(jcs_body);
  root.obj_val["checksum"] = JsonValue::MakeStr(checksum);
  if (out_checksum != nullptr) *out_checksum = checksum;
  return PrettyPrintJson(root, 0) + "\n";
}

template <int N>
std::string ProofArtifactManager<N>::ExportSolutionTreeSgf(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report) const {
  (void)context;
  std::ostringstream sgf;
  sgf << "(;GM[1]FF[4]CA[UTF-8]AP[LDProver:1.8.2]SZ[" << N << "]PL["
      << (initial_pos.ToPlay() == Color::kWhite ? "W" : "B") << "]";

  const auto black_coords = initial_pos.Stones(Color::kBlack).ToCoords();
  if (!black_coords.empty()) {
    sgf << "AB";
    for (int c : black_coords) {
      sgf << "[" << CoordToSgf(static_cast<int16_t>(c), N) << "]";
    }
  }
  const auto white_coords = initial_pos.Stones(Color::kWhite).ToCoords();
  if (!white_coords.empty()) {
    sgf << "AW";
    for (int c : white_coords) {
      sgf << "[" << CoordToSgf(static_cast<int16_t>(c), N) << "]";
    }
  }

  sgf << "C[LDProver v1.8.2 | RootStatus: " << OutcomeToStr(report.root_status)
      << " | PN=" << report.root_pn << " DN=" << report.root_dn
      << " | RZ=" << report.rz_size_at_root << "]";

  Color cur_col = initial_pos.ToPlay();
  for (int16_t mv : report.principal_variation) {
    sgf << ";" << (cur_col == Color::kBlack ? 'B' : 'W') << "["
        << CoordToSgf(mv, N) << "]";
    cur_col = OppositeColor(cur_col);
  }
  sgf << ")";
  return sgf.str();
}

template <int N>
VerificationReport ProofArtifactManager<N>::VerifyProofDag(
    const Position<N>& initial_pos, const ProofContext& context,
    const SolveReport<N>& report) const {
  VerificationReport ver;
  SerializeLProofJson(initial_pos, context, report, &ver.jcs_sha256_checksum);

  if (report.root_status == ProofOutcome::kUnknown) {
    ver.passed = false;
    ver.error_code = "LP-U01";
    ver.message =
        "Root proposition is UNKNOWN; only PROVEN_* carry complete proof DAGs.";
    return ver;
  }

  if (report.proof_dag_nodes.empty() ||
      report.root_dag_node_id >= report.proof_dag_nodes.size()) {
    ver.passed = false;
    ver.error_code = "LP-S01";
    ver.message = "Missing or out-of-range rootNode in lproof/1 DAG.";
    return ver;
  }

  const auto& root_node = report.proof_dag_nodes[report.root_dag_node_id];
  if (root_node.outcome != report.root_status) {
    ver.passed = false;
    ver.failed_node_id = static_cast<int32_t>(report.root_dag_node_id);
    ver.error_code = "LP-R00";
    ver.message = "report.root_status disagrees with root ProofDagNode outcome.";
    return ver;
  }

  if ((report.root_status == ProofOutcome::kProvenWin &&
       (report.root_pn != 0 || report.root_dn != kPnDnSaturation)) ||
      (report.root_status == ProofOutcome::kProvenLoss &&
       (report.root_pn != kPnDnSaturation || report.root_dn != 0))) {
    ver.passed = false;
    ver.failed_node_id = static_cast<int32_t>(report.root_dag_node_id);
    ver.error_code = "LP-N15";
    ver.message = "Root report (root_pn, root_dn) violates saturation binding.";
    return ver;
  }

  // Structural & topological pass across all DAG nodes.
  for (size_t i = 0; i < report.proof_dag_nodes.size(); ++i) {
    const auto& node = report.proof_dag_nodes[i];
    ++ver.verified_nodes;
    if (node.node_id != static_cast<uint32_t>(i)) {
      ver.passed = false;
      ver.failed_node_id = static_cast<int32_t>(i);
      ver.error_code = "LP-T01";
      ver.message = "ProofDagNode node_id does not match array index.";
      return ver;
    }

    if (node.outcome == ProofOutcome::kProvenWin) {
      if (node.pn != 0 || node.dn != kPnDnSaturation) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-N15";
        ver.message = "Win node violates (PN=0, DN=SAT) binding.";
        return ver;
      }
    } else if (node.outcome == ProofOutcome::kProvenLoss) {
      if (node.pn != kPnDnSaturation || node.dn != 0) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-N15";
        ver.message = "Loss node violates (PN=SAT, DN=0) binding.";
        return ver;
      }
    } else {
      ver.passed = false;
      ver.failed_node_id = static_cast<int32_t>(node.node_id);
      ver.error_code = "LP-U02";
      ver.message = "ProofDagNode inside proven DAG carries UNKNOWN outcome.";
      return ver;
    }

    if (node.child_moves.size() != node.child_node_ids.size()) {
      ver.passed = false;
      ver.failed_node_id = static_cast<int32_t>(node.node_id);
      ver.error_code = "LP-T02";
      ver.message = "child_moves and child_node_ids length mismatch.";
      return ver;
    }

    for (uint32_t child_id : node.child_node_ids) {
      if (child_id >= node.node_id) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-T02";
        ver.message =
            "Post-order topological DAG constraint violated (child_id >= "
            "node_id).";
        return ver;
      }
    }

    if (node.is_pruned_outside_rz || node.is_tt_hit) {
      // Strict acyclicity: source_proof_node_id MUST strictly precede node_id!
      // Rejects self-referencing prunes (e.g. node_id=0, source_proof_node_id=0).
      if (node.source_proof_node_id >= node.node_id ||
          node.source_proof_node_id >= report.proof_dag_nodes.size() ||
          report.proof_dag_nodes[node.source_proof_node_id].outcome !=
              node.outcome) {
        ver.passed = false;
        ver.failed_node_id = static_cast<int32_t>(node.node_id);
        ver.error_code = "LP-R02";
        ver.message =
            "Pruned/TT node has cyclic, out-of-order, or mismatched "
            "source_proof_node_id.";
        return ver;
      }
    }
  }

  // Verify root input_hash binding to `initial_pos`.
  if (report.input_hash != initial_pos.ZobristHash()) {
    ver.passed = false;
    ver.failed_node_id = static_cast<int32_t>(report.root_dag_node_id);
    ver.error_code = "LP-C01";
    ver.message =
        "report.input_hash does not match initial_pos.ZobristHash().";
    return ver;
  }

  // Zero-trust full recursive DAG verification from `initial_pos`.
  BensonTerminalEvaluator<N> independent_terminal;
  if (!VerifySubgraphRecursive<N>(initial_pos, context, report,
                                  report.root_dag_node_id, independent_terminal,
                                  0U, &ver)) {
    ver.passed = false;
    return ver;
  }

  ver.passed = true;
  ver.error_code = "PASS";
  ver.message =
      "All reachable lproof/1 nodes, SSK/PSK HistorySets, universal move "
      "obligations, Classic Benson leaves, and RZ certificates verified.";
  return ver;
}

template <int N>
VerificationReport ProofArtifactManager<N>::VerifyLProofJsonString(
    const std::string& json_text,
    const ParsedProblem<N>* expected_problem) const {
  VerificationReport ver;
  JsonValue root;
  JsonParser parser(json_text);
  if (!parser.ParseDocument(&root) || root.kind != JsonValue::Kind::kObject) {
    ver.passed = false;
    ver.error_code = "LP-J01";
    ver.message = "Malformed JSON syntax or non-object root in standalone lproof/1 file.";
    return ver;
  }

  const auto it_magic = root.obj_val.find("magic");
  const auto it_chk = root.obj_val.find("checksum");
  const auto it_ctx = root.obj_val.find("context");
  const auto it_setup = root.obj_val.find("problemSetup");
  const auto it_nodes = root.obj_val.find("nodes");

  if (it_magic == root.obj_val.end() ||
      it_magic->second.kind != JsonValue::Kind::kString ||
      it_magic->second.str_val != "lproof/1" ||
      it_chk == root.obj_val.end() ||
      it_chk->second.kind != JsonValue::Kind::kString ||
      it_ctx == root.obj_val.end() ||
      it_ctx->second.kind != JsonValue::Kind::kObject ||
      it_setup == root.obj_val.end() ||
      it_setup->second.kind != JsonValue::Kind::kObject ||
      it_nodes == root.obj_val.end() ||
      it_nodes->second.kind != JsonValue::Kind::kArray) {
    ver.passed = false;
    ver.error_code = "LP-J02";
    ver.message = "Missing required top-level lproof/1 sections.";
    return ver;
  }

  const auto& setup_obj = it_setup->second.obj_val;
  int64_t parsed_bs = -1;
  if (const auto it_sbs = setup_obj.find("boardSize");
      it_sbs != setup_obj.end() && it_sbs->second.kind == JsonValue::Kind::kInt) {
    parsed_bs = it_sbs->second.int_val;
  } else if (const auto it_bs = root.obj_val.find("boardSize");
             it_bs != root.obj_val.end() &&
             it_bs->second.kind == JsonValue::Kind::kInt) {
    parsed_bs = it_bs->second.int_val;
  }
  if (parsed_bs != N) {
    ver.passed = false;
    ver.error_code = "LP-J02";
    ver.message = "Missing or mismatched boardSize in lproof/1 file.";
    return ver;
  }

  const std::string file_checksum = it_chk->second.str_val;
  ver.jcs_sha256_checksum = file_checksum;

  JsonValue without_chk = root;
  without_chk.obj_val.erase("checksum");
  const std::string expected_chk =
      "sha256-jcs:" + Sha256Hex(CanonicalizeJcs(without_chk));
  if (file_checksum != expected_chk) {
    ver.passed = false;
    ver.error_code = "LP-C01";
    ver.message =
        "Standalone lproof/1 RFC 8785 JCS SHA-256 checksum mismatch.";
    return ver;
  }

  ProofContext context;
  Position<N> initial_pos;
  SolveReport<N> report;
  BitBoard<N> origin_b_bits;
  BitBoard<N> origin_w_bits;
  BitBoard<N> wall_bits;
  Color origin_turn = Color::kBlack;

  try {
    if (const auto it_pid = root.obj_val.find("problemId");
        it_pid != root.obj_val.end() &&
        it_pid->second.kind == JsonValue::Kind::kString) {
      report.problem_id = it_pid->second.str_val;
    }

    const auto& ctx_obj = it_ctx->second.obj_val;
    if (const auto it = ctx_obj.find("contextId");
        it != ctx_obj.end() && it->second.kind == JsonValue::Kind::kString) {
      ParseHexU64(it->second.str_val, &context.context_id);
    }
    if (const auto it = ctx_obj.find("rootAttacker"); it == ctx_obj.end() ||
        !ParseColorValue(it->second, &context.root_attacker)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid or missing context.rootAttacker.";
      return ver;
    }
    if (const auto it = ctx_obj.find("attackerGoal");
        it == ctx_obj.end() || it->second.kind != JsonValue::Kind::kString ||
        (it->second.str_val != "TOKILL" && it->second.str_val != "TOLIVE")) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid or missing context.attackerGoal.";
      return ver;
    } else {
      context.attacker_goal = (it->second.str_val == "TOKILL")
                                  ? SearchGoal::kToKill
                                  : SearchGoal::kToLive;
    }
    if (const auto it = ctx_obj.find("crucialStoneOp"); it == ctx_obj.end() ||
        !ParseLogicalOp(it->second, &context.crucial_stone_op)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid or missing context.crucialStoneOp.";
      return ver;
    }
    if (const auto it = ctx_obj.find("koRule"); it == ctx_obj.end() ||
        !ParseKoRule(it->second, &context.ko_rule)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid or missing context.koRule.";
      return ver;
    }
    if (const auto it = ctx_obj.find("attackerAllowKo");
        it != ctx_obj.end() && it->second.kind == JsonValue::Kind::kBool) {
      context.attacker_allow_ko = it->second.bool_val;
    }
    if (const auto it = ctx_obj.find("defenderAllowKo");
        it != ctx_obj.end() && it->second.kind == JsonValue::Kind::kBool) {
      context.defender_allow_ko = it->second.bool_val;
    }
    if (const auto it = ctx_obj.find("initialTokens");
        it != ctx_obj.end() && it->second.kind == JsonValue::Kind::kArray) {
      for (const auto& tj : it->second.arr_val) {
        if (tj.kind != JsonValue::Kind::kObject) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Malformed token entry in context.initialTokens.";
          return ver;
        }
        const auto& tid_v = tj.obj_val.at("tokenId");
        const auto& ico_v = tj.obj_val.at("initialCoord");
        const auto& gix_v = tj.obj_val.at("groupIndex");
        if (tid_v.kind != JsonValue::Kind::kInt ||
            ico_v.kind != JsonValue::Kind::kInt ||
            gix_v.kind != JsonValue::Kind::kInt ||
            ico_v.int_val < 0 || ico_v.int_val >= N * N) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Invalid token integer fields in context.initialTokens.";
          return ver;
        }
        TargetToken tok;
        tok.token_id = static_cast<uint16_t>(tid_v.int_val);
        tok.initial_coord = static_cast<int16_t>(ico_v.int_val);
        tok.group_index = static_cast<uint8_t>(gix_v.int_val);
        if (!ParseColorValue(tj.obj_val.at("stoneColor"), &tok.stone_color)) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Invalid stoneColor in context.initialTokens.";
          return ver;
        }
        context.initial_tokens.push_back(tok);
      }
    }

    auto load_coords_to_bits = [&](const std::string& key, BitBoard<N>* bits,
                                   bool required) -> bool {
      const auto it = setup_obj.find(key);
      if (it == setup_obj.end()) return !required;
      if (it->second.kind != JsonValue::Kind::kArray) return false;
      for (const auto& elem : it->second.arr_val) {
        if (elem.kind != JsonValue::Kind::kInt || elem.int_val < 0 ||
            elem.int_val >= N * N) {
          return false;
        }
        bits->Set(static_cast<int>(elem.int_val), true);
      }
      return true;
    };

    BitBoard<N> claimed_b_bits;
    BitBoard<N> claimed_w_bits;
    if (!load_coords_to_bits("blackInitialCoords", &claimed_b_bits, true) ||
        !load_coords_to_bits("whiteInitialCoords", &claimed_w_bits, true) ||
        !load_coords_to_bits("immortalWallCoords", &wall_bits, false)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid stone/wall coordinate array in problemSetup.";
      return ver;
    }

    Color first_to_play = Color::kBlack;
    if (const auto it = setup_obj.find("firstToPlay"); it == setup_obj.end() ||
        !ParseColorValue(it->second, &first_to_play)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid or missing problemSetup.firstToPlay.";
      return ver;
    }

    std::string root_kind = "initial";
    if (const auto it_rk = setup_obj.find("rootKind");
        it_rk != setup_obj.end()) {
      if (it_rk->second.kind != JsonValue::Kind::kString ||
          (it_rk->second.str_val != "initial" &&
           it_rk->second.str_val != "traced_subposition")) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid problemSetup.rootKind.";
        return ver;
      }
      root_kind = it_rk->second.str_val;
    }

    initial_pos.Clear(context);
    if (root_kind == "traced_subposition") {
      const auto it_oturn = setup_obj.find("originFirstToPlay");
      const auto it_trace = setup_obj.find("initialTraceMoves");
      if (it_oturn == setup_obj.end() ||
          !ParseColorValue(it_oturn->second, &origin_turn) ||
          it_trace == setup_obj.end() ||
          it_trace->second.kind != JsonValue::Kind::kArray ||
          it_trace->second.arr_val.empty() ||
          !load_coords_to_bits("originBlackCoords", &origin_b_bits, true) ||
          !load_coords_to_bits("originWhiteCoords", &origin_w_bits, true)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message =
            "traced_subposition requires origin coords, originFirstToPlay, and "
            "non-empty initialTraceMoves.";
        return ver;
      }
      for (int c : origin_b_bits.ToCoords()) {
        initial_pos.SetupInitialStone(c, Color::kBlack);
      }
      for (int c : origin_w_bits.ToCoords()) {
        initial_pos.SetupInitialStone(c, Color::kWhite);
      }
      initial_pos.SetImmortalWall(wall_bits);
      initial_pos.FinalizeInitialPosition(origin_turn);

      for (const auto& mv_val : it_trace->second.arr_val) {
        if (mv_val.kind != JsonValue::Kind::kInt ||
            mv_val.int_val < kPassMove || mv_val.int_val >= N * N) {
          ver.passed = false;
          ver.error_code = "LP-S09";
          ver.message = "Invalid move coordinate in initialTraceMoves.";
          return ver;
        }
        if (!initial_pos.PlayMove(static_cast<int16_t>(mv_val.int_val))) {
          ver.passed = false;
          ver.error_code = "LP-S09";
          ver.message =
              "Illegal move in traced_subposition initialTraceMoves replay.";
          return ver;
        }
      }

      if (initial_pos.Stones(Color::kBlack) != claimed_b_bits ||
          initial_pos.Stones(Color::kWhite) != claimed_w_bits ||
          initial_pos.ToPlay() != first_to_play) {
        ver.passed = false;
        ver.error_code = "LP-S02";
        ver.message =
            "Replayed traced_subposition disagrees with declared "
            "blackInitialCoords/whiteInitialCoords/firstToPlay.";
        return ver;
      }
    } else {
      origin_b_bits = claimed_b_bits;
      origin_w_bits = claimed_w_bits;
      origin_turn = first_to_play;
      for (int c : claimed_b_bits.ToCoords()) {
        initial_pos.SetupInitialStone(c, Color::kBlack);
      }
      for (int c : claimed_w_bits.ToCoords()) {
        initial_pos.SetupInitialStone(c, Color::kWhite);
      }
      initial_pos.SetImmortalWall(wall_bits);
      initial_pos.FinalizeInitialPosition(first_to_play);
    }

    if (const auto it_ko = setup_obj.find("koPoint");
        it_ko != setup_obj.end() && it_ko->second.kind == JsonValue::Kind::kInt &&
        it_ko->second.int_val != initial_pos.KoPoint()) {
      ver.passed = false;
      ver.error_code = "LP-S02";
      ver.message = "problemSetup.koPoint disagrees with reconstructed position.";
      return ver;
    }
    if (const auto it_cp = setup_obj.find("consecutivePasses");
        it_cp != setup_obj.end() && it_cp->second.kind == JsonValue::Kind::kInt &&
        it_cp->second.int_val != initial_pos.ConsecutivePasses()) {
      ver.passed = false;
      ver.error_code = "LP-S02";
      ver.message =
          "problemSetup.consecutivePasses disagrees with reconstructed position.";
      return ver;
    }
    if (const auto it_stm = setup_obj.find("survivingTokensMask");
        it_stm != setup_obj.end() &&
        it_stm->second.kind == JsonValue::Kind::kInt &&
        static_cast<uint64_t>(it_stm->second.int_val) !=
            initial_pos.SurvivingTargetTokensMask()) {
      ver.passed = false;
      ver.error_code = "LP-S02";
      ver.message =
          "problemSetup.survivingTokensMask disagrees with reconstructed "
          "position.";
      return ver;
    }
    if (const auto it_zh = setup_obj.find("zobristHex");
        it_zh != setup_obj.end() &&
        it_zh->second.kind == JsonValue::Kind::kString) {
      uint64_t claimed_zh = 0;
      if (!ParseHexU64(it_zh->second.str_val, &claimed_zh) ||
          claimed_zh != initial_pos.ZobristHash()) {
        ver.passed = false;
        ver.error_code = "LP-C01";
        ver.message =
            "problemSetup.zobristHex disagrees with reconstructed position hash.";
        return ver;
      }
    }

    if (const auto it = setup_obj.find("inputHash");
        it == setup_obj.end() ||
        it->second.kind != JsonValue::Kind::kString ||
        !ParseHexU64(it->second.str_val, &report.input_hash)) {
      ver.passed = false;
      ver.error_code = "LP-C01";
      ver.message =
          "Missing or invalid inputHash hex string in standalone lproof/1 "
          "file.";
      return ver;
    }

    bool has_region_hint = false;
    if (const auto it_hr = setup_obj.find("hasRegionHint");
        it_hr != setup_obj.end() &&
        it_hr->second.kind == JsonValue::Kind::kBool) {
      has_region_hint = it_hr->second.bool_val;
    } else if (const auto it_rc = setup_obj.find("regionCoords");
               it_rc != setup_obj.end() &&
               it_rc->second.kind == JsonValue::Kind::kArray &&
               !it_rc->second.arr_val.empty()) {
      has_region_hint = true;
    }
    if (has_region_hint) {
      BitBoard<N> reg_bits;
      if (!load_coords_to_bits("regionCoords", &reg_bits, true)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid problemSetup.regionCoords array.";
        return ver;
      }
      report.region_hint = reg_bits;
    }

    // F4: Optional external problem binding check (--problem <original.json>).
    if (expected_problem != nullptr) {
      if (!expected_problem->valid) {
        ver.passed = false;
        ver.error_code = "LP-P01";
        ver.message = "External problem contract is invalid.";
        return ver;
      }
      const auto& ep_pos = expected_problem->initial_position;
      const auto& ep_ctx = expected_problem->proof_context;
      const bool board_matches =
          (origin_b_bits == ep_pos.Stones(Color::kBlack)) &&
          (origin_w_bits == ep_pos.Stones(Color::kWhite)) &&
          (wall_bits == ep_pos.ImmortalWall()) &&
          (origin_turn == ep_pos.ToPlay());
      const bool ctx_matches =
          (context.root_attacker == ep_ctx.root_attacker) &&
          (context.attacker_goal == ep_ctx.attacker_goal) &&
          (context.crucial_stone_op == ep_ctx.crucial_stone_op) &&
          (context.ko_rule == ep_ctx.ko_rule) &&
          (context.attacker_allow_ko == ep_ctx.attacker_allow_ko) &&
          (context.defender_allow_ko == ep_ctx.defender_allow_ko) &&
          TargetTokensEqual(context.initial_tokens, ep_ctx.initial_tokens);
      const bool region_matches =
          (report.region_hint.has_value() ==
           expected_problem->region_search_mask.has_value()) &&
          (!report.region_hint.has_value() ||
           (*report.region_hint == *expected_problem->region_search_mask));
      if (!board_matches || !ctx_matches || !region_matches) {
        ver.passed = false;
        ver.error_code = "LP-P01";
        ver.message =
            "Proof certificate does not match external --problem identity "
            "(stones, turn, immortal walls, context, tokens, or region).";
        return ver;
      }
    }

    // Validate optional stateTable shape when verifying full-table TS exports.
    if (const auto it_st = root.obj_val.find("stateTable");
        it_st != root.obj_val.end()) {
      if (it_st->second.kind != JsonValue::Kind::kArray ||
          it_st->second.arr_val.empty() ||
          it_st->second.arr_val[0].kind != JsonValue::Kind::kObject) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Malformed optional stateTable in lproof/1 file.";
        return ver;
      }
      const auto& s0 = it_st->second.arr_val[0].obj_val;
      if (const auto it_z0 = s0.find("zobristHex");
          it_z0 != s0.end() &&
          it_z0->second.kind == JsonValue::Kind::kString) {
        uint64_t z0 = 0;
        if (!ParseHexU64(it_z0->second.str_val, &z0) ||
            z0 != initial_pos.ZobristHash()) {
          ver.passed = false;
          ver.error_code = "LP-S02";
          ver.message = "stateTable[0].zobristHex disagrees with initial position.";
          return ver;
        }
      }
    }

    if (const auto it = root.obj_val.find("rootOutcome");
        it == root.obj_val.end() ||
        it->second.kind != JsonValue::Kind::kString ||
        !StrToOutcome(it->second.str_val, &report.root_status)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid rootOutcome in standalone lproof/1 file.";
      return ver;
    }
    const auto& rn_val = root.obj_val.at("rootNode");
    if (rn_val.kind != JsonValue::Kind::kInt || rn_val.int_val < 0) {
      report.root_dag_node_id = kInvalidDagNodeId;
    } else {
      report.root_dag_node_id = static_cast<uint32_t>(rn_val.int_val);
    }
    if (!ParseSatU32(root.obj_val.at("rootPn"), &report.root_pn) ||
        !ParseSatU32(root.obj_val.at("rootDn"), &report.root_dn)) {
      ver.passed = false;
      ver.error_code = "LP-J02";
      ver.message = "Invalid rootPn or rootDn in standalone lproof/1 file.";
      return ver;
    }
    if (const auto it = root.obj_val.find("bestMove");
        it != root.obj_val.end() && it->second.kind == JsonValue::Kind::kInt) {
      report.best_move = static_cast<int16_t>(it->second.int_val);
    }

    for (const auto& nj : it_nodes->second.arr_val) {
      if (nj.kind != JsonValue::Kind::kObject) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Malformed node entry in standalone lproof/1 file.";
        return ver;
      }
      const auto& nid_v = nj.obj_val.at("nodeId");
      const auto& or_v = nj.obj_val.at("isOrNode");
      const auto& im_v = nj.obj_val.at("incomingMove");
      const auto& out_v = nj.obj_val.at("outcome");
      const auto& prz_v = nj.obj_val.at("isPrunedOutsideRz");
      const auto& tt_v = nj.obj_val.at("isTtHit");
      const auto& pcoords_v = nj.obj_val.at("proofRzCoords");
      const auto& dcoords_v = nj.obj_val.at("disproofRzCoords");
      const auto& cm_v = nj.obj_val.at("childMoves");
      const auto& ci_v = nj.obj_val.at("childNodeIds");
      if (nid_v.kind != JsonValue::Kind::kInt || nid_v.int_val < 0 ||
          or_v.kind != JsonValue::Kind::kBool ||
          im_v.kind != JsonValue::Kind::kInt ||
          out_v.kind != JsonValue::Kind::kString ||
          prz_v.kind != JsonValue::Kind::kBool ||
          tt_v.kind != JsonValue::Kind::kBool ||
          pcoords_v.kind != JsonValue::Kind::kArray ||
          dcoords_v.kind != JsonValue::Kind::kArray ||
          cm_v.kind != JsonValue::Kind::kArray ||
          ci_v.kind != JsonValue::Kind::kArray) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid node field type in standalone lproof/1 file.";
        return ver;
      }

      ProofDagNode<N> node;
      node.node_id = static_cast<uint32_t>(nid_v.int_val);
      node.is_or_node = or_v.bool_val;
      if (!ParseColorValue(nj.obj_val.at("toPlay"), &node.to_play)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid node toPlay in standalone lproof/1 file.";
        return ver;
      }
      node.incoming_move = static_cast<int16_t>(im_v.int_val);
      if (!ParseSatU32(nj.obj_val.at("pn"), &node.pn) ||
          !ParseSatU32(nj.obj_val.at("dn"), &node.dn)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid node pn/dn in standalone lproof/1 file.";
        return ver;
      }
      if (!StrToOutcome(out_v.str_val, &node.outcome)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid node outcome in standalone lproof/1 file.";
        return ver;
      }
      if (!ParseEvidenceKind(nj.obj_val.at("terminalEvidence"),
                             &node.terminal_evidence)) {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid node terminalEvidence in standalone lproof/1 file.";
        return ver;
      }
      node.is_pruned_outside_rz = prz_v.bool_val;
      node.is_tt_hit = tt_v.bool_val;
      const auto& spn = nj.obj_val.at("sourceProofNodeId");
      if (spn.kind == JsonValue::Kind::kNull) {
        node.source_proof_node_id = kInvalidDagNodeId;
      } else if (spn.kind == JsonValue::Kind::kInt && spn.int_val >= 0) {
        node.source_proof_node_id = static_cast<uint32_t>(spn.int_val);
      } else {
        ver.passed = false;
        ver.error_code = "LP-J02";
        ver.message = "Invalid sourceProofNodeId in standalone lproof/1 file.";
        return ver;
      }

      BitBoard<N> p_rz;
      BitBoard<N> d_rz;
      for (const auto& el : pcoords_v.arr_val) {
        if (el.kind != JsonValue::Kind::kInt) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Non-integer entry in proofRzCoords.";
          return ver;
        }
        const int c = static_cast<int>(el.int_val);
        if (c >= 0 && c < N * N) p_rz.Set(c, true);
      }
      for (const auto& el : dcoords_v.arr_val) {
        if (el.kind != JsonValue::Kind::kInt) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Non-integer entry in disproofRzCoords.";
          return ver;
        }
        const int c = static_cast<int>(el.int_val);
        if (c >= 0 && c < N * N) d_rz.Set(c, true);
      }
      node.proof_rz = ProofCertificateRZ<N>(p_rz);
      node.disproof_rz = ProofCertificateRZ<N>(d_rz);

      for (const auto& el : cm_v.arr_val) {
        if (el.kind != JsonValue::Kind::kInt) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Non-integer entry in childMoves.";
          return ver;
        }
        node.child_moves.push_back(static_cast<int16_t>(el.int_val));
      }
      for (const auto& el : ci_v.arr_val) {
        if (el.kind != JsonValue::Kind::kInt || el.int_val < 0) {
          ver.passed = false;
          ver.error_code = "LP-J02";
          ver.message = "Invalid entry in childNodeIds.";
          return ver;
        }
        node.child_node_ids.push_back(static_cast<uint32_t>(el.int_val));
      }
      report.proof_dag_nodes.push_back(std::move(node));
    }
  } catch (const std::exception& e) {
    ver.passed = false;
    ver.error_code = "LP-J02";
    ver.message =
        std::string("Incomplete lproof/1 field structure: ") + e.what();
    return ver;
  }

  return VerifyProofDag(initial_pos, context, report);
}

template class ProofArtifactManager<5>;
template class ProofArtifactManager<7>;
template class ProofArtifactManager<19>;

}  // namespace ldprover
