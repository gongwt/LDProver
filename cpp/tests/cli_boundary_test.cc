// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: tests/cli_boundary_test.cc
// Description: Versioned CLI boundary & path-reservation regression suite for
// `tprover solve | check | bench` (R22/R23 P1 & P2 fixes). Passes raw,
// un-normalized paths directly via fork/execv without shell or path rewriting.

#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <system_error>
#include <vector>

#if defined(__APPLE__) || defined(__unix__)
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>
#elif defined(_WIN32)
#include <process.h>
#endif

namespace {

int g_total = 0;
int g_passed = 0;
int g_failed = 0;

void Check(bool cond, const std::string& name, const std::string& detail) {
  ++g_total;
  if (cond) {
    ++g_passed;
    std::cout << "  [PASS] " << name << "\n";
  } else {
    ++g_failed;
    std::cout << "  [FAIL] " << name << " -> " << detail << "\n";
  }
}

bool ReadBytes(const std::filesystem::path& p, std::string* out) {
  std::ifstream ifs(p, std::ios::in | std::ios::binary);
  if (!ifs.is_open()) return false;
  std::ostringstream ss;
  ss << ifs.rdbuf();
  *out = ss.str();
  return !ifs.bad();
}

bool WriteBytes(const std::filesystem::path& p, const std::string& data) {
  std::ofstream ofs(p, std::ios::out | std::ios::binary | std::ios::trunc);
  if (!ofs.is_open()) return false;
  ofs << data;
  return ofs.good();
}

std::string JsonEscapePath(const std::string& s) {
  std::string out;
  for (char c : s) {
    if (c == '\\') out.append("\\\\");
    else if (c == '"') out.append("\\\"");
    else out.push_back(c);
  }
  return out;
}

#if defined(__APPLE__) || defined(__unix__)

struct ExecResult {
  int exit_code = -1;
  std::string stdout_str;
  std::string stderr_str;
};

std::string DrainFd(int fd) {
  std::string out;
  char buf[4096];
  while (true) {
    const ssize_t n = ::read(fd, buf, sizeof(buf));
    if (n > 0) {
      out.append(buf, static_cast<size_t>(n));
    } else if (n == 0) {
      break;
    } else {
      break;
    }
  }
  return out;
}

ExecResult RunCliRaw(const std::string& bin_path,
                     const std::vector<std::string>& args,
                     const std::string& working_dir = "",
                     int umask_override = -1) {
  ExecResult res;
  int out_pipe[2] = {-1, -1};
  int err_pipe[2] = {-1, -1};
  if (::pipe(out_pipe) != 0 || ::pipe(err_pipe) != 0) {
    return res;
  }

  const pid_t pid = ::fork();
  if (pid < 0) {
    ::close(out_pipe[0]);
    ::close(out_pipe[1]);
    ::close(err_pipe[0]);
    ::close(err_pipe[1]);
    return res;
  }

  if (pid == 0) {
    ::dup2(out_pipe[1], STDOUT_FILENO);
    ::dup2(err_pipe[1], STDERR_FILENO);
    ::close(out_pipe[0]);
    ::close(out_pipe[1]);
    ::close(err_pipe[0]);
    ::close(err_pipe[1]);

    if (umask_override >= 0) {
      ::umask(static_cast<mode_t>(umask_override));
    }

    if (!working_dir.empty()) {
      if (::chdir(working_dir.c_str()) != 0) {
        ::_exit(126);
      }
    }

    std::vector<std::string> storage;
    storage.reserve(1U + args.size());
    storage.push_back(bin_path);
    for (const std::string& a : args) storage.push_back(a);

    std::vector<char*> argv_ptrs;
    argv_ptrs.reserve(storage.size() + 1U);
    for (std::string& s : storage) argv_ptrs.push_back(s.data());
    argv_ptrs.push_back(nullptr);

    ::execv(bin_path.c_str(), argv_ptrs.data());
    ::_exit(127);
  }

  ::close(out_pipe[1]);
  ::close(err_pipe[1]);
  res.stdout_str = DrainFd(out_pipe[0]);
  res.stderr_str = DrainFd(err_pipe[0]);
  ::close(out_pipe[0]);
  ::close(err_pipe[0]);

  int status = 0;
  if (::waitpid(pid, &status, 0) > 0 && WIFEXITED(status)) {
    res.exit_code = WEXITSTATUS(status);
  }
  return res;
}

bool DetectCaseInsensitiveVolume(const std::filesystem::path& dir) {
  const std::filesystem::path lower = dir / "case_probe_tmp.txt";
  const std::filesystem::path upper = dir / "CASE_PROBE_TMP.TXT";
  WriteBytes(lower, "probe");
  struct stat s1 {};
  struct stat s2 {};
  const bool ok = (::stat(lower.c_str(), &s1) == 0 &&
                   ::stat(upper.c_str(), &s2) == 0 &&
                   s1.st_dev == s2.st_dev && s1.st_ino == s2.st_ino);
  std::error_code ec;
  std::filesystem::remove(lower, ec);
  return ok;
}

struct TempWorkspaceGuard {
  std::filesystem::path root;
  ~TempWorkspaceGuard() {
    std::error_code ec;
    if (!root.empty()) std::filesystem::remove_all(root, ec);
  }
};

#elif defined(_WIN32)

struct TempWorkspaceGuard {
  std::filesystem::path root;
  ~TempWorkspaceGuard() {
    std::error_code ec;
    if (!root.empty()) std::filesystem::remove_all(root, ec);
  }
};

int RunWinRaw(const std::string& bin_path,
              const std::vector<std::string>& args) {
  std::vector<std::string> storage;
  storage.reserve(1U + args.size());
  storage.push_back(bin_path);
  for (const std::string& a : args) storage.push_back(a);
  std::vector<const char*> ptrs;
  ptrs.reserve(storage.size() + 1U);
  for (const std::string& s : storage) ptrs.push_back(s.c_str());
  ptrs.push_back(nullptr);
  return _spawnv(_P_WAIT, bin_path.c_str(), ptrs.data());
}

#endif

}  // namespace

int main(int argc, char* argv[]) {
  if (argc < 3) {
    std::cerr << "Usage: ldprover_cli_tests <tprover_bin> <tsumego_dir> "
                 "[--skip-concurrent]\n";
    return 2;
  }
  const std::string tprover_bin = argv[1];
  const std::filesystem::path tsumego_dir(argv[2]);
  bool skip_concurrent = false;
  for (int i = 3; i < argc; ++i) {
    if (std::string(argv[i]) == "--skip-concurrent") skip_concurrent = true;
  }
  const std::filesystem::path p042_src = tsumego_dir / "chao_vol1_p042.json";
  const std::filesystem::path p031_src = tsumego_dir / "chao_vol1_p031.json";

  std::string p042_bytes;
  std::string p031_bytes;
  if (!ReadBytes(p042_src, &p042_bytes) || !ReadBytes(p031_src, &p031_bytes)) {
    std::cerr << "Cannot read fixture JSONs in " << tsumego_dir << "\n";
    return 2;
  }

#if !(defined(__APPLE__) || defined(__unix__))
#if defined(_WIN32)
  std::error_code ec;
  const std::filesystem::path tmp_base =
      std::filesystem::temp_directory_path(ec);
  TempWorkspaceGuard ws{tmp_base /
                        ("ldprover_cli_win_" + std::to_string(_getpid()))};
  std::filesystem::remove_all(ws.root, ec);
  std::filesystem::create_directories(ws.root, ec);
  const auto prev_cwd = std::filesystem::current_path(ec);
  std::filesystem::current_path(ws.root, ec);

  // Portable Win32 subset: same-file, ./pending.json alias, existing bytes,
  // bench member protection, and valid separated run
  {
    const int rc = RunWinRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         "pending.json", "--profile-json", "./pending.json", "--node-limit",
         "3500", "--max-depth", "48", "--memory-budget", "512"});
    const bool left = std::filesystem::exists(ws.root / "pending.json", ec);
    Check(rc == 2 && !left,
          "W1. Win32 solve rejects pending.json vs ./pending.json without leftovers",
          "rc=" + std::to_string(rc));
  }
  {
    const std::filesystem::path keep = ws.root / "existing.json";
    const std::string sentinel = "{\"keepWin32\":true}\n";
    WriteBytes(keep, sentinel);
    const int rc = RunWinRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         keep.string(), "--profile-json", (ws.root / "EXISTING.json").string(),
         "--node-limit", "3500"});
    std::string after;
    Check(rc == 2 && ReadBytes(keep, &after) && after == sentinel,
          "W2. Win32 solve rejects case-colliding existing file without truncating it",
          "rc=" + std::to_string(rc));
  }
  {
    const std::filesystem::path b1 = ws.root / "b1.json";
    WriteBytes(b1, p031_bytes);
    const std::filesystem::path man = ws.root / "m.json";
    WriteBytes(man, "[\"" + JsonEscapePath(b1.string()) + "\"]\n");
    const int rc = RunWinRaw(
        tprover_bin,
        {"bench", "--manifest", man.string(), "--out", b1.string(),
         "--node-limit", "3500"});
    std::string after;
    Check(rc == 2 && ReadBytes(b1, &after) && after == p031_bytes,
          "W3. Win32 bench rejects --out overwriting manifest member",
          "rc=" + std::to_string(rc));
  }
  {
    const std::filesystem::path proof_p = ws.root / "ok_proof.json";
    const std::filesystem::path prof_p = ws.root / "ok_prof.json";
    const int rc = RunWinRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         proof_p.string(), "--profile-json", prof_p.string(), "--node-limit",
         "3500", "--max-depth", "48", "--memory-budget", "512"});
    const int chk = RunWinRaw(
        tprover_bin,
        {"check", "--proof", proof_p.string(), "--problem", p042_src.string()});
    Check(rc == 0 && chk == 0,
          "W4. Win32 solve/check succeeds on separated outputs",
          "rc=" + std::to_string(rc) + " chk=" + std::to_string(chk));
  }
  std::filesystem::current_path(prev_cwd, ec);
  std::cout << "\n========================================\n"
            << "R25 Win32 CLI Summary: " << g_passed << "/" << g_total
            << " passed, " << g_failed << " failed.\n"
            << "========================================\n";
  return g_failed == 0 ? 0 : 1;
#else
  std::cout << "[SKIP] Unsupported non-POSIX/non-Win32 platform: returning CTest skip code 77.\n";
  return 77;
#endif
#else
  std::error_code ec;
  const std::filesystem::path tmp_base =
      std::filesystem::temp_directory_path(ec);
  TempWorkspaceGuard ws{tmp_base /
                        ("ldprover_cli_tests_" + std::to_string(::getpid()))};
  std::filesystem::remove_all(ws.root, ec);
  std::filesystem::create_directories(ws.root, ec);

  const bool case_insensitive = DetectCaseInsensitiveVolume(ws.root);
  std::cout << "[INFO] Workspace: " << ws.root
            << " (caseInsensitive=" << (case_insensitive ? "true" : "false")
            << ")\n";

  // 1. APFS case-insensitive brand-new outputs: --out-proof out.json --profile-json OUT.json
  {
    const std::filesystem::path dir = ws.root / "case_new";
    std::filesystem::create_directories(dir, ec);
    const std::string lower_p = (dir / "out.json").string();
    const std::string upper_p = (dir / "OUT.json").string();
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", lower_p,
         "--profile-json", upper_p, "--node-limit", "3500", "--max-depth",
         "48", "--memory-budget", "512"});
    if (case_insensitive) {
      const bool left_behind = std::filesystem::exists(dir / "out.json", ec) ||
                               std::filesystem::exists(dir / "OUT.json", ec);
      Check(r.exit_code == 2 && !left_behind &&
                r.stderr_str.find("Path conflict") != std::string::npos,
            "1. solve rejects case-colliding brand-new outputs without leaving artifacts",
            "rc=" + std::to_string(r.exit_code) +
                " left=" + (left_behind ? "true" : "false"));
    } else {
      Check(r.exit_code == 0,
            "1. solve allows distinct case outputs on case-sensitive filesystem",
            "rc=" + std::to_string(r.exit_code));
    }
  }

  // 2. APFS case-insensitive existing-file protection (pre-existing bytes intact)
  if (case_insensitive) {
    const std::filesystem::path dir = ws.root / "case_existing";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path existing = dir / "existing.json";
    const std::string sentinel = "{\"sentinel\":\"KEEP_ME_CASE_P1\"}\n";
    WriteBytes(existing, sentinel);
    const std::string upper_p = (dir / "EXISTING.json").string();
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         existing.string(), "--profile-json", upper_p, "--node-limit", "3500",
         "--max-depth", "48", "--memory-budget", "512"});
    std::string after;
    const bool read_ok = ReadBytes(existing, &after);
    Check(r.exit_code == 2 && read_ok && after == sentinel,
          "2. solve rejects case-colliding existing output without truncating it",
          "rc=" + std::to_string(r.exit_code) + " len=" +
              std::to_string(after.size()));
  } else {
    Check(true, "2. skipped (volume is case-sensitive)", "");
  }

  // Setup 2-level directory symlink: link -> dir1/dir2
  const std::filesystem::path sym_root = ws.root / "sym_alias";
  std::filesystem::create_directories(sym_root / "dir1" / "dir2", ec);
  std::filesystem::create_directory_symlink("dir1/dir2", sym_root / "link", ec);

  // 3. 2-level symlink `link/../new.json` vs `dir1/new.json` -> TRUE ALIAS, neither exists
  {
    const std::string raw_link = sym_root.string() + "/link/../new.json";
    const std::string raw_dir1 = sym_root.string() + "/dir1/new.json";
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", raw_link,
         "--profile-json", raw_dir1, "--node-limit", "3500", "--max-depth",
         "48", "--memory-budget", "512"});
    const bool left_behind =
        std::filesystem::exists(sym_root / "dir1" / "new.json", ec) ||
        std::filesystem::exists(sym_root / "new.json", ec);
    Check(r.exit_code == 2 && !left_behind &&
              r.stderr_str.find("Path conflict") != std::string::npos,
          "3. solve rejects 2-level symlink dir alias `link/../new.json` vs `dir1/new.json` with zero leftovers",
          "rc=" + std::to_string(r.exit_code) +
              " left=" + (left_behind ? "true" : "false"));
  }

  // 4. 2-level symlink `link/../sep.json` (=dir1/sep.json) vs `sep.json` (=parent/sep.json) -> DISTINCT FILES!
  {
    const std::string raw_link_out = sym_root.string() + "/link/../sep.json";
    const std::string raw_parent_prof = sym_root.string() + "/sep.json";
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", raw_link_out,
         "--profile-json", raw_parent_prof, "--node-limit", "3500",
         "--max-depth", "48", "--memory-budget", "512"});
    std::string proof_bytes;
    std::string prof_bytes;
    const bool both_read =
        ReadBytes(sym_root / "dir1" / "sep.json", &proof_bytes) &&
        ReadBytes(sym_root / "sep.json", &prof_bytes);
    const bool both_exist =
        std::filesystem::exists(sym_root / "dir1" / "sep.json", ec) &&
        std::filesystem::exists(sym_root / "sep.json", ec);
    const auto chk = RunCliRaw(
        tprover_bin,
        {"check", "--proof", (sym_root / "dir1" / "sep.json").string(),
         "--problem", p042_src.string()});
    const bool prof_valid =
        prof_bytes.find("\"exclusiveSearchMs\"") != std::string::npos &&
        proof_bytes.find("lproof/1") != std::string::npos;
    const bool chk_ok =
        chk.exit_code == 0 &&
        chk.stdout_str.find("\"passed\":true") != std::string::npos &&
        chk.stdout_str.find("\"verifiedScope\":\"original_root\"") !=
            std::string::npos &&
        chk.stdout_str.find("\"verifiedRootKind\":\"initial\"") !=
            std::string::npos;
    Check(r.exit_code == 0 && both_exist && both_read && prof_valid &&
              chk_ok,
          "4. solve allows distinct `link/../sep.json` vs parent `sep.json` and writes valid proof + profile",
          "rc=" + std::to_string(r.exit_code) + " chk=" +
              std::to_string(chk.exit_code) + " exist=" +
              std::to_string(both_exist) + " read=" +
              std::to_string(both_read) + " profValid=" +
              std::to_string(prof_valid) + " chkOut=" + chk.stdout_str);
  }

  // 5. Raw relative un-normalized `sub/../rel_same.json` vs `rel_same.json`
  {
    const std::filesystem::path dir = ws.root / "rel_dir";
    std::filesystem::create_directories(dir / "sub", ec);
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         "sub/../rel_same.json", "--profile-json", "rel_same.json",
         "--node-limit", "3500", "--max-depth", "48", "--memory-budget", "512"},
        dir.string());
    const bool left_behind =
        std::filesystem::exists(dir / "rel_same.json", ec);
    Check(r.exit_code == 2 && !left_behind,
          "5. solve rejects raw relative `sub/../rel_same.json` vs `rel_same.json` without leaving files",
          "rc=" + std::to_string(r.exit_code));
  }

  // 6. Dangling symlink aliasing preserves symlink and removes newly created target
  {
    const std::filesystem::path dir = ws.root / "dangling";
    std::filesystem::create_directories(dir / "sub", ec);
    const std::filesystem::path target = dir / "sub" / "target.json";
    const std::filesystem::path sym = dir / "dangling_proof.json";
    std::filesystem::create_symlink(target, sym, ec);
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", sym.string(),
         "--profile-json", target.string(), "--node-limit", "3500",
         "--max-depth", "48", "--memory-budget", "512"});
    const bool target_absent = !std::filesystem::exists(target, ec);
    const bool sym_still_symlink = std::filesystem::is_symlink(
        std::filesystem::symlink_status(sym, ec));
    Check(r.exit_code == 2 && target_absent && sym_still_symlink,
          "6. solve rejects dangling symlink vs target without deleting symlink or leaving target",
          "rc=" + std::to_string(r.exit_code) +
              " sym=" + (sym_still_symlink ? "yes" : "no"));
  }

  // 7. Hard-link & --problem protection
  {
    const std::filesystem::path dir = ws.root / "hardlink";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path prob_copy = dir / "p042_copy.json";
    const std::filesystem::path prob_hl = dir / "p042_hardlink.json";
    WriteBytes(prob_copy, p042_bytes);
    std::filesystem::create_hard_link(prob_copy, prob_hl, ec);
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", prob_copy.string(), "--out-proof",
         prob_hl.string(), "--node-limit", "3500", "--max-depth", "48",
         "--memory-budget", "512"});
    std::string after;
    const bool intact = ReadBytes(prob_copy, &after) && after == p042_bytes;
    Check(r.exit_code == 2 && intact,
          "7. solve rejects --out-proof hardlinked to --problem and preserves input bytes",
          "rc=" + std::to_string(r.exit_code));
  }

  // 8. Quoted + tab filename round-trip JSON escaping & verification
  {
    const std::filesystem::path dir = ws.root / "quoted";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path special_prob = dir / "角\"1\tprobe.json";
    const std::filesystem::path q_proof = dir / "q_proof.json";
    const std::filesystem::path q_prof = dir / "q_prof.json";
    WriteBytes(special_prob, p042_bytes);
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", special_prob.string(), "--out-proof",
         q_proof.string(), "--profile-json", q_prof.string(), "--node-limit",
         "3500", "--max-depth", "48", "--memory-budget", "512"});
    std::string prof_bytes;
    const bool has_prof = ReadBytes(q_prof, &prof_bytes);
    const std::string expected_id = "\"problemId\":\"角\\\"1\\tprobe\"";
    const std::string expected_id_pretty =
        "\"problemId\": \"角\\\"1\\tprobe\"";
    const auto chk = RunCliRaw(
        tprover_bin,
        {"check", "--proof", q_proof.string(), "--problem",
         special_prob.string()});
    Check(r.exit_code == 0 && has_prof &&
              r.stdout_str.find(expected_id) != std::string::npos &&
              prof_bytes.find(expected_id_pretty) != std::string::npos &&
              chk.exit_code == 0 &&
              chk.stdout_str.find("\"passed\":true") != std::string::npos,
          "8. solve escapes quote+tab problemId in stdout & profile JSON and check passes",
          "rc=" + std::to_string(r.exit_code) +
              " chk=" + std::to_string(chk.exit_code));
  }

  // Setup bench fixtures
  const std::filesystem::path bench_dir = ws.root / "bench";
  std::filesystem::create_directories(bench_dir / "d1" / "d2", ec);
  std::filesystem::create_directory_symlink("d1/d2", bench_dir / "blink", ec);
  const std::filesystem::path b1 = bench_dir / "b1.json";
  const std::filesystem::path b2 = bench_dir / "d1" / "b2.json";
  WriteBytes(b1, p031_bytes);
  WriteBytes(b2, p042_bytes);
  const std::filesystem::path b1_hl = bench_dir / "b1_hardlink.json";
  const std::filesystem::path b2_sym = bench_dir / "b2_sym.json";
  std::filesystem::create_hard_link(b1, b1_hl, ec);
  std::filesystem::create_symlink(b2, b2_sym, ec);

  const std::filesystem::path manifest = bench_dir / "manifest.json";
  const std::string manifest_body =
      "[\n  \"" + JsonEscapePath(b1.string()) + "\",\n  \"" +
      JsonEscapePath(b2.string()) + "\"\n]\n";
  WriteBytes(manifest, manifest_body);

  auto inputs_intact = [&]() -> bool {
    std::string s1, s2, sm;
    return ReadBytes(b1, &s1) && ReadBytes(b2, &s2) &&
           ReadBytes(manifest, &sm) && s1 == p031_bytes && s2 == p042_bytes &&
           sm == manifest_body;
  };

  // 9. bench --out targeting first manifest member
  {
    const auto r = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", b1.string(),
         "--node-limit", "3500"});
    Check(r.exit_code == 2 && inputs_intact(),
          "9. bench rejects --out targeting first manifest member without overwriting it",
          "rc=" + std::to_string(r.exit_code));
  }

  // 10. bench --out targeting second manifest member
  {
    const auto r = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", b2.string(),
         "--node-limit", "3500"});
    Check(r.exit_code == 2 && inputs_intact(),
          "10. bench rejects --out targeting second manifest member without overwriting it",
          "rc=" + std::to_string(r.exit_code));
  }

  // 11. bench --out targeting hardlink / symlink / blink/../b2.json / manifest
  {
    const std::string alias_b2_link = bench_dir.string() + "/blink/../b2.json";
    const auto r_hl = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", b1_hl.string(),
         "--node-limit", "3500"});
    const auto r_sym = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", b2_sym.string(),
         "--node-limit", "3500"});
    const auto r_lnk = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", alias_b2_link,
         "--node-limit", "3500"});
    const auto r_man = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", manifest.string(), "--out", manifest.string(),
         "--node-limit", "3500"});
    Check(r_hl.exit_code == 2 && r_sym.exit_code == 2 &&
              r_lnk.exit_code == 2 && r_man.exit_code == 2 && inputs_intact(),
          "11. bench rejects --out aliasing hardlink, symlink, symlink-`..`, or --manifest while preserving all files",
          "rc=" + std::to_string(r_hl.exit_code) + "/" +
              std::to_string(r_sym.exit_code) + "/" +
              std::to_string(r_lnk.exit_code) + "/" +
              std::to_string(r_man.exit_code));
  }

  // 12. bench manifest with duplicate problem entry + separate CSV succeeds
  {
    const std::filesystem::path dup_manifest = bench_dir / "dup_manifest.json";
    WriteBytes(dup_manifest, "[\n  \"" + JsonEscapePath(b1.string()) +
                                 "\",\n  \"" + JsonEscapePath(b1.string()) +
                                 "\"\n]\n");
    const std::filesystem::path out_csv = bench_dir / "results.csv";
    const auto r = RunCliRaw(
        tprover_bin,
        {"bench", "--manifest", dup_manifest.string(), "--out",
         out_csv.string(), "--node-limit", "3500"});
    std::string csv_bytes;
    const bool has_csv = ReadBytes(out_csv, &csv_bytes);
    size_t pass_rows = 0;
    size_t pos = 0;
    while ((pos = csv_bytes.find(",PASS\n", pos)) != std::string::npos) {
      ++pass_rows;
      pos += 6U;
    }
    Check(r.exit_code == 0 && has_csv && pass_rows == 2U && inputs_intact() &&
              r.stdout_str.find("\"provenAndVerified\":2") !=
                  std::string::npos,
          "12. bench allows duplicate manifest inputs when --out CSV is separate and writes valid CSV",
          "rc=" + std::to_string(r.exit_code) + " rows=" +
              std::to_string(pass_rows));
  }

  // 13. solve preserves pre-existing --out-proof when failing (parse/conflict)
  {
    const std::filesystem::path dir = ws.root / "preexisting_fail";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path keep_out = dir / "keep.json";
    const std::string sentinel = "{\"existingProof\":true}\n";
    WriteBytes(keep_out, sentinel);
    const std::filesystem::path bad_prob = dir / "bad.json";
    WriteBytes(bad_prob, "{invalid json");
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", bad_prob.string(), "--out-proof",
         keep_out.string()});
    std::string after;
    const bool intact = ReadBytes(keep_out, &after) && after == sentinel;
    Check(r.exit_code == 2 && intact,
          "13. solve preserves pre-existing --out-proof bytes when problem parsing fails",
          "rc=" + std::to_string(r.exit_code));
  }

  // 14. Portable `pending.json` vs `./pending.json` brand-new output alias
  {
    const std::filesystem::path dir = ws.root / "dot_pending";
    std::filesystem::create_directories(dir, ec);
    const auto r = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         "pending.json", "--profile-json", "./pending.json", "--node-limit",
         "3500", "--max-depth", "48", "--memory-budget", "512"},
        dir.string());
    const bool left_behind = std::filesystem::exists(dir / "pending.json", ec);
    Check(r.exit_code == 2 && !left_behind,
          "14. solve rejects brand-new `pending.json` vs `./pending.json` without leftovers",
          "rc=" + std::to_string(r.exit_code));
  }

  // 15. POSIX concurrent dual-writer safety (16 barrier-synchronized trials)
  if (!skip_concurrent) {
    const std::filesystem::path dir = ws.root / "concurrent_dual";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path bad_prob = dir / "bad.json";
    WriteBytes(bad_prob, "{invalid json");

    int trials_ok = 0;
    constexpr int kNumTrials = 16;
    std::string first_fail_detail;
    for (int trial = 0; trial < kNumTrials; ++trial) {
      const std::filesystem::path shared_out =
          dir / ("shared_" + std::to_string(trial) + ".json");
      int barrier_pipe[2] = {-1, -1};
      if (::pipe(barrier_pipe) != 0) {
        first_fail_detail = "pipe() failed";
        break;
      }

      auto spawn_with_barrier = [&](const std::vector<std::string>& args) -> pid_t {
        const pid_t cpid = ::fork();
        if (cpid == 0) {
          ::close(barrier_pipe[1]);
          char ch = 0;
          while (::read(barrier_pipe[0], &ch, 1) < 0) {}
          ::close(barrier_pipe[0]);
          const int devnull = ::open("/dev/null", O_WRONLY);
          if (devnull >= 0) {
            ::dup2(devnull, STDOUT_FILENO);
            ::dup2(devnull, STDERR_FILENO);
            ::close(devnull);
          }
          std::vector<std::string> storage;
          storage.reserve(1U + args.size());
          storage.push_back(tprover_bin);
          for (const std::string& a : args) storage.push_back(a);
          std::vector<char*> argv_ptrs;
          argv_ptrs.reserve(storage.size() + 1U);
          for (std::string& s : storage) argv_ptrs.push_back(s.data());
          argv_ptrs.push_back(nullptr);
          ::execv(tprover_bin.c_str(), argv_ptrs.data());
          ::_exit(127);
        }
        return cpid;
      };

      const std::vector<std::string> valid_args = {
          "solve", "--problem", p042_src.string(), "--out-proof",
          shared_out.string(), "--node-limit", "3500", "--max-depth", "48",
          "--memory-budget", "512"};
      const std::vector<std::string> fail_args =
          (trial % 2 == 0)
              ? std::vector<std::string>{
                    "solve", "--problem", p042_src.string(), "--out-proof",
                    shared_out.string(), "--profile-json", shared_out.string(),
                    "--node-limit", "3500", "--max-depth", "48",
                    "--memory-budget", "512"}
              : std::vector<std::string>{
                    "solve", "--problem", bad_prob.string(), "--out-proof",
                    shared_out.string()};

      // Alternate spawn order between trials
      pid_t pid_valid = -1;
      pid_t pid_fail = -1;
      if (trial % 2 == 0) {
        pid_fail = spawn_with_barrier(fail_args);
        pid_valid = spawn_with_barrier(valid_args);
      } else {
        pid_valid = spawn_with_barrier(valid_args);
        pid_fail = spawn_with_barrier(fail_args);
      }
      ::close(barrier_pipe[0]);
      ::close(barrier_pipe[1]);  // Release both children simultaneously!

      int st_valid = 0;
      int st_fail = 0;
      if (pid_valid > 0) ::waitpid(pid_valid, &st_valid, 0);
      if (pid_fail > 0) ::waitpid(pid_fail, &st_fail, 0);

      const int rc_valid = WIFEXITED(st_valid) ? WEXITSTATUS(st_valid) : -1;
      const int rc_fail = WIFEXITED(st_fail) ? WEXITSTATUS(st_fail) : -1;
      const bool exists_after = std::filesystem::exists(shared_out, ec);
      const auto chk = RunCliRaw(
          tprover_bin,
          {"check", "--proof", shared_out.string(), "--problem",
           p042_src.string()});
      const bool chk_ok =
          chk.exit_code == 0 &&
          chk.stdout_str.find("\"passed\":true") != std::string::npos;
      if (rc_valid == 0 && rc_fail == 2 && exists_after && chk_ok) {
        ++trials_ok;
      } else if (first_fail_detail.empty()) {
        first_fail_detail = "trial=" + std::to_string(trial) +
                            " validRc=" + std::to_string(rc_valid) +
                            " failRc=" + std::to_string(rc_fail) +
                            " exists=" + std::to_string(exists_after) +
                            " chk=" + std::to_string(chk.exit_code);
      }
    }
    Check(trials_ok == kNumTrials,
          "15. concurrent dual-writer stress (16x): failing peer rollback never deletes or corrupts valid peer proof",
          "passedTrials=" + std::to_string(trials_ok) + "/" +
              std::to_string(kNumTrials) + " " + first_fail_detail);
  }

  // 16. R25 P1 Fix: Volume-native Unicode NFC/NFD & Unicode case-folding É/é
  {
    const std::filesystem::path dir = ws.root / "unicode_equiv";
    std::filesystem::create_directories(dir / "dirA", ec);
    std::filesystem::create_directories(dir / "dirB", ec);

    auto probe_same = [&](const std::string& a, const std::string& b) -> bool {
      const std::string pa = (dir / a).string();
      const std::string pb = (dir / b).string();
      WriteBytes(pa, "probe");
      struct stat s1 {};
      struct stat s2 {};
      const bool eq = (::stat(pa.c_str(), &s1) == 0 &&
                       ::stat(pb.c_str(), &s2) == 0 &&
                       s1.st_dev == s2.st_dev && s1.st_ino == s2.st_ino);
      std::filesystem::remove(dir / a, ec);
      return eq;
    };
    const bool unicode_norm_equiv =
        probe_same("probe_\xC3\xA9.tmp", "probe_e\xCC\x81.tmp");
    const bool unicode_case_equiv =
        probe_same("probe_\xC3\x89.tmp", "probe_\xC3\xA9.tmp");

    // 16a: Same dir NFC proof_é.json vs NFD proof_é.json (brand-new)
    const std::string nfc_same = (dir / "proof_\xC3\xA9.json").string();
    const std::string nfd_same = (dir / "proof_e\xCC\x81.json").string();
    const auto r_norm = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", nfc_same,
         "--profile-json", nfd_same, "--node-limit", "3500", "--max-depth",
         "48", "--memory-budget", "512"});
    bool ok_norm = false;
    if (unicode_norm_equiv) {
      const bool left = std::filesystem::exists(nfc_same, ec) ||
                        std::filesystem::exists(nfd_same, ec);
      ok_norm = (r_norm.exit_code == 2 && !left &&
                 r_norm.stderr_str.find("Path conflict") != std::string::npos);
    } else {
      std::string p1, p2;
      ok_norm = (r_norm.exit_code == 0 && ReadBytes(nfc_same, &p1) &&
                 ReadBytes(nfd_same, &p2) &&
                 p1.find("lproof/1") != std::string::npos &&
                 p2.find("exclusiveSearchMs") != std::string::npos);
    }

    // 16b: Same dir Unicode case É vs é (brand-new)
    const std::string u_upper = (dir / "out_\xC3\x89.json").string();
    const std::string u_lower = (dir / "out_\xC3\xA9.json").string();
    const auto r_ucase = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", u_upper,
         "--profile-json", u_lower, "--node-limit", "3500", "--max-depth",
         "48", "--memory-budget", "512"});
    bool ok_ucase = false;
    if (unicode_case_equiv) {
      const bool left = std::filesystem::exists(u_upper, ec) ||
                        std::filesystem::exists(u_lower, ec);
      ok_ucase =
          (r_ucase.exit_code == 2 && !left &&
           r_ucase.stderr_str.find("Path conflict") != std::string::npos);
    } else {
      ok_ucase = (r_ucase.exit_code == 0);
    }

    // 16c: Different parent directories dirA/café.json (NFC) vs dirB/café.json (NFD)
    const std::string sep_a = (dir / "dirA" / "caf\xC3\xA9.json").string();
    const std::string sep_b = (dir / "dirB" / "cafe\xCC\x81.json").string();
    const auto r_sep = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", sep_a,
         "--profile-json", sep_b, "--node-limit", "3500", "--max-depth", "48",
         "--memory-budget", "512"});
    std::string sep_proof, sep_prof;
    const auto chk_sep = RunCliRaw(
        tprover_bin,
        {"check", "--proof", sep_a, "--problem", p042_src.string()});
    const bool ok_sep =
        (r_sep.exit_code == 0 && ReadBytes(sep_a, &sep_proof) &&
         ReadBytes(sep_b, &sep_prof) &&
         sep_proof.find("lproof/1") != std::string::npos &&
         sep_prof.find("exclusiveSearchMs") != std::string::npos &&
         chk_sep.exit_code == 0 &&
         chk_sep.stdout_str.find("\"passed\":true") != std::string::npos);

    // 16d: Truly distinct ASCII names alpha.json vs beta.json in same dir
    const std::string d_a = (dir / "alpha.json").string();
    const std::string d_b = (dir / "beta.json").string();
    const auto r_dist = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", d_a,
         "--profile-json", d_b, "--node-limit", "3500", "--max-depth", "48",
         "--memory-budget", "512"});

    Check(ok_norm && ok_ucase && ok_sep && r_dist.exit_code == 0,
          "16. volume-native Unicode NFC/NFD & case-folding check rejects collisions cleanly and permits distinct/cross-dir outputs",
          "norm=" + std::to_string(ok_norm) + "(" +
              std::to_string(unicode_norm_equiv) + ") ucase=" +
              std::to_string(ok_ucase) + "(" +
              std::to_string(unicode_case_equiv) + ") sep=" +
              std::to_string(ok_sep) + " distRc=" +
              std::to_string(r_dist.exit_code));
  }

  // 17. R25 P2 Fix: Overwriting existing file preserves mode (0600, 0640) and
  // brand-new outputs respect caller process umask (0077 -> 0600, 0022 -> 0644)
  {
    const std::filesystem::path dir = ws.root / "file_modes";
    std::filesystem::create_directories(dir, ec);

    auto get_mode = [&](const std::filesystem::path& p) -> int {
      struct stat st {};
      if (::stat(p.c_str(), &st) != 0) return -1;
      return static_cast<int>(st.st_mode & 0777);
    };

    // 17a: Existing 0600 under umask 0022 stays 0600
    const std::filesystem::path p600 = dir / "perm_0600.json";
    WriteBytes(p600, "{\"old\":true}\n");
    ::chmod(p600.c_str(), 0600);
    const auto r600 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", p600.string(),
         "--node-limit", "3500", "--max-depth", "48", "--memory-budget", "512"},
        "", 0022);
    const auto chk600 = RunCliRaw(
        tprover_bin,
        {"check", "--proof", p600.string(), "--problem", p042_src.string()});

    // 17b: Existing 0640 under umask 0022 stays 0640
    const std::filesystem::path p640 = dir / "perm_0640.json";
    WriteBytes(p640, "{\"old\":true}\n");
    ::chmod(p640.c_str(), 0640);
    const auto r640 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof", p640.string(),
         "--node-limit", "3500", "--max-depth", "48", "--memory-budget", "512"},
        "", 0022);

    // 17c: Brand-new files under umask 0077 (-> 0600) and umask 0022 (-> 0644)
    const std::filesystem::path pnew77 = dir / "new_0077.json";
    const auto rnew77 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         pnew77.string(), "--node-limit", "3500", "--max-depth", "48",
         "--memory-budget", "512"},
        "", 0077);
    const std::filesystem::path pnew22 = dir / "new_0022.json";
    const auto rnew22 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         pnew22.string(), "--node-limit", "3500", "--max-depth", "48",
         "--memory-budget", "512"},
        "", 0022);

    // 17d: Failing run targeting existing 0600 file preserves both bytes and 0600
    const std::filesystem::path pkeep = dir / "keep_fail_0600.json";
    const std::string sentinel = "{\"keepPerm\":600}\n";
    WriteBytes(pkeep, sentinel);
    ::chmod(pkeep.c_str(), 0600);
    const std::filesystem::path badp = dir / "bad.json";
    WriteBytes(badp, "{invalid");
    const auto rfail = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", badp.string(), "--out-proof", pkeep.string()},
        "", 0022);
    std::string keep_after;

    const int m600 = get_mode(p600);
    const int m640 = get_mode(p640);
    const int mn77 = get_mode(pnew77);
    const int mn22 = get_mode(pnew22);
    const int mkeep = get_mode(pkeep);
    Check(r600.exit_code == 0 && chk600.exit_code == 0 && m600 == 0600 &&
              r640.exit_code == 0 && m640 == 0640 && rnew77.exit_code == 0 &&
              mn77 == 0600 && rnew22.exit_code == 0 && mn22 == 0644 &&
              rfail.exit_code == 2 && ReadBytes(pkeep, &keep_after) &&
              keep_after == sentinel && mkeep == 0600,
          "17. output publishing preserves existing modes (0600/0640) and applies caller umask (0077/0022) to new files",
          "m600=" + std::to_string(m600) + " m640=" + std::to_string(m640) +
              " mn77=" + std::to_string(mn77) + " mn22=" +
              std::to_string(mn22) + " mkeep=" + std::to_string(mkeep));
  }

  // 18. R27 P2 Fix: CLI `--near-pn-continuation-calls` rejects 0 and honors 1
  {
    const std::filesystem::path dir = ws.root / "near_pn_calls";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path bad_out = dir / "zero_proof.json";
    const auto r_zero = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p031_src.string(), "--out-proof",
         bad_out.string(), "--node-limit", "120", "--max-depth", "48",
         "--memory-budget", "512", "--near-pn-continuation",
         "--near-pn-continuation-calls", "0"});
    const bool zero_left_file = std::filesystem::exists(bad_out, ec);

    const std::filesystem::path one_out = dir / "one_proof.json";
    const std::filesystem::path one_conv = dir / "one_conv.json";
    const auto r_one = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p031_src.string(), "--out-proof",
         one_out.string(), "--convergence-json", one_conv.string(),
         "--node-limit", "120", "--max-depth", "48", "--memory-budget", "512",
         "--near-pn-continuation", "--near-pn-continuation-calls", "1"});
    std::string conv_bytes;
    const bool has_conv = ReadBytes(one_conv, &conv_bytes);
    Check(r_zero.exit_code == 2 && !zero_left_file && r_one.exit_code == 0 &&
              has_conv &&
              conv_bytes.find("\"claimed\": true") != std::string::npos &&
              conv_bytes.find("\"extraCallsSpent\": 1") != std::string::npos,
          "18. CLI rejects --near-pn-continuation-calls 0 cleanly and caps budget=1 to extraCallsSpent=1 on p031@120",
          "zeroRc=" + std::to_string(r_zero.exit_code) +
              " oneRc=" + std::to_string(r_one.exit_code));
  }

  // 19. Task Card 1: CLI resource bounds (--time-limit-ms, --memory-budget-bytes, --original-root)
  {
    const std::filesystem::path dir = ws.root / "resource_bounds";
    std::filesystem::create_directories(dir, ec);
    const std::filesystem::path bad_tl_out = dir / "bad_tl.json";
    const std::filesystem::path bad_mb_out = dir / "bad_mb.json";
    const auto r_tl0 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         bad_tl_out.string(), "--time-limit-ms", "0"});
    const auto r_mb0 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         bad_mb_out.string(), "--memory-budget-bytes", "0"});

    const std::filesystem::path p42_out = dir / "p42.proof.json";
    const std::filesystem::path p42_prof = dir / "p42.prof.json";
    const auto r_p42 = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p042_src.string(), "--out-proof",
         p42_out.string(), "--profile-json", p42_prof.string(),
         "--node-limit", "3500", "--max-depth", "48", "--time-limit-ms",
         "30000", "--memory-budget-bytes", "1073741824"});
    const auto chk_orig = RunCliRaw(
        tprover_bin,
        {"check", "--proof", p42_out.string(), "--problem", p042_src.string(),
         "--original-root"});
    const auto chk_mutex = RunCliRaw(
        tprover_bin,
        {"check", "--proof", p42_out.string(), "--original-root",
         "--allow-subposition"});

    const std::filesystem::path p060_src = tsumego_dir / "chao_vol1_p060.json";
    const std::filesystem::path p60_out = dir / "p60_to.proof.json";
    const auto r_to = RunCliRaw(
        tprover_bin,
        {"solve", "--problem", p060_src.string(), "--out-proof",
         p60_out.string(), "--node-limit", "1000000", "--max-depth", "64",
         "--time-limit-ms", "25", "--memory-budget-bytes", "1073741824"});

    std::string p42_prof_bytes;
    const bool has_prof = ReadBytes(p42_prof, &p42_prof_bytes);
    Check(r_tl0.exit_code == 2 && !std::filesystem::exists(bad_tl_out, ec) &&
              r_mb0.exit_code == 2 && !std::filesystem::exists(bad_mb_out, ec) &&
              r_p42.exit_code == 0 && has_prof &&
              p42_prof_bytes.find("\"timeLimitMs\": 30000") !=
                  std::string::npos &&
              p42_prof_bytes.find("\"memoryBudgetBytes\": 1073741824") !=
                  std::string::npos &&
              chk_orig.exit_code == 0 &&
              chk_orig.stdout_str.find("\"passed\":true") != std::string::npos &&
              chk_mutex.exit_code == 2 && r_to.exit_code == 0 &&
              r_to.stdout_str.find("\"unknownReason\":\"timeout\"") !=
                  std::string::npos,
          "19. CLI enforces --time-limit-ms / --memory-budget-bytes > 0, --original-root check, and cooperative timeout",
          "tl0=" + std::to_string(r_tl0.exit_code) +
              " mb0=" + std::to_string(r_mb0.exit_code) +
              " chk=" + std::to_string(chk_orig.exit_code) +
              " to=" + std::to_string(r_to.exit_code));
  }

  std::cout << "\n========================================\n"
            << "R26 CLI Boundary Summary: " << g_passed << "/" << g_total
            << " passed, " << g_failed << " failed.\n"
            << "========================================\n";
  return g_failed == 0 ? 0 : 1;
#endif
}
