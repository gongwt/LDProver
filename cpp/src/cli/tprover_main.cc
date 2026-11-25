// Copyright 2026 LDProver Authors. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
//
// File: src/cli/tprover_main.cc
// Description: CLI entrypoint for LDProver (`tprover solve | check | bench`)
// conforming to FR-10.1..FR-10.3 and exit code contract (§6: 0=normal/UNKNOWN,
// 2=rejected/missing file/artifact/check failure, 3=internal error).

#include <algorithm>
#include <atomic>
#include <cctype>
#include <chrono>
#include <cmath>
#include <cstdint>
#include <cstdlib>
#include <filesystem>
#include <fstream>
#include <iomanip>
#include <iostream>
#include <optional>
#include <sstream>
#include <string>
#include <system_error>
#include <utility>
#include <vector>

#if defined(__APPLE__) || defined(__unix__)
#include <sys/resource.h>
#endif

#if (defined(__APPLE__) || defined(__unix__)) && \
    !defined(LDPROVER_FORCE_PORTABLE_RESERVATION_FALLBACK)
#include <cerrno>
#include <climits>
#include <cstring>
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>
#elif defined(_WIN32) && !defined(LDPROVER_FORCE_PORTABLE_RESERVATION_FALLBACK)
#ifndef WIN32_LEAN_AND_MEAN
#define WIN32_LEAN_AND_MEAN
#endif
#ifndef NOMINMAX
#define NOMINMAX
#endif
#include <windows.h>
#endif

#include "ldprover/core/position.h"
#include "ldprover/core/problem_parser.h"
#include "ldprover/proof/proof_checker.h"
#include "ldprover/search/dfpn_solver.h"

namespace {

bool ReadEntireFile(const std::string& path, std::string* out) {
  std::ifstream ifs(path, std::ios::in | std::ios::binary);
  if (!ifs.is_open()) return false;
  std::ostringstream ss;
  ss << ifs.rdbuf();
  if (ifs.bad()) return false;
  *out = ss.str();
  return true;
}

#if !((defined(__APPLE__) || defined(__unix__) || defined(_WIN32)) && \
      !defined(LDPROVER_FORCE_PORTABLE_RESERVATION_FALLBACK))
bool WriteEntireFile(const std::string& path, const std::string& content) {
  std::ofstream ofs(path, std::ios::out | std::ios::binary | std::ios::trunc);
  if (!ofs.is_open()) return false;
  ofs << content;
  return ofs.good();
}
#endif

std::string BasenameStem(const std::string& path) {
  const size_t slash = path.find_last_of("/\\");
  std::string name = (slash == std::string::npos) ? path : path.substr(slash + 1U);
  const size_t dot = name.find_last_of('.');
  if (dot != std::string::npos) name = name.substr(0U, dot);
  return name.empty() ? "problem" : name;
}

std::string EscapeJsonString(const std::string& s) {
  static constexpr char kHex[] = "0123456789abcdef";
  std::string out;
  out.reserve(s.size() + 8U);
  for (unsigned char c : s) {
    switch (c) {
      case '"':
        out.append("\\\"");
        break;
      case '\\':
        out.append("\\\\");
        break;
      case '\b':
        out.append("\\b");
        break;
      case '\f':
        out.append("\\f");
        break;
      case '\n':
        out.append("\\n");
        break;
      case '\r':
        out.append("\\r");
        break;
      case '\t':
        out.append("\\t");
        break;
      default:
        if (c < 0x20U) {
          out.append("\\u00");
          out.push_back(kHex[(c >> 4U) & 0x0FU]);
          out.push_back(kHex[c & 0x0FU]);
        } else {
          out.push_back(static_cast<char>(c));
        }
        break;
    }
  }
  return out;
}

#if (defined(__APPLE__) || defined(__unix__)) && \
    !defined(LDPROVER_FORCE_PORTABLE_RESERVATION_FALLBACK)

struct FileIdentity {
  dev_t dev = 0;
  ino_t ino = 0;
  bool operator==(const FileIdentity& other) const noexcept {
    return dev == other.dev && ino == other.ino;
  }
};

struct InputFileRecord {
  std::string label;
  std::string path;
  FileIdentity id{};
};

bool StatFileIdentity(const std::string& path, FileIdentity* out_id) {
  struct stat st {};
  if (::stat(path.c_str(), &st) != 0) return false;
  if (out_id != nullptr) {
    out_id->dev = st.st_dev;
    out_id->ino = st.st_ino;
  }
  return true;
}

std::pair<std::string, std::string> SplitDirAndBase(const std::string& raw) {
  const size_t pos = raw.find_last_of('/');
  if (pos == std::string::npos) return {".", raw};
  if (pos == 0U) return {"/", raw.substr(1U)};
  return {raw.substr(0U, pos), raw.substr(pos + 1U)};
}

bool RealPathPosix(const std::string& path, std::string* out_resolved) {
  char buf[PATH_MAX];
  if (::realpath(path.c_str(), buf) == nullptr) return false;
  *out_resolved = std::string(buf);
  return true;
}

bool ResolveOutputTargetPosix(const std::string& label,
                              const std::string& raw_path,
                              std::string* out_real_parent,
                              FileIdentity* out_parent_id,
                              std::string* out_base_name,
                              std::string* out_final_path,
                              bool* out_existed, FileIdentity* out_existing_id,
                              bool* out_is_regular, mode_t* out_existing_mode,
                              std::string* out_err) {
  std::string cur = raw_path;
  for (int hop = 0; hop < 40; ++hop) {
    struct stat lst {};
    if (::lstat(cur.c_str(), &lst) != 0) {
      if (errno == ENOENT) break;
      if (out_err != nullptr) {
        *out_err = "[LDProver] Cannot inspect output path (" + label +
                   "): '" + raw_path + "' (" + std::strerror(errno) + ").\n";
      }
      return false;
    }
    if (!S_ISLNK(lst.st_mode)) break;
    std::vector<char> link_buf(PATH_MAX + 1U, '\0');
    const ssize_t len =
        ::readlink(cur.c_str(), link_buf.data(), link_buf.size() - 1U);
    if (len < 0) {
      if (out_err != nullptr) {
        *out_err = "[LDProver] Cannot read symlink (" + label + "): '" +
                   raw_path + "' (" + std::strerror(errno) + ").\n";
      }
      return false;
    }
    link_buf[static_cast<size_t>(len)] = '\0';
    const std::string target(link_buf.data(), static_cast<size_t>(len));
    if (!target.empty() && target[0] == '/') {
      cur = target;
    } else {
      const auto [link_dir, unused_name] = SplitDirAndBase(cur);
      (void)unused_name;
      std::string real_link_dir;
      if (!RealPathPosix(link_dir, &real_link_dir)) {
        if (out_err != nullptr) {
          *out_err = "[LDProver] Cannot resolve symlink parent (" + label +
                     "): '" + raw_path + "' (" + std::strerror(errno) + ").\n";
        }
        return false;
      }
      cur = (real_link_dir == "/") ? ("/" + target)
                                   : (real_link_dir + "/" + target);
    }
    if (hop == 39) {
      if (out_err != nullptr) {
        *out_err = "[LDProver] Too many symbolic link levels (" + label +
                   "): '" + raw_path + "'.\n";
      }
      return false;
    }
  }

  const auto [dir_part, base_name] = SplitDirAndBase(cur);
  if (base_name.empty() || base_name == "." || base_name == "..") {
    if (out_err != nullptr) {
      *out_err = "[LDProver] Output path must name a file (" + label +
                 "): '" + raw_path + "'.\n";
    }
    return false;
  }

  std::string real_parent;
  if (!RealPathPosix(dir_part, &real_parent)) {
    if (out_err != nullptr) {
      *out_err = "[LDProver] Cannot resolve parent directory (" + label +
                 "): '" + raw_path + "' (" + std::strerror(errno) + ").\n";
    }
    return false;
  }
  struct stat st_parent {};
  if (::stat(real_parent.c_str(), &st_parent) != 0 ||
      !S_ISDIR(st_parent.st_mode)) {
    if (out_err != nullptr) {
      *out_err = "[LDProver] Parent path is not a directory (" + label +
                 "): '" + raw_path + "'.\n";
    }
    return false;
  }

  const std::string final_path = (real_parent == "/")
                                     ? ("/" + base_name)
                                     : (real_parent + "/" + base_name);
  struct stat st_target {};
  if (::stat(final_path.c_str(), &st_target) == 0) {
    if (S_ISDIR(st_target.st_mode)) {
      if (out_err != nullptr) {
        *out_err = "[LDProver] Output path is a directory (" + label +
                   "): '" + raw_path + "'.\n";
      }
      return false;
    }
    *out_existed = true;
    *out_existing_id = FileIdentity{st_target.st_dev, st_target.st_ino};
    *out_is_regular = S_ISREG(st_target.st_mode);
    *out_existing_mode =
        *out_is_regular ? static_cast<mode_t>(st_target.st_mode & 0777) : 0;
  } else if (errno == ENOENT) {
    *out_existed = false;
    *out_existing_id = FileIdentity{};
    *out_is_regular = true;
    *out_existing_mode = 0;
  } else {
    if (out_err != nullptr) {
      *out_err = "[LDProver] Cannot stat output target (" + label + "): '" +
                 raw_path + "' (" + std::strerror(errno) + ").\n";
    }
    return false;
  }

  *out_real_parent = real_parent;
  *out_parent_id = FileIdentity{st_parent.st_dev, st_parent.st_ino};
  *out_base_name = base_name;
  *out_final_path = final_path;
  return true;
}

class OutputReservationGuard {
 public:
  OutputReservationGuard() = default;
  OutputReservationGuard(const OutputReservationGuard&) = delete;
  OutputReservationGuard& operator=(const OutputReservationGuard&) = delete;
  ~OutputReservationGuard() {
    if (!committed_) Rollback();
  }

  bool Reserve(
      const std::vector<InputFileRecord>& inputs,
      const std::vector<std::pair<std::string, std::string>>& declared_outputs,
      std::string* out_err) {
    Rollback();
    committed_ = false;
    static std::atomic<uint64_t> tmp_seq{0ULL};

    for (const auto& [label, path] : declared_outputs) {
      if (path.empty()) continue;

      ReservedOutput rec;
      rec.label = label;
      rec.path = path;
      if (!ResolveOutputTargetPosix(label, path, &rec.real_parent,
                                    &rec.parent_id, &rec.base_name,
                                    &rec.final_target_path, &rec.existed,
                                    &rec.existing_id, &rec.is_regular,
                                    &rec.existing_mode, out_err)) {
        Rollback();
        return false;
      }

      for (const InputFileRecord& inp : inputs) {
        if (rec.existed && rec.existing_id == inp.id) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + inp.label + " ('" +
                       inp.path + "') and " + rec.label + " ('" + rec.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }

      for (const ReservedOutput& prev : reserved_) {
        if (rec.existed && prev.existed && rec.existing_id == prev.existing_id) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + prev.label + " ('" +
                       prev.path + "') and " + rec.label + " ('" + rec.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }

      reserved_.push_back(std::move(rec));
    }

    // Volume-native collision probe for non-existent outputs sharing the same
    // parent directory inode (catches NFC/NFD Unicode equivalence, Unicode
    // case-folding like É/é, ASCII case insensitivity, etc.).
    std::vector<bool> checked_parent(reserved_.size(), false);
    for (size_t i = 0; i < reserved_.size(); ++i) {
      if (reserved_[i].existed || checked_parent[i]) continue;
      checked_parent[i] = true;
      std::vector<size_t> group = {i};
      for (size_t j = i + 1U; j < reserved_.size(); ++j) {
        if (!reserved_[j].existed &&
            reserved_[j].parent_id == reserved_[i].parent_id) {
          checked_parent[j] = true;
          group.push_back(j);
        }
      }
      if (group.size() < 2U) continue;

      struct ProbeDirCleanup {
        std::string dir;
        std::vector<std::string> files;
        ~ProbeDirCleanup() {
          for (const std::string& f : files) ::unlink(f.c_str());
          if (!dir.empty()) ::rmdir(dir.c_str());
        }
      } probe_cleanup;

      std::string tmpl = (reserved_[i].real_parent == "/")
                             ? "/.ldprover.probe.XXXXXX"
                             : (reserved_[i].real_parent +
                                "/.ldprover.probe.XXXXXX");
      std::vector<char> tmpl_buf(tmpl.begin(), tmpl.end());
      tmpl_buf.push_back('\0');
      char* created_dir = ::mkdtemp(tmpl_buf.data());
      if (created_dir == nullptr) {
        if (out_err != nullptr) {
          *out_err = "[LDProver] Cannot create name-probe directory in '" +
                     reserved_[i].real_parent + "' (" + std::strerror(errno) +
                     ").\n";
        }
        Rollback();
        return false;
      }
      probe_cleanup.dir = created_dir;

      struct ProbeRecord {
        size_t reserved_idx;
        FileIdentity id;
      };
      std::vector<ProbeRecord> probed;
      for (size_t idx : group) {
        const std::string probe_path =
            probe_cleanup.dir + "/" + reserved_[idx].base_name;
        const int pfd =
            ::open(probe_path.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0600);
        if (pfd >= 0) {
          struct stat st_p {};
          if (::fstat(pfd, &st_p) != 0) {
            const int saved = errno;
            ::close(pfd);
            probe_cleanup.files.push_back(probe_path);
            if (out_err != nullptr) {
              *out_err = "[LDProver] Cannot stat probe file (" +
                         reserved_[idx].label + "): (" +
                         std::strerror(saved) + ").\n";
            }
            Rollback();
            return false;
          }
          ::close(pfd);
          probe_cleanup.files.push_back(probe_path);
          probed.push_back(
              {idx, FileIdentity{st_p.st_dev, st_p.st_ino}});
          continue;
        }
        if (errno == EEXIST) {
          size_t conflict_prev_idx = group[0];
          struct stat st_ex {};
          if (::stat(probe_path.c_str(), &st_ex) == 0) {
            const FileIdentity ex_id{st_ex.st_dev, st_ex.st_ino};
            for (const ProbeRecord& pr : probed) {
              if (pr.id == ex_id) {
                conflict_prev_idx = pr.reserved_idx;
                break;
              }
            }
          }
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " +
                       reserved_[conflict_prev_idx].label + " ('" +
                       reserved_[conflict_prev_idx].path + "') and " +
                       reserved_[idx].label + " ('" + reserved_[idx].path +
                       "') resolve to the same file on target volume.\n";
          }
          Rollback();
          return false;
        }
        if (out_err != nullptr) {
          *out_err = "[LDProver] Cannot probe output name (" +
                     reserved_[idx].label + "): '" + reserved_[idx].path +
                     "' (" + std::strerror(errno) + ").\n";
        }
        Rollback();
        return false;
      }
    }

    // Create private 0600 per-invocation staging files (or open special device).
    for (ReservedOutput& rec : reserved_) {
      if (rec.is_regular) {
        // Atomic O_CREAT | O_EXCL ownership on per-invocation staging file (0600).
        for (int attempt = 0; attempt < 16; ++attempt) {
          const uint64_t seq =
              tmp_seq.fetch_add(1ULL, std::memory_order_relaxed);
          const std::string cand =
              (rec.real_parent == "/")
                  ? ("/.ldprover.tmp." + std::to_string(::getpid()) + "." +
                     std::to_string(seq))
                  : (rec.real_parent + "/.ldprover.tmp." +
                     std::to_string(::getpid()) + "." + std::to_string(seq));
          const int fd =
              ::open(cand.c_str(), O_WRONLY | O_CREAT | O_EXCL, 0600);
          if (fd >= 0) {
            struct stat st_tmp {};
            if (::fstat(fd, &st_tmp) != 0) {
              const int saved = errno;
              ::close(fd);
              ::unlink(cand.c_str());
              if (out_err != nullptr) {
                *out_err = "[LDProver] Cannot stat staging file (" + rec.label +
                           "): '" + cand + "' (" + std::strerror(saved) +
                           ").\n";
              }
              Rollback();
              return false;
            }
            rec.fd = fd;
            rec.staged = true;
            rec.tmp_path = cand;
            rec.tmp_id = FileIdentity{st_tmp.st_dev, st_tmp.st_ino};
            break;
          }
          if (errno != EEXIST) {
            if (out_err != nullptr) {
              *out_err = "[LDProver] Cannot create staging file (" + rec.label +
                         "): '" + cand + "' (" + std::strerror(errno) + ").\n";
            }
            Rollback();
            return false;
          }
        }
        if (rec.fd < 0) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Exhausted staging attempts (" + rec.label +
                       ").\n";
          }
          Rollback();
          return false;
        }
      } else {
        const int fd = ::open(rec.final_target_path.c_str(), O_WRONLY, 0);
        if (fd < 0) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Cannot open special output file (" +
                       rec.label + "): '" + rec.path + "' (" +
                       std::strerror(errno) + ").\n";
          }
          Rollback();
          return false;
        }
        rec.fd = fd;
      }
    }
    return true;
  }

  bool WriteOutput(const std::string& label, const std::string& content) {
    for (ReservedOutput& rec : reserved_) {
      if (rec.label != label) continue;
      if (rec.fd < 0) return false;
      if (rec.staged) {
        if (::lseek(rec.fd, 0, SEEK_SET) < 0) return false;
        if (::ftruncate(rec.fd, 0) != 0) return false;
      }
      size_t written = 0U;
      while (written < content.size()) {
        const ssize_t n = ::write(rec.fd, content.data() + written,
                                  content.size() - written);
        if (n < 0) {
          if (errno == EINTR) continue;
          return false;
        }
        written += static_cast<size_t>(n);
      }
      rec.has_written = true;
      rec.bytes_written_by_us = static_cast<uint64_t>(content.size());
      return true;
    }
    return false;
  }

  bool Commit() {
    std::optional<mode_t> cached_new_file_mode;
    for (ReservedOutput& rec : reserved_) {
      if (rec.staged && rec.has_written && rec.fd >= 0) {
        mode_t target_mode = 0644;
        if (rec.existed && rec.is_regular) {
          target_mode = rec.existing_mode;
        } else {
          if (!cached_new_file_mode.has_value()) {
            const mode_t cur_umask = ::umask(0);
            ::umask(cur_umask);
            cached_new_file_mode = static_cast<mode_t>(0666 & ~cur_umask);
          }
          target_mode = *cached_new_file_mode;
        }
        if (::fchmod(rec.fd, target_mode) != 0) {
          Rollback();
          return false;
        }
      }
      if (rec.fd >= 0) {
        if (::close(rec.fd) != 0) {
          rec.fd = -1;
          Rollback();
          return false;
        }
        rec.fd = -1;
      }
      if (rec.staged) {
        if (rec.has_written) {
          if (::rename(rec.tmp_path.c_str(), rec.final_target_path.c_str()) !=
              0) {
            Rollback();
            return false;
          }
          rec.staged = false;
          rec.tmp_path.clear();
        } else {
          struct stat st_now {};
          if (::lstat(rec.tmp_path.c_str(), &st_now) == 0 &&
              !S_ISLNK(st_now.st_mode) &&
              FileIdentity{st_now.st_dev, st_now.st_ino} == rec.tmp_id &&
              static_cast<uint64_t>(st_now.st_size) ==
                  rec.bytes_written_by_us) {
            ::unlink(rec.tmp_path.c_str());
          }
          rec.staged = false;
          rec.tmp_path.clear();
        }
      }
    }
    reserved_.clear();
    committed_ = true;
    return true;
  }

  void Rollback() {
    for (ReservedOutput& rec : reserved_) {
      if (rec.staged && !rec.tmp_path.empty()) {
        struct stat st_now {};
        if (::lstat(rec.tmp_path.c_str(), &st_now) == 0 &&
            !S_ISLNK(st_now.st_mode) &&
            FileIdentity{st_now.st_dev, st_now.st_ino} == rec.tmp_id &&
            static_cast<uint64_t>(st_now.st_size) == rec.bytes_written_by_us) {
          ::unlink(rec.tmp_path.c_str());
        }
        rec.staged = false;
        rec.tmp_path.clear();
      }
    }
    for (ReservedOutput& rec : reserved_) {
      if (rec.fd >= 0) {
        ::close(rec.fd);
        rec.fd = -1;
      }
    }
    reserved_.clear();
  }

 private:
  struct ReservedOutput {
    std::string label;
    std::string path;
    std::string real_parent;
    FileIdentity parent_id{};
    std::string base_name;
    std::string final_target_path;
    bool existed = false;
    FileIdentity existing_id{};
    bool is_regular = true;
    mode_t existing_mode = 0;
    bool staged = false;
    std::string tmp_path;
    FileIdentity tmp_id{};
    int fd = -1;
    bool has_written = false;
    uint64_t bytes_written_by_us = 0ULL;
  };

  std::vector<ReservedOutput> reserved_;
  bool committed_ = false;
};

#elif defined(_WIN32) && !defined(LDPROVER_FORCE_PORTABLE_RESERVATION_FALLBACK)

struct FileIdentity {
  DWORD volume_serial = 0;
  DWORD index_high = 0;
  DWORD index_low = 0;
  bool operator==(const FileIdentity& other) const noexcept {
    return volume_serial == other.volume_serial &&
           index_high == other.index_high && index_low == other.index_low;
  }
};

struct InputFileRecord {
  std::string label;
  std::string path;
  FileIdentity id{};
};

bool StatFileIdentity(const std::string& path, FileIdentity* out_id) {
  HANDLE h = CreateFileA(
      path.c_str(), 0,
      FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, nullptr,
      OPEN_EXISTING, FILE_FLAG_BACKUP_SEMANTICS, nullptr);
  if (h == INVALID_HANDLE_VALUE) return false;
  BY_HANDLE_FILE_INFORMATION info{};
  const BOOL ok = GetFileInformationByHandle(h, &info);
  CloseHandle(h);
  if (!ok) return false;
  if (out_id != nullptr) {
    out_id->volume_serial = info.dwVolumeSerialNumber;
    out_id->index_high = info.nFileIndexHigh;
    out_id->index_low = info.nFileIndexLow;
  }
  return true;
}

class OutputReservationGuard {
 public:
  OutputReservationGuard() = default;
  OutputReservationGuard(const OutputReservationGuard&) = delete;
  OutputReservationGuard& operator=(const OutputReservationGuard&) = delete;
  ~OutputReservationGuard() {
    if (!committed_) Rollback();
  }

  bool Reserve(
      const std::vector<InputFileRecord>& inputs,
      const std::vector<std::pair<std::string, std::string>>& declared_outputs,
      std::string* out_err) {
    Rollback();
    committed_ = false;
    for (const auto& [label, path] : declared_outputs) {
      if (path.empty()) continue;
      SetLastError(0);
      HANDLE h = CreateFileA(
          path.c_str(), GENERIC_WRITE,
          FILE_SHARE_READ | FILE_SHARE_WRITE | FILE_SHARE_DELETE, nullptr,
          OPEN_ALWAYS, FILE_ATTRIBUTE_NORMAL, nullptr);
      if (h == INVALID_HANDLE_VALUE) {
        if (out_err != nullptr) {
          *out_err = "[LDProver] Cannot open output file (" + label + "): '" +
                     path + "'.\n";
        }
        Rollback();
        return false;
      }
      const bool created_by_us = (GetLastError() != ERROR_ALREADY_EXISTS);
      BY_HANDLE_FILE_INFORMATION info{};
      if (!GetFileInformationByHandle(h, &info)) {
        CloseHandle(h);
        if (out_err != nullptr) {
          *out_err = "[LDProver] Cannot stat output file (" + label + "): '" +
                     path + "'.\n";
        }
        Rollback();
        return false;
      }

      ReservedOutput rec;
      rec.label = label;
      rec.path = path;
      rec.handle = h;
      rec.id = FileIdentity{info.dwVolumeSerialNumber, info.nFileIndexHigh,
                            info.nFileIndexLow};
      rec.created_by_us = created_by_us;
      reserved_.push_back(std::move(rec));
      const ReservedOutput& cur = reserved_.back();

      for (const InputFileRecord& inp : inputs) {
        if (cur.id == inp.id) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + inp.label + " ('" +
                       inp.path + "') and " + cur.label + " ('" + cur.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }
      for (size_t i = 0; i + 1U < reserved_.size(); ++i) {
        const ReservedOutput& prev = reserved_[i];
        if (cur.id == prev.id) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + prev.label + " ('" +
                       prev.path + "') and " + cur.label + " ('" + cur.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }
    }
    return true;
  }

  bool WriteOutput(const std::string& label, const std::string& content) {
    for (ReservedOutput& rec : reserved_) {
      if (rec.label != label) continue;
      if (rec.handle == INVALID_HANDLE_VALUE) return false;
      LARGE_INTEGER zero{};
      if (!SetFilePointerEx(rec.handle, zero, nullptr, FILE_BEGIN)) {
        return false;
      }
      if (!SetEndOfFile(rec.handle)) return false;
      size_t written = 0U;
      while (written < content.size()) {
        const DWORD chunk = static_cast<DWORD>(
            std::min<size_t>(content.size() - written, 1U << 20U));
        DWORD out_bytes = 0;
        if (!WriteFile(rec.handle, content.data() + written, chunk, &out_bytes,
                       nullptr)) {
          return false;
        }
        written += static_cast<size_t>(out_bytes);
      }
      rec.bytes_written_by_us = static_cast<uint64_t>(content.size());
      return true;
    }
    return false;
  }

  bool Commit() {
    for (ReservedOutput& rec : reserved_) {
      if (rec.handle != INVALID_HANDLE_VALUE) {
        CloseHandle(rec.handle);
        rec.handle = INVALID_HANDLE_VALUE;
      }
    }
    reserved_.clear();
    committed_ = true;
    return true;
  }

  void Rollback() {
    std::vector<ReservedOutput> copy = std::move(reserved_);
    reserved_.clear();
    for (ReservedOutput& rec : copy) {
      if (rec.handle != INVALID_HANDLE_VALUE) {
        LARGE_INTEGER fsz{};
        const bool size_ok =
            rec.created_by_us && GetFileSizeEx(rec.handle, &fsz) &&
            static_cast<uint64_t>(fsz.QuadPart) == rec.bytes_written_by_us;
        CloseHandle(rec.handle);
        rec.handle = INVALID_HANDLE_VALUE;
        if (size_ok) {
          DeleteFileA(rec.path.c_str());
        }
      }
    }
  }

 private:
  struct ReservedOutput {
    std::string label;
    std::string path;
    HANDLE handle = INVALID_HANDLE_VALUE;
    FileIdentity id{};
    bool created_by_us = false;
    uint64_t bytes_written_by_us = 0ULL;
  };

  std::vector<ReservedOutput> reserved_;
  bool committed_ = false;
};

#else

struct FileIdentity {};

struct InputFileRecord {
  std::string label;
  std::string path;
  FileIdentity id{};
};

bool StatFileIdentity(const std::string& path, FileIdentity* = nullptr) {
  std::error_code ec;
  return std::filesystem::exists(std::filesystem::path(path), ec) && !ec;
}

class OutputReservationGuard {
 public:
  OutputReservationGuard() = default;
  OutputReservationGuard(const OutputReservationGuard&) = delete;
  OutputReservationGuard& operator=(const OutputReservationGuard&) = delete;
  ~OutputReservationGuard() {
    if (!committed_) Rollback();
  }

  bool Reserve(
      const std::vector<InputFileRecord>& inputs,
      const std::vector<std::pair<std::string, std::string>>& declared_outputs,
      std::string* out_err) {
    Rollback();
    committed_ = false;
    std::error_code ec;

    for (const auto& [label, path] : declared_outputs) {
      if (path.empty()) continue;
      const std::filesystem::path p(path);
      const bool existed_before = std::filesystem::exists(p, ec) && !ec;
      if (existed_before && std::filesystem::is_directory(p, ec)) {
        if (out_err != nullptr) {
          *out_err = "[LDProver] Output path is a directory (" + label +
                     "): '" + path + "'.\n";
        }
        Rollback();
        return false;
      }
      const bool was_dangling_symlink =
          (!existed_before &&
           std::filesystem::is_symlink(
               std::filesystem::symlink_status(p, ec)) &&
           !ec);

      // Non-truncating creation ensures destination now exists on disk so
      // filesystem::equivalent checks kernel-resolved identity uniformly.
      {
        std::ofstream probe(p, std::ios::out | std::ios::binary | std::ios::app);
        if (!probe.is_open()) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Cannot open output file (" + label +
                       "): '" + path + "'.\n";
          }
          Rollback();
          return false;
        }
      }

      ReservedOutput rec;
      rec.label = label;
      rec.path = path;
      rec.created_by_us = !existed_before;
      if (rec.created_by_us) {
        const std::filesystem::path canon = std::filesystem::canonical(p, ec);
        if (!ec && !canon.empty()) {
          rec.unlink_path = canon.string();
        } else if (!was_dangling_symlink) {
          rec.unlink_path = path;
        }
      }
      reserved_.push_back(std::move(rec));
      const ReservedOutput& cur = reserved_.back();

      for (const InputFileRecord& inp : inputs) {
        std::error_code eq_ec;
        if (std::filesystem::equivalent(p, std::filesystem::path(inp.path),
                                        eq_ec) &&
            !eq_ec) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + inp.label + " ('" +
                       inp.path + "') and " + cur.label + " ('" + cur.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }

      for (size_t i = 0; i + 1U < reserved_.size(); ++i) {
        const ReservedOutput& prev = reserved_[i];
        std::error_code eq_ec;
        if (std::filesystem::equivalent(p, std::filesystem::path(prev.path),
                                        eq_ec) &&
            !eq_ec) {
          if (out_err != nullptr) {
            *out_err = "[LDProver] Path conflict: " + prev.label + " ('" +
                       prev.path + "') and " + cur.label + " ('" + cur.path +
                       "') resolve to the same file.\n";
          }
          Rollback();
          return false;
        }
      }
    }
    return true;
  }

  bool WriteOutput(const std::string& label, const std::string& content) {
    for (ReservedOutput& rec : reserved_) {
      if (rec.label != label) continue;
      if (!WriteEntireFile(rec.path, content)) return false;
      rec.bytes_written_by_us = static_cast<uint64_t>(content.size());
      return true;
    }
    return false;
  }

  bool Commit() {
    reserved_.clear();
    committed_ = true;
    return true;
  }

  void Rollback() {
    std::error_code ec;
    for (const ReservedOutput& rec : reserved_) {
      if (rec.created_by_us && !rec.unlink_path.empty()) {
        const std::filesystem::path up(rec.unlink_path);
        const uintmax_t fsz = std::filesystem::file_size(up, ec);
        if (!ec && static_cast<uint64_t>(fsz) == rec.bytes_written_by_us) {
          std::filesystem::remove(up, ec);
        }
      }
    }
    reserved_.clear();
  }

 private:
  struct ReservedOutput {
    std::string label;
    std::string path;
    bool created_by_us = false;
    std::string unlink_path;
    uint64_t bytes_written_by_us = 0ULL;
  };

  std::vector<ReservedOutput> reserved_;
  bool committed_ = false;
};

#endif

int DetectBoardSizeFromProofJson(const std::string& json_text) {
  const std::string key = "\"boardSize\"";
  const size_t pos = json_text.find(key);
  if (pos == std::string::npos) return 19;
  size_t cur = pos + key.size();
  while (cur < json_text.size() &&
         (std::isspace(static_cast<unsigned char>(json_text[cur])) ||
          json_text[cur] == ':')) {
    ++cur;
  }
  int val = 0;
  while (cur < json_text.size() &&
         std::isdigit(static_cast<unsigned char>(json_text[cur]))) {
    val = val * 10 + static_cast<int>(json_text[cur] - '0');
    ++cur;
  }
  return (val == 5 || val == 7 || val == 19) ? val : -1;
}

std::vector<std::string> ParseJsonStringArray(const std::string& json_text) {
  std::vector<std::string> items;
  size_t cur = 0;
  while (cur < json_text.size() && json_text[cur] != '[') ++cur;
  if (cur >= json_text.size()) return items;
  ++cur;
  while (cur < json_text.size()) {
    while (cur < json_text.size() &&
           (std::isspace(static_cast<unsigned char>(json_text[cur])) ||
            json_text[cur] == ',')) {
      ++cur;
    }
    if (cur >= json_text.size() || json_text[cur] == ']') break;
    if (json_text[cur] != '"') return {};
    ++cur;
    std::string s;
    while (cur < json_text.size() && json_text[cur] != '"') {
      if (json_text[cur] == '\\' && cur + 1U < json_text.size()) {
        ++cur;
      }
      s.push_back(json_text[cur++]);
    }
    if (cur >= json_text.size() || json_text[cur] != '"') return {};
    ++cur;
    items.push_back(s);
  }
  return items;
}

std::string OutcomeLabel(ldprover::ProofOutcome outcome) {
  if (outcome == ldprover::ProofOutcome::kProvenWin) return "PROVEN_WIN";
  if (outcome == ldprover::ProofOutcome::kProvenLoss) return "PROVEN_LOSS";
  return "UNKNOWN";
}

std::string EvidenceKindLabel(ldprover::EvidenceKind kind) {
  switch (kind) {
    case ldprover::EvidenceKind::kBensonUca:
      return "BENSON_UCA";
    case ldprover::EvidenceKind::kTokensCaptured:
      return "TOKENS_CAPTURED";
    case ldprover::EvidenceKind::kDoublePassResolution:
      return "DOUBLE_PASS_RESOLUTION";
    case ldprover::EvidenceKind::kEmptyTargetConstantFalse:
      return "EMPTY_TARGET_CONSTANT_FALSE";
    case ldprover::EvidenceKind::kNone:
    default:
      return "NONE";
  }
}

std::vector<std::string> ParseCsvListPreserveEmpty(const std::string& raw) {
  std::vector<std::string> items;
  size_t start = 0;
  while (start <= raw.size()) {
    const size_t comma = raw.find(',', start);
    if (comma == std::string::npos) {
      items.push_back(raw.substr(start));
      break;
    }
    items.push_back(raw.substr(start, comma - start));
    start = comma + 1U;
  }
  return items;
}

std::string UnknownReasonLabel(ldprover::UnknownReason reason) {
  switch (reason) {
    case ldprover::UnknownReason::kNone:
      return "none";
    case ldprover::UnknownReason::kTimeout:
      return "timeout";
    case ldprover::UnknownReason::kKoDependent:
      return "ko_dependent";
    case ldprover::UnknownReason::kCycle:
      return "cycle";
    case ldprover::UnknownReason::kNodeLimit:
      return "node_limit";
    case ldprover::UnknownReason::kDepthLimit:
      return "depth_limit";
    case ldprover::UnknownReason::kMemoryBudget:
      return "memory_budget";
    case ldprover::UnknownReason::kWideningStalled:
      return "widening_stalled";
    case ldprover::UnknownReason::kInternalError:
      return "internal_error";
  }
  return "none";
}

bool ParseStrictPositiveDouble(const char* raw, double* out_val) {
  if (raw == nullptr || *raw == '\0') return false;
  char* endptr = nullptr;
  const double v = std::strtod(raw, &endptr);
  if (endptr == raw || *endptr != '\0') return false;
  if (!std::isfinite(v) || v <= 0.0) return false;
  *out_val = v;
  return true;
}

bool ParseStrictPositiveU32(const char* raw, uint32_t* out_val) {
  if (raw == nullptr || *raw == '\0' || raw[0] == '-') return false;
  char* endptr = nullptr;
  const unsigned long v = std::strtoul(raw, &endptr, 10);
  if (endptr == raw || *endptr != '\0' || v == 0UL || v > 0xFFFFFFFFUL) {
    return false;
  }
  *out_val = static_cast<uint32_t>(v);
  return true;
}

int RunSolveCommand(int argc, char* argv[]) {
  using SteadyClock = std::chrono::steady_clock;
  const auto cli_t0 = SteadyClock::now();

  std::string problem_path;
  std::string out_proof_path;
  std::string out_sgf_path;
  std::string out_profile_path;
  std::string out_convergence_path;
  ldprover::SolverConfig config;

  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--problem" && i + 1 < argc) {
      problem_path = argv[++i];
    } else if (arg == "--out-proof" && i + 1 < argc) {
      out_proof_path = argv[++i];
    } else if (arg == "--out-sgf" && i + 1 < argc) {
      out_sgf_path = argv[++i];
    } else if (arg == "--profile-json" && i + 1 < argc) {
      out_profile_path = argv[++i];
      config.enable_stage_profiling = true;
    } else if (arg == "--convergence-json" && i + 1 < argc) {
      out_convergence_path = argv[++i];
      config.enable_convergence_trace = true;
    } else if (arg == "--observe-paths" && i + 1 < argc) {
      config.observed_paths = ParseCsvListPreserveEmpty(argv[++i]);
    } else if (arg == "--mode" && i + 1 < argc) {
      const std::string mode = argv[++i];
      if (mode == "board-tt") {
        config.enable_pattern_tt = false;
      } else if (mode == "pattern-tt") {
        config.enable_pattern_tt = true;
      } else {
        std::cerr << "[LDProver] Invalid --mode: " << mode << "\n";
        return 2;
      }
    } else if (arg == "--node-limit" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.max_nodes)) {
        std::cerr << "[LDProver] Invalid positive integer for --node-limit\n";
        return 2;
      }
    } else if (arg == "--max-depth" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.max_depth)) {
        std::cerr << "[LDProver] Invalid positive integer for --max-depth\n";
        return 2;
      }
    } else if (arg == "--widening-base-k" && i + 1 < argc) {
      if (!ParseStrictPositiveU32(argv[++i], &config.widening_base_k)) {
        std::cerr
            << "[LDProver] Invalid positive integer for --widening-base-k\n";
        return 2;
      }
    } else if (arg == "--memory-budget" && i + 1 < argc) {
      double mb = 0.0;
      if (!ParseStrictPositiveDouble(argv[++i], &mb)) {
        std::cerr << "[LDProver] Invalid positive number (MiB) for "
                     "--memory-budget\n";
        return 2;
      }
      const double bytes_d = std::floor(mb * 1024.0 * 1024.0);
      config.memory_budget_bytes =
          (bytes_d < 1.0) ? 1ULL : static_cast<uint64_t>(bytes_d);
    } else {
      std::cerr << "[LDProver] Unknown or incomplete solve option: " << arg
                << "\n";
      return 2;
    }
  }

  if (problem_path.empty()) {
    std::cerr << "[LDProver] Missing required --problem <file.json>\n";
    return 2;
  }

  std::string raw_json;
  if (!ReadEntireFile(problem_path, &raw_json)) {
    std::cerr << "[LDProver] Cannot read problem file: " << problem_path << "\n";
    return 2;
  }

  FileIdentity problem_id{};
  if (!StatFileIdentity(problem_path, &problem_id)) {
    std::cerr << "[LDProver] Cannot stat problem file: " << problem_path << "\n";
    return 2;
  }

  OutputReservationGuard out_guard;
  std::string conflict_err;
  if (!out_guard.Reserve(
          {{"--problem", problem_path, problem_id}},
          {{"--out-proof", out_proof_path},
           {"--out-sgf", out_sgf_path},
           {"--profile-json", out_profile_path},
           {"--convergence-json", out_convergence_path}},
          &conflict_err)) {
    std::cerr << conflict_err;
    return 2;
  }

  ldprover::ProblemContractParser<19> parser;
  const std::string prob_id = BasenameStem(problem_path);
  const auto parsed = parser.ParseTsumegoJsonObject(prob_id, raw_json);
  const auto parse_t1 = SteadyClock::now();
  if (!parsed.valid) {
    std::cerr << "{\"problemId\":\"" << EscapeJsonString(prob_id)
              << "\",\"valid\":false,"
              << "\"errorCode\":\"" << EscapeJsonString(parsed.error_code)
              << "\","
              << "\"message\":\"" << EscapeJsonString(parsed.error_message)
              << "\"}\n";
    return 2;
  }

  const auto solve_t0 = SteadyClock::now();
  ldprover::DfpnSolver<19> solver(config);
  const auto report = solver.Solve(parsed.initial_position, parsed.proof_context,
                                   parsed.region_search_mask, prob_id);
  const auto solve_t1 = SteadyClock::now();

  const auto verify_t0 = SteadyClock::now();
  ldprover::ProofArtifactManager<19> artifacts;
  std::string checker_code = "SKIPPED_UNKNOWN";
  if (report.root_status != ldprover::ProofOutcome::kUnknown) {
    const auto ver = artifacts.VerifyProofDag(
        parsed.initial_position, parsed.proof_context, report);
    checker_code = ver.error_code;
    if (!ver.passed) {
      std::cerr << "[LDProver] Proof verification failed (" << ver.error_code
                << "): " << ver.message << "\n";
      return 2;
    }
  }
  const auto verify_t1 = SteadyClock::now();

  const auto ser_t0 = SteadyClock::now();
  std::string checksum;
  const std::string proof_json = artifacts.SerializeLProofJson(
      parsed.initial_position, parsed.proof_context, report, &checksum);
  const auto ser_t1 = SteadyClock::now();

  const auto write_t0 = SteadyClock::now();
  if (!out_proof_path.empty() &&
      !out_guard.WriteOutput("--out-proof", proof_json)) {
    std::cerr << "[LDProver] Failed to write proof file: " << out_proof_path
              << "\n";
    return 2;
  }
  if (!out_sgf_path.empty()) {
    const std::string sgf = artifacts.ExportSolutionTreeSgf(
        parsed.initial_position, parsed.proof_context, report);
    if (!out_guard.WriteOutput("--out-sgf", sgf)) {
      std::cerr << "[LDProver] Failed to write SGF file: " << out_sgf_path
                << "\n";
      return 2;
    }
  }
  const auto write_t1 = SteadyClock::now();

  if (!out_profile_path.empty()) {
    auto ns_between = [](SteadyClock::time_point a,
                         SteadyClock::time_point b) -> uint64_t {
      const auto diff =
          std::chrono::duration_cast<std::chrono::nanoseconds>(b - a).count();
      return diff > 0 ? static_cast<uint64_t>(diff) : 0ULL;
    };
    auto to_ms = [](uint64_t ns) -> double {
      return static_cast<double>(ns) / 1000000.0;
    };

    const auto& p = solver.StageProfile();
    const uint64_t parse_ns = ns_between(cli_t0, parse_t1);
    const uint64_t solve_cli_ns = ns_between(solve_t0, solve_t1);
    const uint64_t verify_ns = ns_between(verify_t0, verify_t1);
    const uint64_t ser_ns = ns_between(ser_t0, ser_t1);
    const uint64_t write_ns = ns_between(write_t0, write_t1);
    const uint64_t total_cli_ns = ns_between(cli_t0, write_t1);

    const uint64_t reval_outside_ns =
        p.reval_by_caller[static_cast<size_t>(ldprover::RevalCaller::kOutsideRz)]
            .inclusive_ns;
    const uint64_t reval_board_ns =
        p.reval_by_caller[static_cast<size_t>(ldprover::RevalCaller::kBoardTt)]
            .inclusive_ns;
    const uint64_t reval_pattern_ns =
        p.reval_by_caller[static_cast<size_t>(ldprover::RevalCaller::kPatternTt)]
            .inclusive_ns;
    const uint64_t total_reval_ns =
        reval_outside_ns + reval_board_ns + reval_pattern_ns;

    const uint64_t reval_accounted_ns =
        p.reval_cache_lookup_ns + p.benson_replay_ns +
        p.reval_witness_play_move_ns + p.reval_universal_gen_legal_ns +
        p.reval_universal_edge_scan_ns + p.reval_universal_play_move_ns;
    const uint64_t reval_other_self_ns =
        (total_reval_ns > reval_accounted_ns)
            ? (total_reval_ns - reval_accounted_ns)
            : 0ULL;

    const uint64_t accounted_search_ns =
        p.benson_main_ns + p.tt.board_lookup_exclusive_ns +
        p.tt.pattern_scan_exclusive_ns + total_reval_ns +
        p.outside_rz_play_move_ns + p.frontier_tctx_ns +
        p.frontier_gen_legal_ns + p.cand_eval_exclusive_ns + p.benson_cand_ns +
        p.frontier_sort_init_ns + p.main_play_undo_ns + p.rz_compute_ns +
        p.tt.board_store_ns + p.tt.pattern_store_ns;
    const uint64_t unaccounted_self_ns =
        (p.solve_total_ns > accounted_search_ns)
            ? (p.solve_total_ns - accounted_search_ns)
            : 0ULL;

    double user_cpu_ms = 0.0;
    double sys_cpu_ms = 0.0;
    uint64_t max_rss_bytes = 0;
#if defined(__APPLE__) || defined(__unix__)
    struct rusage ru {};
    if (getrusage(RUSAGE_SELF, &ru) == 0) {
      user_cpu_ms = static_cast<double>(ru.ru_utime.tv_sec) * 1000.0 +
                    static_cast<double>(ru.ru_utime.tv_usec) / 1000.0;
      sys_cpu_ms = static_cast<double>(ru.ru_stime.tv_sec) * 1000.0 +
                   static_cast<double>(ru.ru_stime.tv_usec) / 1000.0;
#if defined(__APPLE__)
      max_rss_bytes = static_cast<uint64_t>(ru.ru_maxrss);
#else
      max_rss_bytes = static_cast<uint64_t>(ru.ru_maxrss) * 1024ULL;
#endif
    }
#endif

    std::ostringstream pj;
    pj << std::fixed << std::setprecision(4);
    pj << "{\n";
    pj << "  \"problemId\": \"" << EscapeJsonString(prob_id) << "\",\n";
    pj << "  \"maxNodes\": " << config.max_nodes << ",\n";
    pj << "  \"mode\": \"" << (config.enable_pattern_tt ? "pattern-tt" : "board-tt") << "\",\n";
    pj << "  \"rootStatus\": \"" << OutcomeLabel(report.root_status) << "\",\n";
    pj << "  \"unknownReason\": \"" << UnknownReasonLabel(report.unknown_reason) << "\",\n";
    pj << "  \"numNodes\": " << report.num_nodes << ",\n";
    pj << "  \"prunedOutsideRz\": " << report.pruned_outside_rz_count << ",\n";
    pj << "  \"checker\": \"" << EscapeJsonString(checker_code) << "\",\n";
    pj << "  \"proofChecksum\": \"" << EscapeJsonString(checksum) << "\",\n";
    pj << "  \"proofJsonBytes\": " << proof_json.size() << ",\n";
    pj << "  \"cliStagesMs\": {\n";
    pj << "    \"readAndParseProblemMs\": " << to_ms(parse_ns) << ",\n";
    pj << "    \"solveSearchMs\": " << to_ms(solve_cli_ns) << ",\n";
    pj << "    \"inMemoryVerifyMs\": " << to_ms(verify_ns) << ",\n";
    pj << "    \"serializeProofJsonMs\": " << to_ms(ser_ns) << ",\n";
    pj << "    \"writeProofFileMs\": " << to_ms(write_ns) << ",\n";
    pj << "    \"totalCliMs\": " << to_ms(total_cli_ns) << "\n";
    pj << "  },\n";
    pj << "  \"processRusage\": {\n";
    pj << "    \"userCpuMs\": " << user_cpu_ms << ",\n";
    pj << "    \"sysCpuMs\": " << sys_cpu_ms << ",\n";
    pj << "    \"maxRssBytes\": " << max_rss_bytes << ",\n";
    pj << "    \"maxRssMiB\": " << (static_cast<double>(max_rss_bytes) / (1024.0 * 1024.0)) << "\n";
    pj << "  },\n";
    pj << "  \"exclusiveSearchMs\": {\n";
    pj << "    \"solveTotalMs\": " << to_ms(p.solve_total_ns) << ",\n";
    pj << "    \"bensonMainMs\": " << to_ms(p.benson_main_ns) << ",\n";
    pj << "    \"boardTtLookupExclusiveMs\": " << to_ms(p.tt.board_lookup_exclusive_ns) << ",\n";
    pj << "    \"patternTtScanExclusiveMs\": " << to_ms(p.tt.pattern_scan_exclusive_ns) << ",\n";
    pj << "    \"revalOutsideRzInclusiveMs\": " << to_ms(reval_outside_ns) << ",\n";
    pj << "    \"revalBoardTtInclusiveMs\": " << to_ms(reval_board_ns) << ",\n";
    pj << "    \"revalPatternTtInclusiveMs\": " << to_ms(reval_pattern_ns) << ",\n";
    pj << "    \"outsideRzPlayMoveMs\": " << to_ms(p.outside_rz_play_move_ns) << ",\n";
    pj << "    \"frontierTctxMs\": " << to_ms(p.frontier_tctx_ns) << ",\n";
    pj << "    \"frontierGenLegalMs\": " << to_ms(p.frontier_gen_legal_ns) << ",\n";
    pj << "    \"candEvalExclusiveMs\": " << to_ms(p.cand_eval_exclusive_ns) << ",\n";
    pj << "    \"bensonCandMs\": " << to_ms(p.benson_cand_ns) << ",\n";
    pj << "    \"frontierSortInitMs\": " << to_ms(p.frontier_sort_init_ns) << ",\n";
    pj << "    \"mainPlayUndoMs\": " << to_ms(p.main_play_undo_ns) << ",\n";
    pj << "    \"rzComputeMs\": " << to_ms(p.rz_compute_ns) << ",\n";
    pj << "    \"boardTtStoreMs\": " << to_ms(p.tt.board_store_ns) << ",\n";
    pj << "    \"patternTtStoreMs\": " << to_ms(p.tt.pattern_store_ns) << ",\n";
    pj << "    \"accountedExclusiveSumMs\": " << to_ms(accounted_search_ns) << ",\n";
    pj << "    \"unaccountedMidsearchSelfMs\": " << to_ms(unaccounted_self_ns) << "\n";
    pj << "  },\n";
    pj << "  \"revalBreakdownMs\": {\n";
    pj << "    \"totalRevalInclusiveMs\": " << to_ms(total_reval_ns) << ",\n";
    pj << "    \"cacheLookupMs\": " << to_ms(p.reval_cache_lookup_ns) << ",\n";
    pj << "    \"bensonReplayMs\": " << to_ms(p.benson_replay_ns) << ",\n";
    pj << "    \"witnessPlayMoveMs\": " << to_ms(p.reval_witness_play_move_ns) << ",\n";
    pj << "    \"universalGenLegalMs\": " << to_ms(p.reval_universal_gen_legal_ns) << ",\n";
    pj << "    \"universalEdgeScanMs\": " << to_ms(p.reval_universal_edge_scan_ns) << ",\n";
    pj << "    \"universalPlayMoveMs\": " << to_ms(p.reval_universal_play_move_ns) << ",\n";
    pj << "    \"revalOtherSelfMs\": " << to_ms(reval_other_self_ns) << "\n";
    pj << "  },\n";
    pj << "  \"ttStats\": {\n";
    pj << "    \"boardQueries\": " << p.tt.board_queries << ",\n";
    pj << "    \"boardBucketHits\": " << p.tt.board_bucket_hits << ",\n";
    pj << "    \"boardEntriesScanned\": " << p.tt.board_entries_scanned << ",\n";
    pj << "    \"boardExactOrMonotonicHits\": " << p.tt.board_exact_or_monotonic_hits << ",\n";
    pj << "    \"boardRevalEntered\": " << p.tt.board_reval_entered << ",\n";
    pj << "    \"boardRevalSucceeded\": " << p.tt.board_reval_succeeded << ",\n";
    pj << "    \"boardStoreCalls\": " << p.tt.board_store_calls << ",\n";
    pj << "    \"boardBucketCount\": " << p.tt.board_bucket_count << ",\n";
    pj << "    \"boardTotalEntries\": " << p.tt.board_total_entries << ",\n";
    pj << "    \"patternQueries\": " << p.tt.pattern_queries << ",\n";
    pj << "    \"patternEntriesScanned\": " << p.tt.pattern_entries_scanned << ",\n";
    pj << "    \"patternContextMatched\": " << p.tt.pattern_context_matched << ",\n";
    pj << "    \"patternGeomMatched\": " << p.tt.pattern_geom_matched << ",\n";
    pj << "    \"patternDirectExactHits\": " << p.tt.pattern_direct_exact_hits << ",\n";
    pj << "    \"patternHeuristicHits\": " << p.tt.pattern_heuristic_hits << ",\n";
    pj << "    \"patternRevalEntered\": " << p.tt.pattern_reval_entered << ",\n";
    pj << "    \"patternRevalSucceeded\": " << p.tt.pattern_reval_succeeded << ",\n";
    pj << "    \"patternStoreCalls\": " << p.tt.pattern_store_calls << ",\n";
    pj << "    \"patternEntryCount\": " << p.tt.pattern_entry_count << "\n";
    pj << "  },\n";
    pj << "  \"searchCounts\": {\n";
    pj << "    \"bensonMainCalls\": " << p.benson_main_calls << ",\n";
    pj << "    \"bensonCandCalls\": " << p.benson_cand_calls << ",\n";
    pj << "    \"bensonReplayCalls\": " << p.benson_replay_calls << ",\n";
    pj << "    \"newFrontiers\": " << p.new_frontiers << ",\n";
    pj << "    \"candidatesGenerated\": " << p.candidates_generated << ",\n";
    pj << "    \"candidatesScored\": " << p.candidates_scored << ",\n";
    pj << "    \"candidatesPassScored\": " << p.candidates_pass_scored << ",\n";
    pj << "    \"candidatesOuterMoatSkipped\": " << p.candidates_outer_moat_skipped << ",\n";
    pj << "    \"candidateScoringPlayMoves\": " << p.candidate_scoring_play_moves << ",\n";
    pj << "    \"outsideRzCandidatesTested\": " << p.outside_rz_candidates_tested << ",\n";
    pj << "    \"mainSearchPlayMoves\": " << p.main_search_play_moves << ",\n";
    pj << "    \"revalRecursiveVisits\": " << p.reval_recursive_visits << ",\n";
    pj << "    \"revalCacheHits\": " << p.reval_cache_hits << ",\n";
    pj << "    \"revalCacheMisses\": " << p.reval_cache_misses << ",\n";
    pj << "    \"revalWitnessVisits\": " << p.reval_witness_visits << ",\n";
    pj << "    \"revalWitnessPlayMoves\": " << p.reval_witness_play_moves << ",\n";
    pj << "    \"revalUniversalVisits\": " << p.reval_universal_visits << ",\n";
    pj << "    \"revalUniversalLegalMoves\": " << p.reval_universal_legal_moves << ",\n";
    pj << "    \"revalUniversalEdgeComparisons\": " << p.reval_universal_edge_comparisons << ",\n";
    pj << "    \"revalUniversalPlayMoves\": " << p.reval_universal_play_moves << ",\n";
    auto emit_caller = [&](const char* label, ldprover::RevalCaller c, bool last) {
      const auto& cs = p.reval_by_caller[static_cast<size_t>(c)];
      pj << "    \"" << label << "\": {\"topCalls\": " << cs.top_calls
         << ", \"topSuccesses\": " << cs.top_successes
         << ", \"topFailures\": " << cs.top_failures
         << ", \"inclusiveMs\": " << to_ms(cs.inclusive_ns) << "}"
         << (last ? "\n" : ",\n");
    };
    pj << "    \"revalByCaller\": {\n";
    emit_caller("outsideRz", ldprover::RevalCaller::kOutsideRz, false);
    emit_caller("boardTt", ldprover::RevalCaller::kBoardTt, false);
    emit_caller("patternTt", ldprover::RevalCaller::kPatternTt, true);
    pj << "    }\n";
    pj << "  },\n";
    pj << "  \"structuresAndMemory\": {\n";
    pj << "    \"peakFrontiers\": " << p.peak_frontiers << ",\n";
    pj << "    \"liveFrontiersAtEnd\": " << p.live_frontiers_at_end << ",\n";
    pj << "    \"revalCacheEntries\": " << p.reval_cache_entries << ",\n";
    pj << "    \"dagNodes\": " << p.dag_nodes << ",\n";
    pj << "    \"bensonUcaLeaves\": " << p.benson_uca_leaves << ",\n";
    pj << "    \"tokensCapturedLeaves\": " << p.tokens_captured_leaves << ",\n";
    pj << "    \"doublePassLeaves\": " << p.double_pass_leaves << ",\n";
    pj << "    \"prunedOutsideRzDagNodes\": " << p.pruned_outside_rz_dag_nodes << ",\n";
    pj << "    \"ttHitDagNodes\": " << p.tt_hit_dag_nodes << ",\n";
    pj << "    \"estimatedMemoryBytes\": " << p.estimated_memory_bytes << "\n";
    pj << "  }\n";
    pj << "}\n";

    if (!out_guard.WriteOutput("--profile-json", pj.str())) {
      std::cerr << "[LDProver] Failed to write profile JSON: "
                << out_profile_path << "\n";
      return 2;
    }
  }

  if (!out_convergence_path.empty()) {
    const auto& tr = solver.ConvergenceTrace();
    auto emit_child_array =
        [&](std::ostringstream& os,
            const std::vector<ldprover::ObservedChildSummary>& items,
            const char* indent) {
          os << "[";
          if (!items.empty()) os << "\n";
          for (size_t i = 0; i < items.size(); ++i) {
            const auto& c = items[i];
            os << indent << "  {\"moveSgf\": \""
               << EscapeJsonString(c.move_sgf)
               << "\", \"move\": " << c.move << ", \"rank\": " << c.rank
               << ", \"tacticalScore\": " << c.tactical_score
               << ", \"pn\": " << c.pn << ", \"dn\": " << c.dn
               << ", \"probed\": " << (c.probed ? "true" : "false")
               << ", \"koDependent\": " << (c.ko_dependent ? "true" : "false")
               << ", \"inWindow\": " << (c.in_window ? "true" : "false")
               << ", \"deferredOutsideRz\": "
               << (c.deferred_outside_rz ? "true" : "false")
               << ", \"prunedOutsideRz\": "
               << (c.pruned_outside_rz ? "true" : "false")
               << ", \"hasDecisiveDag\": "
               << (c.has_decisive_dag ? "true" : "false")
               << ", \"outcome\": \"" << OutcomeLabel(c.outcome) << "\"}";
            if (i + 1U < items.size()) os << ",";
            os << "\n";
          }
          if (!items.empty()) os << indent;
          os << "]";
        };

    std::ostringstream cj;
    cj << "{\n";
    cj << "  \"problemId\": \"" << EscapeJsonString(prob_id) << "\",\n";
    cj << "  \"maxNodes\": " << config.max_nodes << ",\n";
    cj << "  \"rootStatus\": \"" << OutcomeLabel(report.root_status) << "\",\n";
    cj << "  \"unknownReason\": \""
       << UnknownReasonLabel(report.unknown_reason) << "\",\n";
    cj << "  \"numNodes\": " << report.num_nodes << ",\n";
    cj << "  \"prunedOutsideRz\": " << report.pruned_outside_rz_count << ",\n";
    cj << "  \"proofChecksum\": \"" << EscapeJsonString(checksum) << "\",\n";
    cj << "  \"firstTerminalLeafNode\": " << tr.first_terminal_leaf_node << ",\n";
    cj << "  \"firstTerminalLeafKind\": \""
       << EvidenceKindLabel(tr.first_terminal_leaf_kind) << "\",\n";
    cj << "  \"firstTerminalLeafPath\": \""
       << EscapeJsonString(tr.first_terminal_leaf_path) << "\",\n";
    cj << "  \"firstProvenSubproofNode\": " << tr.first_proven_subproof_node
       << ",\n";
    cj << "  \"firstProvenSubproofOutcome\": \""
       << OutcomeLabel(tr.first_proven_subproof_outcome) << "\",\n";
    cj << "  \"firstProvenSubproofDagId\": "
       << (tr.first_proven_subproof_dag_id == ldprover::kInvalidDagNodeId
               ? -1
               : static_cast<int64_t>(tr.first_proven_subproof_dag_id))
       << ",\n";
    cj << "  \"firstProvenSubproofPath\": \""
       << EscapeJsonString(tr.first_proven_subproof_path) << "\",\n";
    cj << "  \"maxDepthReached\": " << tr.max_depth_reached << ",\n";
    cj << "  \"deepestPath\": \"" << EscapeJsonString(tr.deepest_path)
       << "\",\n";
    cj << "  \"watchedPaths\": [\n";
    for (size_t wi = 0; wi < tr.watched_paths.size(); ++wi) {
      const auto& wt = tr.watched_paths[wi];
      cj << "    {\n";
      cj << "      \"path\": \"" << EscapeJsonString(wt.path) << "\",\n";
      cj << "      \"firstEnterNode\": " << wt.first_enter_node << ",\n";
      cj << "      \"visitCount\": " << wt.visit_count << ",\n";
      cj << "      \"firstActiveRzSourceNode\": "
         << wt.first_active_rz_source_node << ",\n";
      cj << "      \"firstActiveRzSourceMoveSgf\": \""
         << EscapeJsonString(wt.first_active_rz_source_move_sgf) << "\",\n";
      cj << "      \"firstActiveRzSourceDagId\": "
         << (wt.first_active_rz_source_dag_id == ldprover::kInvalidDagNodeId
                 ? -1
                 : static_cast<int64_t>(wt.first_active_rz_source_dag_id))
         << ",\n";
      cj << "      \"firstActiveRzSourceSize\": "
         << wt.first_active_rz_source_size << ",\n";
      cj << "      \"firstDecisiveChildNode\": "
         << wt.first_decisive_child_node << ",\n";
      cj << "      \"firstDecisiveChildMoveSgf\": \""
         << EscapeJsonString(wt.first_decisive_child_move_sgf) << "\",\n";
      cj << "      \"firstDecisiveChildOutcome\": \""
         << OutcomeLabel(wt.first_decisive_child_outcome) << "\",\n";
      cj << "      \"maxDepthUnderPath\": " << wt.max_depth_under_path
         << ",\n";
      cj << "      \"deepestLineUnderPath\": \""
         << EscapeJsonString(wt.deepest_line_under_path) << "\",\n";
      cj << "      \"frontierExists\": "
         << (wt.frontier_exists ? "true" : "false") << ",\n";
      cj << "      \"frontierErasedOnProof\": "
         << (wt.frontier_erased_on_proof ? "true" : "false") << ",\n";
      cj << "      \"isOrNode\": " << (wt.is_or_node ? "true" : "false")
         << ",\n";
      cj << "      \"totalLegalMoves\": " << wt.total_legal_moves << ",\n";
      cj << "      \"wideningLevel\": " << wt.widening_level << ",\n";
      cj << "      \"windowSize\": " << wt.window_size << ",\n";
      cj << "      \"hasActiveRzSource\": "
         << (wt.has_active_rz_source ? "true" : "false") << ",\n";
      cj << "      \"representativeMoveSgf\": \""
         << EscapeJsonString(wt.representative_move_sgf) << "\",\n";
      cj << "      \"activeRzSize\": " << wt.active_rz_size << ",\n";
      cj << "      \"closedProvenWinDirect\": " << wt.closed_proven_win_direct
         << ",\n";
      cj << "      \"closedProvenWinOutsideRz\": "
         << wt.closed_proven_win_outside_rz << ",\n";
      cj << "      \"closedProvenLossDirect\": "
         << wt.closed_proven_loss_direct << ",\n";
      cj << "      \"closedProvenLossOutsideRz\": "
         << wt.closed_proven_loss_outside_rz << ",\n";
      cj << "      \"deferredOutsideRzCount\": "
         << wt.deferred_outside_rz_count << ",\n";
      cj << "      \"koBarrierCount\": " << wt.ko_barrier_count << ",\n";
      cj << "      \"expandedUnknownCount\": " << wt.expanded_unknown_count
         << ",\n";
      cj << "      \"unexpandedUnknownCount\": "
         << wt.unexpanded_unknown_count << ",\n";
      cj << "      \"topUnclosedChildren\": ";
      emit_child_array(cj, wt.top_unclosed_children, "      ");
      cj << ",\n";
      cj << "      \"watchedNextMoves\": ";
      emit_child_array(cj, wt.watched_next_moves, "      ");
      cj << "\n    }" << (wi + 1U < tr.watched_paths.size() ? "," : "")
         << "\n";
    }
    cj << "  ]\n";
    cj << "}\n";

    if (!out_guard.WriteOutput("--convergence-json", cj.str())) {
      std::cerr << "[LDProver] Failed to write convergence JSON: "
                << out_convergence_path << "\n";
      return 2;
    }
  }

  if (!out_guard.Commit()) {
    std::cerr << "[LDProver] Failed to commit output files.\n";
    return 2;
  }

  std::cout << "{\"solverVersion\":\"LDProver-1.8.2\",\"problemId\":\""
            << EscapeJsonString(prob_id) << "\",\"rootStatus\":\""
            << OutcomeLabel(report.root_status)
            << "\",\"unknownReason\":\""
            << UnknownReasonLabel(report.unknown_reason)
            << "\",\"bestMove\":" << report.best_move
            << ",\"numNodes\":" << report.num_nodes
            << ",\"prunedOutsideRz\":" << report.pruned_outside_rz_count
            << ",\"checker\":\"" << EscapeJsonString(checker_code)
            << "\",\"proofChecksum\":\"" << EscapeJsonString(checksum) << "\"}\n";
  return 0;
}

template <int N>
int ExecuteCheckForBoardSize(
    const std::string& proof_json, const std::string& problem_path,
    std::optional<ldprover::VerificationScope> scope_override,
    ldprover::VerificationReport* out_ver) {
  ldprover::ProofArtifactManager<N> mgr;
  if (!problem_path.empty()) {
    std::string raw_problem_json;
    if (!ReadEntireFile(problem_path, &raw_problem_json)) {
      std::cerr << "[LDProver] Cannot read --problem file: " << problem_path
                << "\n";
      return 2;
    }
    ldprover::ProblemContractParser<N> parser;
    const std::string pid = BasenameStem(problem_path);
    const auto parsed = parser.ParseTsumegoJsonObject(pid, raw_problem_json);
    if (!parsed.valid) {
      std::cerr << "{\"problemId\":\"" << EscapeJsonString(pid)
                << "\",\"valid\":false,"
                << "\"errorCode\":\"" << EscapeJsonString(parsed.error_code)
                << "\","
                << "\"message\":\"" << EscapeJsonString(parsed.error_message)
                << "\"}\n";
      return 2;
    }
    *out_ver = mgr.VerifyLProofJsonString(proof_json, &parsed, scope_override);
    return 0;
  }
  *out_ver = mgr.VerifyLProofJsonString(proof_json, nullptr, scope_override);
  return 0;
}

int RunCheckCommand(int argc, char* argv[]) {
  std::string proof_path;
  std::string problem_path;
  bool allow_subposition = false;
  bool free_exploration = false;
  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--proof" && i + 1 < argc) {
      proof_path = argv[++i];
    } else if (arg == "--problem" && i + 1 < argc) {
      problem_path = argv[++i];
    } else if (arg == "--allow-subposition") {
      allow_subposition = true;
    } else if (arg == "--free-exploration") {
      free_exploration = true;
    } else {
      std::cerr << "[LDProver] Unknown or incomplete check option: " << arg
                << "\n";
      return 2;
    }
  }

  if (allow_subposition && free_exploration) {
    std::cerr << "[LDProver] --allow-subposition and --free-exploration are "
                 "mutually exclusive.\n";
    return 2;
  }
  std::optional<ldprover::VerificationScope> scope_override;
  if (allow_subposition) {
    scope_override = ldprover::VerificationScope::kTracedWithinRules;
  } else if (free_exploration) {
    scope_override = ldprover::VerificationScope::kFreeExploration;
  }

  if (proof_path.empty()) {
    std::cerr << "[LDProver] Missing required --proof <proof.json>\n";
    return 2;
  }

  std::string proof_json;
  if (!ReadEntireFile(proof_path, &proof_json)) {
    std::cerr << "[LDProver] Cannot read proof file: " << proof_path << "\n";
    return 2;
  }

  const int bs = DetectBoardSizeFromProofJson(proof_json);
  ldprover::VerificationReport ver;
  int prep_rc = 0;
  if (bs == 5) {
    prep_rc = ExecuteCheckForBoardSize<5>(proof_json, problem_path,
                                          scope_override, &ver);
  } else if (bs == 7) {
    prep_rc = ExecuteCheckForBoardSize<7>(proof_json, problem_path,
                                          scope_override, &ver);
  } else if (bs == 19) {
    prep_rc = ExecuteCheckForBoardSize<19>(proof_json, problem_path,
                                           scope_override, &ver);
  } else {
    std::cerr << "[LDProver] Unsupported boardSize in proof JSON.\n";
    return 2;
  }
  if (prep_rc != 0) return prep_rc;

  std::cout << "{\"passed\":" << (ver.passed ? "true" : "false")
            << ",\"errorCode\":\"" << EscapeJsonString(ver.error_code)
            << "\",\"message\":\"" << EscapeJsonString(ver.message)
            << "\",\"verifiedNodes\":" << ver.verified_nodes
            << ",\"verifiedStates\":" << ver.verified_states
            << ",\"replayedPrunedCertificates\":"
            << ver.replayed_pruned_certificates
            << ",\"encodingMode\":\"" << EscapeJsonString(ver.encoding_mode)
            << "\",\"verifiedScope\":\"" << EscapeJsonString(ver.verified_scope)
            << "\",\"verifiedRootKind\":\""
            << EscapeJsonString(ver.verified_root_kind)
            << "\",\"traceOutsideRegion\":"
            << (ver.trace_outside_region ? "true" : "false")
            << ",\"traceHasRestrictedKoCapture\":"
            << (ver.trace_has_restricted_ko_capture ? "true" : "false")
            << ",\"checksum\":\"" << EscapeJsonString(ver.jcs_sha256_checksum)
            << "\",\"canonicalDagChecksum\":\""
            << EscapeJsonString(ver.canonical_dag_checksum)
            << "\"}\n";
  return ver.passed ? 0 : 2;
}

int RunBenchCommand(int argc, char* argv[]) {
  std::string manifest_path;
  std::string out_csv_path;
  ldprover::SolverConfig config;
  config.max_nodes = 2500;

  for (int i = 2; i < argc; ++i) {
    const std::string arg = argv[i];
    if (arg == "--manifest" && i + 1 < argc) {
      manifest_path = argv[++i];
    } else if (arg == "--out" && i + 1 < argc) {
      out_csv_path = argv[++i];
    } else if (arg == "--node-limit" && i + 1 < argc) {
      config.max_nodes =
          static_cast<uint32_t>(std::strtoul(argv[++i], nullptr, 10));
    } else {
      std::cerr << "[LDProver] Unknown or incomplete bench option: " << arg
                << "\n";
      return 2;
    }
  }

  if (manifest_path.empty()) {
    std::cerr << "[LDProver] Missing required --manifest <manifest.json>\n";
    return 2;
  }

  std::string manifest_json;
  if (!ReadEntireFile(manifest_path, &manifest_json)) {
    std::cerr << "[LDProver] Cannot read manifest file: " << manifest_path
              << "\n";
    return 2;
  }

  FileIdentity manifest_id{};
  if (!StatFileIdentity(manifest_path, &manifest_id)) {
    std::cerr << "[LDProver] Cannot stat manifest file: " << manifest_path
              << "\n";
    return 2;
  }

  const auto problem_files = ParseJsonStringArray(manifest_json);
  if (problem_files.empty()) {
    std::cerr << "[LDProver] Manifest must be a non-empty JSON array of problem "
                 "file paths.\n";
    return 2;
  }

  std::vector<InputFileRecord> bench_inputs;
  bench_inputs.reserve(1U + problem_files.size());
  bench_inputs.push_back({"--manifest", manifest_path, manifest_id});
  for (size_t idx = 0; idx < problem_files.size(); ++idx) {
    FileIdentity pfile_id{};
    if (!StatFileIdentity(problem_files[idx], &pfile_id)) {
      std::cerr << "[LDProver] Cannot read benchmark problem: "
                << problem_files[idx] << "\n";
      return 2;
    }
    bench_inputs.push_back(
        {"manifest[" + std::to_string(idx) + "]", problem_files[idx], pfile_id});
  }

  OutputReservationGuard bench_guard;
  std::string bench_conflict_err;
  if (!bench_guard.Reserve(bench_inputs, {{"--out", out_csv_path}},
                           &bench_conflict_err)) {
    std::cerr << bench_conflict_err;
    return 2;
  }

  std::ostringstream csv;
  csv << "problem_id,root_status,best_move,num_nodes,pruned_outside_rz,checker\n";

  ldprover::ProblemContractParser<19> parser;
  ldprover::ProofArtifactManager<19> checker;
  uint32_t proven_count = 0;

  for (const std::string& pfile : problem_files) {
    std::string raw_json;
    if (!ReadEntireFile(pfile, &raw_json)) {
      std::cerr << "[LDProver] Cannot read benchmark problem: " << pfile << "\n";
      return 2;
    }
    const std::string pid = BasenameStem(pfile);
    const auto parsed = parser.ParseTsumegoJsonObject(pid, raw_json);
    if (!parsed.valid) {
      std::cerr << "[LDProver] Contract error in " << pid << ": "
                << parsed.error_code << "\n";
      return 2;
    }
    ldprover::DfpnSolver<19> solver(config);
    const auto rep = solver.Solve(parsed.initial_position, parsed.proof_context,
                                  parsed.region_search_mask);
    std::string chk_status = "UNKNOWN_BARRIER";
    if (rep.root_status != ldprover::ProofOutcome::kUnknown) {
      const auto ver = checker.VerifyProofDag(parsed.initial_position,
                                              parsed.proof_context, rep);
      if (!ver.passed) {
        std::cerr << "[LDProver] Benchmark proof check FAILED on " << pid
                  << " (" << ver.error_code << ")\n";
        return 2;
      }
      chk_status = "PASS";
      ++proven_count;
    }
    csv << pid << "," << OutcomeLabel(rep.root_status) << "," << rep.best_move
        << "," << rep.num_nodes << "," << rep.pruned_outside_rz_count << ","
        << chk_status << "\n";
  }

  if (!out_csv_path.empty() && !bench_guard.WriteOutput("--out", csv.str())) {
    std::cerr << "[LDProver] Cannot write CSV output: " << out_csv_path << "\n";
    return 2;
  }

  if (!bench_guard.Commit()) {
    std::cerr << "[LDProver] Failed to commit CSV output: " << out_csv_path
              << "\n";
    return 2;
  }

  std::cout << "{\"subcommand\":\"bench\",\"totalProblems\":"
            << problem_files.size() << ",\"provenAndVerified\":" << proven_count
            << "}\n";
  return 0;
}

}  // namespace

int main(int argc, char* argv[]) {
  if (argc < 2) {
    std::cerr << "Usage: tprover <solve|check|bench> [options]\n"
              << "  solve --problem <file.json> [--out-proof <proof.json>] "
              << "[--profile-json <profile.json>] "
              << "[--mode board-tt|pattern-tt] [--node-limit <N>] "
              << "[--memory-budget <MiB>]\n"
              << "  check --proof <proof.json> [--problem <original.json>] "
              << "[--allow-subposition | --free-exploration]\n"
              << "  bench --manifest <benchmark_manifest.json> [--out <out.csv>]\n";
    return 2;
  }

  try {
    const std::string subcommand = argv[1];
    if (subcommand == "solve") return RunSolveCommand(argc, argv);
    if (subcommand == "check") return RunCheckCommand(argc, argv);
    if (subcommand == "bench") return RunBenchCommand(argc, argv);

    std::cerr << "[LDProver] Unknown subcommand: " << subcommand << "\n";
    return 2;
  } catch (const std::exception& e) {
    std::cerr << "[LDProver] Internal error: " << e.what() << "\n";
    return 3;
  }
}
