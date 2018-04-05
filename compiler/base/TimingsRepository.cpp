// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Format.h"

#include "base/TimingsRepository.h"
#include "pystring/pystring.h"

namespace foster {

TimingsRepository gTimings;

void TimingsRepository::incr(const char* dottedpath, uint64_t n) {
  std::vector<string> parts;
  pystring::split(dottedpath, parts, ".");

  local_us[dottedpath] += n;

  string prefix;
  for (size_t i = 0; i < parts.size(); ++i) {
    if (i > 0) prefix += ".";
    prefix += parts[i];
    total_us[prefix] += n;
  }
}

void TimingsRepository::print(const std::string& title) {
  size_t maxTotalLength = 0;
  for (auto it : total_us) {
    const string& s = it.first;
    maxTotalLength = (std::max)(maxTotalLength, s.size());
  }
  string pathFormatString;
  llvm::raw_string_ostream pfs(pathFormatString);
  pfs << "\t%-" << (maxTotalLength) << "s";
  pfs.flush();

  llvm::outs() << "============== " << title << " =============\n";
  llvm::outs() << llvm::format(pathFormatString.c_str(), (const char*) "Category name")
      << "     Total" << "     " << "Local" << "\n";

  for (auto it : total_us) {
    const string& s = it.first;
    const string& d = descriptions[s];

    if (local_us[s] < 1000 && d.empty()) {
      continue; // Don't report on uninteresting operations.
    }

    llvm::outs() << llvm::format(pathFormatString.c_str(), s.c_str())
                << "  " << llvm::format("%5u ms", (unsigned) total_us[s] / 1000)
                << "  " << llvm::format("%5u ms", (unsigned) local_us[s] / 1000);
    if (!d.empty()) {
      llvm::outs() << " -- " << d;
    } 
    llvm::outs() << "\n";
  }
}

} // namespace foster

