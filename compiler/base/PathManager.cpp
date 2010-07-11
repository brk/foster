// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/PathManager.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <queue>

using llvm::sys::Path;

namespace foster {

PathManager gPathManager;

void PathManager::registerPath(const Path& path) {
  candidates[path.getLast()].insert( path.str() );
}

static char getDirectorySeparator(const Path& p) {
  size_t dirSepOffsetFromBack = p.getLast().size();
  if (dirSepOffsetFromBack == p.size()) return '\0';
  return p.str()[p.size() - dirSepOffsetFromBack - 1];
}

static std::string wellFormedSuffixIncluding(
	const Path& inputPath, size_t offsetFromBack) {
  const std::string& s(inputPath.str());
  char dirSep = getDirectorySeparator(inputPath);
  if (!dirSep) return s;

  size_t completeSuffixOffset = s.size() - offsetFromBack;
  while (completeSuffixOffset > 0 &&
         s[completeSuffixOffset] != dirSep) {
    --completeSuffixOffset;
  }

  // We don't want to return absolute paths,
  // unless the original path was absolute
  if (s[completeSuffixOffset] == dirSep
    &&  completeSuffixOffset > 0) {
    ++completeSuffixOffset;
  }

  return s.substr(completeSuffixOffset);
}

static std::string disamb(const std::set<std::string>& candidates,
                          const Path& inputPath) {
  
  std::string pathstr = inputPath.str();
  if (candidates.empty()) { return pathstr; }

  // Our input path is ..../d/c/b.a
  // and we have a set of paths that end in b.a;
  // they may or may not match c/b.a.
  //
  // We'll choose the candidate with the longest matching suffix.
  typedef std::set<std::string> CandSet;
  typedef std::string::reverse_iterator rit;
  typedef std::pair<int, const std::string*> MatchedLengthSuffix;
  std::priority_queue<MatchedLengthSuffix> pq;
  
  // Given no alternatives, the shortest unambiguous suffix
  // for the input path is the last component of the input path.
  pq.push(MatchedLengthSuffix(inputPath.getLast().size(), &pathstr));

  for (CandSet::iterator it = candidates.begin();
                         it != candidates.end();
                       ++it) {
    std::string s = *it;
    
    // We've already created an entry for the input path, so skip it.
    if (s == pathstr) continue;
    
    // Make sure we don't inspect more characters than either string's length.
    size_t commonLength = (std::min)(pathstr.size(), s.size());
    
    // Find the first mismatched character from the backs of each string.
    std::pair<rit, rit> mm = std::mismatch(
          s.rbegin(),
          s.rbegin() + commonLength,
          pathstr.rbegin());
    
    // Store a pointer to the string, along with the matched length.
    size_t offsetFromBack = std::distance(s.rbegin(), mm.first);
    pq.push(MatchedLengthSuffix(offsetFromBack, &(*it)));
  }
  
  return wellFormedSuffixIncluding(inputPath, pq.top().first);
}

std::string PathManager::getShortestUnambiguousSuffix(const Path& path) {
  return disamb(candidates[path.getLast()], path);
}

} // namespace foster

