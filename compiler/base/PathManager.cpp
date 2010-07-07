// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/PathManager.h"

#include <iostream>

using llvm::sys::Path;

namespace foster {

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
  if (candidates.empty()) {
    return inputPath.str();
  }

  // Our input path is ..../d/c/b.a
  // and we have a set of paths that end in b.a;
  // they may or may not match c/b.a.
  // We'll iterate backwards through the input path,
  // narrowing the set of the candidates that have
  // matched every subcomponent of the path so far.
  // When the set of matching candidates (not including
  // the input path) becomes empty, the desired
  // suffix is the subpath formed by concatenating
  // the inspected components.
  typedef std::set<std::string> CandSet; 
  CandSet remainingCandidates(candidates);
  CandSet potentialCandidates;
  size_t offsetFromBack = inputPath.getLast().size();
  const std::string& inputPathStr = inputPath.str(); 
  size_t inputPathLength  = inputPath.size(); 

  remainingCandidates.erase(inputPathStr);

  // Loop invariant: at the header, remainingCandidates
  // is the set of paths, not including the input path,
  // that have matched the last offsetFromBack characters
  // in inputPath.
  while (offsetFromBack < inputPathLength
      && !remainingCandidates.empty()) {
    potentialCandidates.clear();
    // TODO replace with std::copy
    for (CandSet::iterator it = remainingCandidates.begin();
                           it != remainingCandidates.end();
                           ++it) {
      potentialCandidates.insert(*it);
    }
    remainingCandidates.clear();

    for (CandSet::iterator it = potentialCandidates.begin();
                           it != potentialCandidates.end();
                           ++it) {
      const std::string& s = *it;
      if (offsetFromBack >= s.size()) continue;
      char sc = s[s.size() - offsetFromBack];
      char ic = inputPathStr[inputPathStr.size() - offsetFromBack];
      if (sc == ic) {
        remainingCandidates.insert(s);
      }
    }
    ++offsetFromBack;
  }

  const std::string& matchingPath(
     (remainingCandidates.size() == 1)
        ? *(remainingCandidates.begin())
        :  inputPathStr);
  return wellFormedSuffixIncluding(inputPath, offsetFromBack);
}

std::string PathManager::getShortestUnambiguousSuffix(const Path& path) {
  return disamb(candidates[path.getLast()], path);
}

} // namespace foster

