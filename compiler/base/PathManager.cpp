// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/PathManager.h"

#include "pystring/pystring.h"

#include <algorithm>
#include <iostream>
#include <iterator>
#include <queue>

using llvm::sys::Path;
using llvm::StringRef;

using std::map;
using std::set;
using std::string;

namespace {
typedef set<Path> PathSet;
}

namespace foster {

PathManager gPathManager;

struct PathManager::Impl {
  // Our assumption is that few paths end with the same
  // filename, so we map ending filenames to sets of paths,
  // which with then do a more-or-less brute-force manipulation
  // to find the shortest unambiguous path from the set.
  typedef StringRef            Filename;
  typedef set<string>          MatchingPaths;
  map<Filename, MatchingPaths> candidates;

  PathSet moduleRootPaths;
};

PathManager::PathManager() {
  impl = new Impl();
}

void
PathManager::registerPath(const Path& path) {
  impl->candidates[path.getLast()].insert( path.str() );
}

static char
getDirectorySeparator(const Path& p) {
  if (p.str().empty()) return '\0';

  size_t dirSepOffsetFromBack = p.getLast().size();
  if (dirSepOffsetFromBack == p.size()) return '\0';
  return p.str()[p.size() - dirSepOffsetFromBack - 1];
}

static string
wellFormedSuffixIncluding(
        const Path& inputPath, size_t offsetFromBack) {
  const string& s(inputPath.str());
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

static string
disamb(const set<string>& candidates,
                          const Path& inputPath) {

  string pathstr = inputPath.str();
  if (candidates.empty()) { return pathstr; }

  // Our input path is ..../d/c/b.a
  // and we have a set of paths that end in b.a;
  // they may or may not match c/b.a.
  //
  // We'll choose the candidate with the longest matching suffix.
  typedef set<string> CandSet;
  typedef string::reverse_iterator rit;
  typedef std::pair<int, const string*> MatchedLengthSuffix;
  std::priority_queue<MatchedLengthSuffix> pq;

  // Given no alternatives, the shortest unambiguous suffix
  // for the input path is the last component of the input path.
  pq.push(MatchedLengthSuffix(inputPath.getLast().size(), &pathstr));

  for (CandSet::iterator it = candidates.begin();
                         it != candidates.end();
                       ++it) {
    string s = *it;

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

string
PathManager::getShortestUnambiguousSuffix(const Path& path) {
  return disamb(impl->candidates[path.getLast()], path);
}

////////////////////////////////////////////////////////////////////

void
PathManager::registerModuleSearchPath(const Path& path) {
  impl->moduleRootPaths.insert(path);
}

static bool
isValidDirectory(const Path& path) {
  return path.isValid() && path.isDirectory();
}

// Returns true if the given path has the chain of subdirectories specified
// by parts. On return, outRoot will be the deepest valid subdirectory of path.
static bool
hasSubdirectories(const Path& path,
                              const std::vector<string>& parts,
                              Path& outRoot) {
  outRoot = path;
  for (size_t i = 0; i < parts.size(); ++i) {
    outRoot.appendComponent(parts[i]);
    if (!isValidDirectory(outRoot)) {
      outRoot.eraseComponent();
      return false;
    }
  }
  return true;
}

set<Path>
PathManager::searchForModuleHomes(const string& fooDotBar) {
  PathSet rv;
  PathSet toDiscard;

  std::vector<string> parts;
  pystring::split(fooDotBar, parts, ".");

  for (PathSet::iterator it = impl->moduleRootPaths.begin();
                        it != impl->moduleRootPaths.end(); ++it) {
    const llvm::sys::Path& path = *it;
    llvm::sys::Path moduleRoot = path; // for now, hasSubdirs will modify

    if (!isValidDirectory(path)) {
      toDiscard.insert(path);
    } else if (hasSubdirectories(path, parts, moduleRoot)) {
      rv.insert(path);
    }
  }

  for (PathSet::iterator it = toDiscard.begin();
                         it != toDiscard.end(); ++it) {
    impl->moduleRootPaths.erase(*it);
  }

  return rv;
}

} // namespace foster

