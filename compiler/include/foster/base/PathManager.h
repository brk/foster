// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PATH_MANAGER_H
#define FOSTER_PATH_MANAGER_H

#include "llvm/System/Path.h"

#include <string>
#include <map>
#include <set>

namespace foster {

class PathManager {
  // Our assumption is that few paths end with the same
  // filename, so we map ending filenames to sets of paths,
  // which with then do a more-or-less brute-force manipulation
  // to find the shortest unambiguous path from the set.
  typedef llvm::StringRef       Filename;
  typedef std::set<std::string> MatchingPaths;
  std::map<Filename, MatchingPaths> candidates;

  typedef std::set<llvm::sys::Path> PathSet;
  PathSet moduleRootPaths;

public:
  PathManager() {}

  // Only registered paths are considered when
  // determining shortest unambiguous suffixes.
  void registerPath(const llvm::sys::Path& path);


  void registerModuleSearchPath(const llvm::sys::Path& path);

  // Returns a set of directories which *might* contain either interface or
  // implementation, in compiled or uncompiled form, of the given module name.
  std::set<llvm::sys::Path> searchForModuleHomes(const std::string& fooDotBar);

  std::string getShortestUnambiguousSuffix(const llvm::sys::Path& path);
};

extern PathManager gPathManager;

} // namespace foster

#endif

