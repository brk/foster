// Copyright (c) 2011 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <set>
#include <stack>

template <typename Key, typename Work>
class WorklistLIFO {
  std::stack<Work> worklist;
  std::set<Key>    seen;

public:
  void clear() {
    while (!worklist.empty()) { worklist.pop(); }
    seen.clear();
  }
  bool tryAdd(Key key, Work work) {
    if (seen.count(key) == 0) {
      seen.insert(key);
      worklist.push(work);
      return true;
    }
    return false;
  }
  bool empty() { return worklist.empty(); }
  Work get() {
    Work work = worklist.top();
    worklist.pop();
    return work;
  }
};
