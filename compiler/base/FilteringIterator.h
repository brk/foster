// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_FILTERING_ITERATOR_H
#define FOSTER_FILTERING_ITERATOR_H

#include <iterator>
#include <vector>

namespace foster {

template <typename Base, typename Derived>
struct dynamic_cast_filtering_iterator
   : public std::iterator<std::forward_iterator_tag, Derived>
{
  typedef dynamic_cast_filtering_iterator<Base, Derived> Self;
  typedef std::iterator<std::forward_iterator_tag, Derived> super;
  typedef typename super::pointer pointer;
  typedef typename super::reference reference;

  typedef typename std::vector<Base*>::iterator underlying_iterator;

  underlying_iterator it;
  underlying_iterator end;

  explicit dynamic_cast_filtering_iterator(
                              underlying_iterator _it,
                              underlying_iterator _end)
      : it(_it), end(_end) {
    // advance to first valid position
    while (it != end && operator*() == NULL) { ++it; }
  }

  pointer  operator*()  const { return dynamic_cast<pointer>(*it); }
  pointer* operator->() const { return &operator*(); }

  // preincrement
  Self& operator++() { // advance to next valid position
     do { ++it; } while (it != end && operator*() == NULL); }

  // postincrement
  Self operator++(int) { Self tmp = *this; ++*this; return tmp; }

  bool operator==(const Self& other) const {
    return it == other.it;
  }
};

} // namespace foster

#endif
