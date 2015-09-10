// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PROTOBUF_TO_LLEXPR_H
#define FOSTER_PROTOBUF_TO_LLEXPR_H

struct LLModule;

namespace foster {

namespace bepb {
  class Module;
} // namespace foster::bepb

LLModule* LLModule_from_pb(const bepb::Module&);

}

#endif
