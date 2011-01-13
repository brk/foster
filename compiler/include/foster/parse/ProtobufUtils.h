// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#ifndef FOSTER_PROTOBUF_UTILS_H
#define FOSTER_PROTOBUF_UTILS_H

#include <string>

class ModuleAST;

namespace foster {
  namespace pb {
    class SourceModule;
  }
}

ModuleAST* readSourceModuleFromProtobuf(const std::string& pathstr,
                                        foster::pb::SourceModule& out_sm);

void dumpModuleToProtobuf(ModuleAST* mod, const std::string& filename);

#endif
