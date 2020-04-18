// Copyright (c) 2020 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/LLVMUtils.h"

#include "parse/ANTLRtoFosterAST.h"

#include <iostream>

// Usage:
//        tokendump-antlr <file.foster>
// Input: a path to a Foster source file.
//
// Prints a description of each token in the given source file.

int main(int argc, char** argv) {
    if (argc != 2) {
        std::cerr << "Need an input file name\n";
        return 1;
    }
    std::string inpath = argv[1];
    foster::validateInputFile(inpath);
    const foster::InputFile infile(inpath);
    foster::dumpModuleTokens(infile);
    return 0;
}
