// Copyright (c) 2018 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/TimingsRepository.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterErrorHandling.h"
#include "parse/ParsingContext.h"

#include "_generated_/fosterLexer.h"
#include "_generated_/fosterParser.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FileSystem.h"

#include <iostream>
#include <string>
#include <map>
#include <queue>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;
using namespace llvm;

#define DEBUG_TYPE "foster"

static cl::opt<string>
optInputPath(cl::Positional, cl::desc("<input file>"));

static cl::opt<bool>
optIncludeTokenText("token-text",
  cl::desc("[foster] Include token text (for debugging purposes)"));


std::string str(pANTLR3_STRING pstr) {
  return string((const char*)pstr->chars);
}

string str(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) return "<nil tok>";

  switch (tok->type) {
    case ANTLR3_TEXT_NONE: return "none";
    case ANTLR3_TEXT_CHARP: return string((const char*)tok->tokText.chars);
    case ANTLR3_TEXT_STRING: return str(tok->tokText.text);
  }

  pANTLR3_STRING pstr = tok->toString(tok);
  if (pstr) {
    return str(pstr);
  } else {
    char buf[80];
    sprintf(buf, "<str(tok) failed, type = %d>", tok->type);
    return string(buf);
  }
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

/*
std::string contentsOfDoubleQuotedStringWithoutQuotes(pTree t) {
  std::string s = textOf(t);
  ASSERT(s.size() >= 2);
  ASSERT(s[0] == '"');
  ASSERT(s[1] != '"');
  return std::string(s.begin() + 1, s.end() - 1);
}
*/

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

namespace foster {

  //int gNumTokensSeen = 0;

  struct FosterIndentingTokenSource : ANTLR3_TOKEN_SOURCE {
    pANTLR3_TOKEN_SOURCE originalSource;
  };

  // The token source produces hidden tokens as well as non-hidden tokens;
  // it's the token stream which wraps the token source that filters out
  // hidden tokens.
  //
  // We can record interesting tokens (like comments, which are type 98)
  // or implement Haskell-like layout rules.
  //
  // See also http://meri-stuff.blogspot.com/2012/09/tackling-comments-in-antlr-compiler.html
  //
  // If the first token in the file is a comment, it will start at char -1.
  pANTLR3_COMMON_TOKEN fosterNextTokenFunc(pANTLR3_TOKEN_SOURCE tokenSource) {
    FosterIndentingTokenSource* s = (FosterIndentingTokenSource*) tokenSource;
    pANTLR3_COMMON_TOKEN tok = s->originalSource->nextToken(s->originalSource);

    //++gNumTokensSeen;

    if (tok->channel == 0) {
      ParsingContext::sawNonHiddenToken();
    }
    if (tok->channel != 0) {
      if (tok->type == NL
       || tok->type == LINE_COMMENT
       || tok->type == NESTING_COMMENT) {
        ParsingContext::sawHiddenToken(tok); // note: WS not included.
      } else if (tok->type == WS) {
         // do nothing
      } else {
        EDiag() << "saw hidden token that was not a newline or a line/nesting comment; type = " << tok->type;
      }

#ifdef ANTLR3_USE_64BIT
#define A3_MARKER_d PRId64
#else
#define A3_MARKER_d "d"
#endif
      if (false) {
        pANTLR3_STRING txt = tok->getText(tok);
        printf("FITS token: channel %d, index %" A3_MARKER_d ", type %3d, line %2d, char %2d, text '%s'\n",
                tok->channel, tok->index, tok->type, tok->line, tok->charPosition,
                        (tok->type == NL)
                                ? "\\n"
                                : (const char*) txt->chars);
      }
    }

    return tok;
  }


} // namespace foster

void dumpTokens(const foster::InputFile& infile) {
  auto buf = infile.getBuffer()->getMemoryBuffer();
  auto filepath = infile.getPath();
  auto input = antlr3StringStreamNew(
                                (pANTLR3_UINT8) buf->getBufferStart(),
                                                ANTLR3_ENC_8BIT,
                                (ANTLR3_UINT32) buf->getBufferSize(),
                                (pANTLR3_UINT8) const_cast<char*>(filepath.c_str()));
  auto lxr = fosterLexerNew(input);
  auto tsr = TOKENSOURCE(lxr);

  pANTLR3_COMMON_TOKEN tok = NULL;
  bool first = true;
  int textOffset = 0;
  do {
    tok = tsr->nextToken(tsr);
    auto txt = tok->getText(tok);
    std::string text((const char*)txt->chars, txt->len);
    int startLine = tok->getLine(tok);
    int startCol  = tok->getCharPositionInLine(tok);
    int endLine = startLine;
    int endCol = startCol;
    if (first) {
      startCol = 0; // For some reason ANTLR initializes the first token's column to -1
      first = false; }
    for (unsigned i = 0; i < txt->len; ++i) {
      if (txt->chars[i] == '\n' && txt->len > 1) {
        ++endLine; endCol = 0;
      } else {
        ++endCol;
      }
    }
    llvm::outs() << "((type " << tok->getType(tok) << ") "
                 << "(channel " << tok->getChannel(tok) << ") "
                 << "(range " << startLine << " "
                              << startCol << " "
                              << endLine << " "
                              << endCol << " "
                 << ")" << ")";
    llvm::outs() << " (offlen " << textOffset << " " << txt->len << ")";
    if (optIncludeTokenText) { llvm::outs() << ":" << text; }
    llvm::outs() << "\n";

    textOffset += txt->len;
  } while (tok != &tsr->eofToken);

  //tsr ->free (tsr);  tsr = NULL;
  lxr->free  (lxr);  lxr = NULL;
}

int main(int argc, char** argv) {
  cl::ParseCommandLineOptions(argc, argv, "Foster tokenizer reference\n");
  const foster::InputFile infile(optInputPath);
  dumpTokens(infile);
  return 0;
}
