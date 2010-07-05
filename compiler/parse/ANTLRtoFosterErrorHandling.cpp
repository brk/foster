// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "parse/ANTLRtoFosterErrorHandling.h"
#include "SourceRange.h"

#include <antlr3.h>

#include <cassert>
#include <string>
#include <sstream>
#include <iostream>

using std::string;

// Function pointer typedef, in case you've never seen the syntax before.
typedef void		(*displayRecognitionErrorFunc)
  (struct ANTLR3_BASE_RECOGNIZER_struct * recognizer,
      pANTLR3_UINT8 * tokenNames);

namespace foster {

// Keep a backup copy of the function pointer that ANTLR3C provides
// to print default error messages; if we can't print anything better,
// we'll fall back to displaying ANTLR's default.
displayRecognitionErrorFunc sgDefaultDRE;

// Handler functions should return false to prevent default ANTLR printouts.
bool handleMissingToken(pANTLR3_EXCEPTION ex, pANTLR3_UINT8* tokenNames);
bool handleNoViableAlt(pANTLR3_EXCEPTION ex, pANTLR3_UINT8* tokenNames);

// This function will get called when ANTLR's parser runs into a problem.
// If we can't print a good error message, we'll simply defer to the
// default ANTLR error message display routine.
static void	customDisplayRecognitionErrorFunc
  (struct ANTLR3_BASE_RECOGNIZER_struct * recognizer,
      pANTLR3_UINT8 * tokenNames) {

  assert(recognizer->type == ANTLR3_TYPE_PARSER);

  bool doDefault = true;
  pANTLR3_EXCEPTION ex = recognizer->state->exception;

  switch (ex->type) {
    case ANTLR3_MISSING_TOKEN_EXCEPTION:
      doDefault = handleMissingToken(ex, tokenNames);
      break;
    case ANTLR3_NO_VIABLE_ALT_EXCEPTION:
      doDefault = handleNoViableAlt(ex, tokenNames);
      break;
    default:
      break;
  }

  if (doDefault) {
    sgDefaultDRE(recognizer, tokenNames);
  }
}

void installRecognitionErrorFilter(pANTLR3_BASE_RECOGNIZER recognizer) {
  sgDefaultDRE = recognizer->displayRecognitionError;
  recognizer->displayRecognitionError =
        customDisplayRecognitionErrorFunc;
}

/////////////////////////////////////////////////////////////////////

inline SourceLocation advanceColumn(foster::SourceLocation s, int n) {
  return SourceLocation(s.line, s.column + n);
}

bool handleMissingToken(pANTLR3_EXCEPTION ex, pANTLR3_UINT8* tokenNames) {
  pANTLR3_COMMON_TOKEN tok = (pANTLR3_COMMON_TOKEN) ex->token;

  SourceLocation errStart(ex->line - 1, ex->charPositionInLine);
  string tokenText;
  bool isPhysicalToken = false;

  if (ex->expecting == ANTLR3_TOKEN_EOF) {
    tokenText = "<EOF>";
  } else if (!tokenNames) {
    std::stringstream ss; ss << "<token ID " << ex->expecting << ">";
    tokenText = ss.str();
  } else {
    tokenText = string((const char*)tokenNames[ex->expecting]);
  }

  SourceLocation errEnd
     = advanceColumn(errStart, isPhysicalToken ? tokenText.size() : 1);

  SourceRange r(gInputFile, errStart, errEnd);
  std::cerr << "Warning: inserted missing " << tokenText << ":\n\n"
            << r << std::endl;
  return false;
}

int getFirstNonWhitespacePosition(llvm::StringRef line) {
  int i = 0, e = line.size();
  while (i < e && isspace(line[i])) { ++i; }
  return i;
}

const char* describeApproximateStartPosition(const SourceRange& r) {
  llvm::StringRef line = r.source->getLine(r.begin.line);
  int lineStart = getFirstNonWhitespacePosition(line);
  float lineLength = (std::min)(1.0f, float(line.size() - lineStart));
  float percentThroughLine = 100.0f * float(r.begin.column - lineStart) / lineLength;
  if (percentThroughLine < 30.0f) {
    return "start";
  } else if (percentThroughLine < 70.0f) {
    return "middle";
  } else {
    return "end";
  }
}

bool handleNoViableAlt(pANTLR3_EXCEPTION ex, pANTLR3_UINT8* tokenNames) {
  pANTLR3_COMMON_TOKEN tok = (pANTLR3_COMMON_TOKEN) ex->token;

  SourceLocation errStart(ex->line - 1, ex->charPositionInLine);
  string tokenText;
  bool isPhysicalToken = false;

  if (ex->expecting == ANTLR3_TOKEN_EOF) {
    tokenText = "<EOF>";
  } else if (!tokenNames) {
    std::stringstream ss; ss << "<token ID " << ex->expecting << ">";
    tokenText = ss.str();
  } else if (tok) {
    tokenText = string((const char*)tok->getText(tok)->chars);
    isPhysicalToken = true;
  } else {
    tokenText = string((const char*)tokenNames[ex->expecting]);
    isPhysicalToken = true;
  }

  SourceLocation errEnd
     = advanceColumn(errStart, isPhysicalToken ? tokenText.size() : 1);

  SourceRange r(gInputFile, errStart, errEnd);
  const char* approxPosition = describeApproximateStartPosition(r);
  std::cerr << r.source->getFilePath() << ":"
            << "error: got stuck parsing near the " << approxPosition
            << " of line " << ex->line << ":\n\n"
            << r << std::endl;
  if (tok) {
    //std::cerr << tok->toString(tok)->chars << std::endl;
  }
  return false;
}

} // namespace foster

