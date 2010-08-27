// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/Assert.h"
#include "base/SourceRange.h"
#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "parse/ANTLRtoFosterErrorHandling.h"

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
bool handleNoViableAlt(pANTLR3_EXCEPTION, const string&, const SourceRange&);
bool handleGenericError(pANTLR3_EXCEPTION, const string&, const SourceRange&);
bool handleMissingToken(pANTLR3_EXCEPTION, const string&, const SourceRange&);
bool handleUnwantedToken(pANTLR3_EXCEPTION, const string&, const SourceRange&);
bool handleMismatchedToken(pANTLR3_EXCEPTION, const string&, const SourceRange&);

inline SourceLocation advanceColumn(foster::SourceLocation s, int n) {
  return SourceLocation(s.line, s.column + n);
}

bool computeTokenText(string& outTokenText,
                      pANTLR3_EXCEPTION ex,
                      pANTLR3_UINT8* tokenNames) {
  pANTLR3_COMMON_TOKEN tok = (pANTLR3_COMMON_TOKEN) ex->token;

  bool isPhysicalToken = false;

  if (ex->expecting == ANTLR3_TOKEN_EOF) {
    outTokenText = "<EOF>";
  } else if (!tokenNames) {
    std::stringstream ss; ss << "<token ID " << ex->expecting << ">";
    outTokenText = ss.str();
  } else if (tok && ex->type != ANTLR3_MISSING_TOKEN_EXCEPTION) {
    // The text for the physical token in the case of missing tokens
    // is "missing 'TOKEN'" but we just want "TOKEN".
    outTokenText = string((const char*)tok->getText(tok)->chars);
    std::cout << "tok : " << outTokenText << "; tokenNames: "
              << (const char*) tokenNames[ex->expecting] << std::endl;
    isPhysicalToken = true;
  } else {
    // TODO names are e.g. ')' instead of ),
    // which messes up highlighting
    outTokenText = string((const char*)tokenNames[ex->expecting]);
    std::cout << "tokenNames: " << outTokenText << std::endl;
    isPhysicalToken = true;
  }

  return isPhysicalToken;
}

SourceRange computeSourceRange(pANTLR3_EXCEPTION ex,
                               const string& tokenText,
                               bool isPhysicalToken) {
  //std::cout << "token text is " << tokenText
  //            << ", start col is " << ex->charPositionInLine << std::endl;
  SourceLocation errStart(ex->line - 1, ex->charPositionInLine);
  SourceLocation errEnd
     = advanceColumn(errStart, isPhysicalToken ? tokenText.size() : 1);
  return SourceRange(gInputFile, errStart, errEnd);
}

// This function will get called when ANTLR's parser runs into a problem.
// If we can't print a good error message, we'll simply defer to the
// default ANTLR error message display routine.
static void	customDisplayRecognitionErrorFunc
  (struct ANTLR3_BASE_RECOGNIZER_struct * recognizer,
      pANTLR3_UINT8 * tokenNames) {

  ASSERT(recognizer->type == ANTLR3_TYPE_PARSER);

  bool doDefault = true;
  pANTLR3_EXCEPTION ex = recognizer->state->exception;

  string tokenText;
  bool isPhysicalToken = computeTokenText(tokenText, ex, tokenNames);
  SourceRange sourceRange = computeSourceRange(ex, tokenText, isPhysicalToken);

  switch (ex->type) {
    case ANTLR3_MISSING_TOKEN_EXCEPTION:
      doDefault = handleMissingToken(ex, tokenText, sourceRange);
      break;
    case ANTLR3_NO_VIABLE_ALT_EXCEPTION:
      doDefault = handleNoViableAlt(ex, tokenText, sourceRange);
      break;
    case ANTLR3_MISMATCHED_TOKEN_EXCEPTION:
      doDefault = handleMismatchedToken(ex, tokenText, sourceRange);
      break;
    case ANTLR3_RECOGNITION_EXCEPTION:
      doDefault = handleGenericError(ex, tokenText, sourceRange);
      break;
    case ANTLR3_UNWANTED_TOKEN_EXCEPTION:
      doDefault = handleUnwantedToken(ex, tokenText, sourceRange);
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

bool handleMissingToken(pANTLR3_EXCEPTION ex,
                        const string& tokenText,
                        const SourceRange& r) {
  std::cerr << "Warning: inserted missing " << tokenText << ":\n\n"
            << r << std::endl;
  return false;
}

/////////////////////////////////////////////////////////////////////

int getFirstNonWhitespacePosition(llvm::StringRef line) {
  int i = 0, e = line.size();
  while (i < e && isspace(line[i])) { ++i; }
  return i;
}

const char* describeApproximateStartPosition(const SourceRange& r) {
  if (!r.source || !r.source->getBuffer()) {
    return "???";
  }

  llvm::StringRef line = r.source->getBuffer()->getLine(r.begin.line);
  int lineStart = getFirstNonWhitespacePosition(line);
  float lineLength = (std::min)(1.0f, float(line.size()    - lineStart));
  float percentThroughLine = 100.0f * float(r.begin.column - lineStart)
                                    / lineLength;
  if (percentThroughLine < 30.0f) {
    return "start";
  } else if (percentThroughLine < 70.0f) {
    return "middle";
  } else {
    return "end";
  }
}

bool handleNoViableAlt(pANTLR3_EXCEPTION ex,
                        const string& tokenText,
                        const SourceRange& r) {
  const char* approxPosition = describeApproximateStartPosition(r);
  std::cerr << r.source->getShortSuffixPath() << ":"
            << "error: got stuck parsing near the " << approxPosition
            << " of line " << (r.begin.line + 1) << ":\n\n"
            << r << std::endl;
  return false;
}

/////////////////////////////////////////////////////////////////////

bool handleMismatchedToken(pANTLR3_EXCEPTION ex,
                        const string& tokenText,
                        const SourceRange& r) {
  const char* approxPosition = describeApproximateStartPosition(r);
  std::cerr << r.source->getShortSuffixPath() << ":"
            << "error: unexpected token near the " << approxPosition
            << " of line " << (r.begin.line + 1) << ":\n\n"
            << r << std::endl;
  return false;
}

/////////////////////////////////////////////////////////////////////

bool handleGenericError(pANTLR3_EXCEPTION ex,
                        const string& tokenText,
                        const SourceRange& r) {
  const char* approxPosition = describeApproximateStartPosition(r);
  std::cerr << r.source->getShortSuffixPath() << ":"
            << "generic error: " << ((const char*) ex->message)
            << " near the " << approxPosition
            << " of line " << (r.begin.line + 1) << ":\n\n"
            << r << std::endl;
  return false;
}

/////////////////////////////////////////////////////////////////////

bool handleUnwantedToken(pANTLR3_EXCEPTION ex,
                        const string& tokenText,
                        const SourceRange& r) {
  const char* approxPosition = describeApproximateStartPosition(r);
  std::cerr << r.source->getShortSuffixPath() << ":"
            << "error: " << ((const char*) ex->message)
            << " " << tokenText 
            << " near the " << approxPosition
            << " of line " << (r.begin.line + 1) << ":\n\n"
            << r << std::endl;
  return false;
}
} // namespace foster



