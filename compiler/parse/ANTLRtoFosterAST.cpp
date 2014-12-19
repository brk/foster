// Copyright (c) 2009 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include "base/InputFile.h"
#include "base/InputTextBuffer.h"
#include "base/strings/utf_string_conversion_utils.h"
#include "base/third_party/icu/icu_utf.h"

#include "parse/ANTLRtoFosterAST.h"
#include "parse/FosterAST.h"
#include "parse/FosterTypeAST.h"
#include "parse/ANTLRtoFosterErrorHandling.h"
#include "parse/ParsingContext.h"

#include "_generated_/fosterLexer.h"
#include "_generated_/fosterParser.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/ADT/SmallString.h"
#include "llvm/Support/DataTypes.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/FileSystem.h"

#include "city.h"
#include "pystring/pystring.h"

#include <iostream>
#include <string>
#include <map>
#include <queue>
#include <vector>
#include <sstream>
#include <cassert>

using std::string;

using foster::EDiag;
using foster::DDiag;
using foster::show;
using foster::ParsingContext;

#define DEBUG_TYPE "foster"

KindAST* getDefaultKind() { return new BaseKindAST(BaseKindAST::KindType); }
KindAST* getBoxedKind() { return new BaseKindAST(BaseKindAST::KindBoxed); }

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

TypeAST* TypeAST_from(pTree tree);
void display_pTree(pTree t, int nspaces);

size_t getChildCount(pTree tree) {
  return static_cast<size_t>(tree->getChildCount(tree));
}

pTree child(pTree tree, int i) {
  ASSERT(tree) << "can't take child of null pTree!";
  return (pTree) tree->getChild(tree, i);
}

string textOf(pTree tree) {
  ASSERT(tree) << "can't get text of null pTree!";
  return str(tree->getText(tree));
}

string textOfVar(pTree tree) { return textOf(child(tree, 0)); }

int typeOf(pTree tree) { return tree->getType(tree); }

pANTLR3_COMMON_TOKEN getStartToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getStartToken(tree);
  if (tok) return tok;

  // Some nodes we're okay with having no token info for...
  /*
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }
  */

  // Usually, ANTLR will have annotated the tree directly;
  // however, in some cases, only subtrees will have token
  // information. In such cases, we search along the edge of the
  // parse tree to find the first edge child with token info.
  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, 0);
    tok = ParsingContext::getStartToken(node);
  }
  if (!tok) {
    llvm::outs() << "Warning: unable to find start token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree
              << " , " << typeOf(tree) << "\n";
  }
  return tok;
}

pANTLR3_COMMON_TOKEN getEndToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = ParsingContext::getEndToken(tree);
  if (tok) return tok;

  /*
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }
  */

  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, getChildCount(node) - 1);
    tok = ParsingContext::getEndToken(node);
  }
  if (!tok) {
    llvm::outs() << "Warning: unable to find end token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree << "\n";
  }
  return tok;
}

foster::SourceLocation getStartLocation(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) { return foster::SourceLocation::getInvalidLocation(); }
  // ANTLR gives source locations starting from 1; we want them from 0
  return foster::SourceLocation(tok->getLine(tok) - 1,
                                tok->getCharPositionInLine(tok));
}

foster::SourceLocation getEndLocation(pANTLR3_COMMON_TOKEN tok) {
  if (!tok) {
    return foster::SourceLocation::getInvalidLocation();
  }
  return foster::SourceLocation(tok->getLine(tok) - 1,
      tok->getCharPositionInLine(tok) + tok->getText(tok)->len);
}

foster::SourceRange rangeFrom(pTree start, pTree end) {
  pANTLR3_COMMON_TOKEN stok = getStartToken(start);
  pANTLR3_COMMON_TOKEN etok = getEndToken(end);
  return foster::SourceRange(foster::gInputFile,
      getStartLocation(stok),
      getEndLocation(etok),
      foster::gInputTextBuffer);
}

foster::SourceRange rangeOf(pTree tree) {
  return rangeFrom(tree, tree);
}

foster::SourceRange rangeFrom(ExprAST* a, ExprAST* b) {
  if (a && b) {
    foster::SourceRange ar = a->sourceRange;
    foster::SourceRange br = b->sourceRange;
    ASSERT(ar.source == br.source);
    return foster::SourceRange(ar.source, ar.begin, br.end);
  } else if (a) {
    foster::SourceRange ar = a->sourceRange;
    return foster::SourceRange(ar.source, ar.begin,
                   foster::SourceLocation::getInvalidLocation());
  } else {
    return foster::SourceRange::getEmptyRange();
  }
}


string spaces(int n) { return (n > 0) ? string(n, ' ') : ""; }

void display_pTree(pTree t, int nspaces) {
  if (!t) {
    llvm::outs() << spaces(nspaces) << "<NULL tree>" << "\n";
    return;
  }

  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::stringstream ss;
  ss << spaces(nspaces) << "<" << text << "; ";
  llvm::outs() << ss.str() << spaces(100 - ss.str().size())
                << token << " @ " << t;
  llvm::outs() << " (";
  llvm::outs() << (ParsingContext::getStartToken(t) ? '+' : '-');
  llvm::outs() << (ParsingContext::getEndToken(t)   ? '+' : '-');
  llvm::outs() << ")" << "\n";
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  llvm::outs() << spaces(nspaces) << "/" << text << ">" << "\n";
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

const char* getDefaultCallingConvParse() {
  //foster::DDiag() << "getDefaultCallingConvParse()";
  return foster::kDefaultFnLiteralCallingConvention;
}

////////////////////////////////////////////////////////////////////

ExprAST* parseNumFrom(pTree t) {
  ASSERT(textOf(t) == "LIT_NUM")
            << "parseIntFrom() called on non-LIT_NUM token " << textOf(t)
            << show(rangeOf(t));

  std::string alltext = textOf(child(t, 0));

  if (pystring::count(alltext, ".") > 0) {
    ASSERT(alltext.find_first_of("abcdfABCDF_") == string::npos)
              << "rationals should not contain hex digits or a base specifier"
              << "; saw " << alltext;

    if (alltext.find_first_of("eE") != string::npos) {
      ASSERT(alltext.find_first_of("eE") > alltext.find_first_of("."))
              << "e/E should only appear in rational as exponent specifier";
    }
    return new RatAST(alltext, rangeOf(t));
  } else {
    return new IntAST(alltext, rangeOf(t));
  }
}

////////////////////////////////////////////////////////////////////

ExprAST* ExprAST_from(pTree tree);
std::vector<TypeAST*> getTypes(pTree tree);

Exprs getExprs(pTree tree) {
  Exprs f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(ExprAST_from(child(tree, i)));
  }
  return f;
}

enum StmtTag { StmtExprs, StmtLetBinds, StmtRecBinds };

string str(char c) { return std::string(1, c); }

string str(StmtTag t) {
  if (t == StmtRecBinds) return "StmtRecBinds";
  if (t == StmtLetBinds) return "StmtLetBinds";
  if (t == StmtExprs)    return "StmtExprs";
  return "UnknownStmtTag";
}

string str(const SourceRange& sr) {
  string s;
  llvm::raw_string_ostream ss(s); ss << sr;
  return s;
}

StmtTag classifyStmt(pTree t) {
  if (typeOf(t) == ABINDING) {
    if (getChildCount(t) == 2) {
      return StmtRecBinds;
    } else {
      return StmtLetBinds;
    }
  } else {
    return StmtExprs;
  }
}

foster::SourceRange rangeOfTrees(const std::vector<pTree>& v) {
  return rangeFrom(v.front(), v.back());
}

Pattern* parsePattern(pTree t);
Pattern* parsePatternAtom(pTree t);

Binding parseBinding(pTree tree) {
  return Binding(parsePatternAtom(child(tree, 0)), ExprAST_from(child(tree, 1)));
}

ExprAST* parseStmts_seq(const std::vector<pTree>& v, ExprAST* mb_last) {
  assert(!v.empty());
  Exprs e;
  for (unsigned i = 0; i < v.size(); ++i) { e.push_back(ExprAST_from(v[i])); }
  if (mb_last) e.push_back(mb_last);
  return new SeqAST(e, rangeOfTrees(v));
}

// ugh...
ExprAST* parseStmts(pTree tree) {
  if (getChildCount(tree) == 1 && typeOf(child(tree, 0)) != ABINDING) {
    return ExprAST_from(child(tree, 0));
  }

  std::vector<std::pair<StmtTag, std::vector<pTree> > > sections;

  for (unsigned i = 0; i < getChildCount(tree);      ) {
    StmtTag t = classifyStmt(child(tree, i));
    std::vector<pTree> section;
    do {
      section.push_back(child(tree, i));
      ++i;
    } while (i < getChildCount(tree) && classifyStmt(child(tree, i)) == t);
    sections.push_back(std::make_pair(t, section));
  }

  ASSERT(!sections.empty());
  if (sections.back().first != StmtExprs) {
    ASSERT(false)
        << "\n\n" << "Statement block should end"
        << " in an expression!" << "\n"
        << show(rangeOf(tree));
  }

  std::vector<pTree>& end_asts = sections.back().second;
  ExprAST* acc = parseStmts_seq(end_asts, NULL);

  // Walk backwards over sections, accumulating.
  for (int i = sections.size() - 2; i >= 0; --i) {
    bool isRec = sections[i].first == StmtRecBinds;
    std::vector<Binding> bindings;

    switch (sections[i].first) {
    case StmtRecBinds: // fallthrough
    case StmtLetBinds:
      for (unsigned x = 0; x < sections[i].second.size(); ++x) {
        pTree c = sections[i].second[x];
        int offset = isRec ? 1 : 0;
        bindings.push_back(parseBinding(child(c, offset)));
      }
      acc = new LetAST(bindings, acc, isRec, rangeOfTrees(sections[i].second));
      break;

    case StmtExprs:
      // accumulator becomes last expr in sequence
      acc = parseStmts_seq(sections[i].second, acc);
      break;
    }
  }

  return acc;
}

ExprAST* parseSeq(pTree tree) {
  return new SeqAST(getExprs(tree), rangeOf(tree));
}

ExprAST* parseParenExpr(pTree tree) {
  return ExprAST_from(child(tree, 0));
}

Formal parseFormal(pTree formal) {
  TypeAST* ty = NULL;
  if (getChildCount(formal) == 2) {
    ty = TypeAST_from(child(formal, 1));
  } else {
    NamedTypeAST* tv = new NamedTypeAST(ParsingContext::freshName(".inferred:\n" + str(rangeOf(formal))),
                                        NULL, rangeOf(formal));
    tv->is_placeholder = true;
    ty = tv;
  }
  return Formal(textOfVar(child(formal, 0)), ty);
}

KindAST* parseKind(pTree t) {
  switch (typeOf(t)) {
  case KIND_TYPE:       return new BaseKindAST(BaseKindAST::KindType);
  case KIND_TYPE_BOXED: return new BaseKindAST(BaseKindAST::KindBoxed);
  }
  ASSERT(false) << "Unknown kind in parseKind()"; return NULL;
}

void parseFormals(std::vector<Formal>& formals, pTree tree) {
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    formals.push_back(parseFormal(child(tree, i)));
  }
}

TypeFormal parseTypeFormal(pTree t, KindAST* defaultKind) {
  std::string varname = textOfVar(child(t, 0));
  KindAST* kind = (getChildCount(t) == 2)
                ? parseKind(child(t, 1))
                : defaultKind;
  return TypeFormal(varname, kind, rangeOf(t));
}

// TYPEVAR_DECL name kind?
std::vector<TypeFormal> parseTyFormals(pTree t, KindAST* defaultKind) {
  std::vector<TypeFormal> names;
  for (size_t i = 0; i < getChildCount(t); ++i) {
    names.push_back(parseTypeFormal(child(t, i), defaultKind));
  }
  return names;
}

std::vector<TypeAST*> noTypes() { std::vector<TypeAST*> types; return types; }

ExprAST* parseTuple(pTree t) {
  if (getChildCount(t) == 1) {
    return ExprAST_from(child(t, 0));
  } return new CallPrimAST("tuple", getExprs(t), noTypes(), rangeOf(t));
}

// ^(VAL_ABS ^(FORMALS formals) ^(MU tyvar_decl*) stmts?)
ValAbs* parseValAbs(pTree tree) {
  std::vector<Formal> formals;
  parseFormals(formals, child(tree, 0));
  std::vector<TypeFormal> tyVarFormals = parseTyFormals(child(tree, 1),
                                                        getDefaultKind());
  const int stmtIndex = 2;
  TypeAST* resultType = NULL;
  ExprAST* resultSeq = getChildCount(tree) == (stmtIndex + 1)
                         ? parseStmts(child(tree, stmtIndex))
                         : new SeqAST(Exprs(), rangeOf(tree));
  return new ValAbs(formals, tyVarFormals, resultSeq, resultType, rangeOf(tree));
}

ExprAST* parseTyCheck(pTree t) {
  ASSERT(getChildCount(t) == 2);
  return new ETypeCheckAST(ExprAST_from(child(t, 0)),
                           TypeAST_from(child(t, 1)),
                           rangeOf(t));
}

// so lame :(
// in particular, we assume the tree is properly structured without checking...
void tryParseOperatorAssocDecl(pTree raw, pTree expli) {
  ASSERT(getChildCount(raw) == 3); // ^(TERM ^(MU opr?) ^(MU phrase) ^(MU binops?))
  pTree rawBinops = child(raw, 2);
  ASSERT(getChildCount(rawBinops) == 4); // ^(MU op1 _ op2 _)
  string o1 = textOf(child(rawBinops, 0));
  string o2 = textOf(child(rawBinops, 2));

  // If this check is removed, note/beware that parseAsTighter(o1, o2)
  // does not imply parseAsLooser(o2, o1)!
  ASSERT(o1 == o2) << "for now, operators must be the same...";

  ASSERT(getChildCount(child(expli, 2)) == 0) << "no binops in explicit parse tree";
  // HUUUUURRRRKKKKKK
  pTree expl = child(child(child(child(child(expli, 1), 0), 0), 0), 0);
  pTree ex   = child(child(child(child(child(expl,  1), 0), 1), 0), 0);
  bool isLeftAssoc = getChildCount(ex) > 1;
  if (isLeftAssoc) {
    ParsingContext::parseAsTighter(o1, o2);
  } else {
    ParsingContext::parseAsLooser(o1, o2);
  }
}

// #associate e1 as e2 in e3 end
// but it's really
// #associate _ `o1` _ `o2` _ as (ox _ (oy _ _)) in e3 end
// ... at least for now...
// ^(PARSE_DECL e1 e2 stmts)
ExprAST* parseParseDecl(pTree t) {
  ASSERT(getChildCount(t) == 3);

  ParsingContext::pushNewContext();
  tryParseOperatorAssocDecl(child(t, 0), child(t, 1));
  ExprAST* e = parseStmts(child(t, 2));
  ParsingContext::popCurrentContext();
  return e;
}

std::vector<Binding> parseBindings(pTree tree) {
  std::vector<Binding> bindings;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    bindings.push_back(parseBinding(child(tree, i)));
  }
  return bindings;
}

// ^(LETS ^(MU binding+) stmts)
ExprAST* parseLets(pTree tree) {
  return new LetAST(parseBindings(child(tree, 0)),
                       parseStmts(child(tree, 1)),
                         false, rangeOf(tree));
}

// ^(LETREC ^(MU binding+) stmts)
ExprAST* parseLetRec(pTree tree) {
  return new LetAST(parseBindings(child(tree, 0)),
                       parseStmts(child(tree, 1)),
                         true,  rangeOf(tree));
}

bool isLexicalOperator(const std::string& text) {
  ASSERT(!text.empty());
  return !isalpha(text[0]); // coincides with fragment IDENT_START
}

VariableAST* parseVarDirect(pTree t) {
  return new VariableAST(textOf(t), NULL, rangeOf(t));
}

std::string parseName(pTree nm) {
  if (typeOf(nm) == QNAME) {
    return textOf(child(nm, 0)) + "." + parseName(child(nm, 1));
  } else {
    return textOf(nm);
  }
}

// t = ^(_NAME name)
VariableAST* parseTermVar(pTree t) {
  return new VariableAST(parseName(child(t, 0)), NULL, rangeOf(t));
}

// ^(IF e stmts stmts)
ExprAST* parseIf(pTree tree) {
  return new IfExprAST(ExprAST_from(child(tree, 0)),
                       parseStmts(child(tree, 1)),
                       parseStmts(child(tree, 2)),
                       rangeOf(tree));
}

// ^(COMPILES e)
ExprAST* parseBuiltinCompiles(pTree t) {
 return new BuiltinCompilesExprAST(ExprAST_from(child(t, 0)), rangeOf(t));
}

ExprAST* parseBool(pTree t) {
  return new BoolAST(textOf(child(t, 0)), rangeOf(t));
}

// ^(STRING type contents)
std::string contentsOfStringWithQuotesAndRawMarker(pTree t) {
  return textOf(child(t, 1));
}

std::string contentsOfDoubleQuotedStringWithoutQuotes(pTree t) {
  std::string s = textOf(t);
  int offset = s[0] == 'r' ? 2 : 1;
  ASSERT(s.size() > (offset + 1));
  return std::string(s.begin() + offset, s.end() - 1);
  EDiag() << "Unable to determine what kind of string this is!" << s << "\n" << show(rangeOf(t));
}

char hexbits(char x) {
  if (isdigit(x)) return (x - '0');
  if (islower(x)) return (x - 'a') + 10;
  if (isupper(x)) return (x - 'A') + 10;
  ASSERT(false) << "can't extract hex bits from char value " << int(x); return 0;
}

// Copied from chromium_base, since they don't export it for some reason.
size_t WriteUnicodeCharacter(uint32_t code_point, std::string* output) {
  if (code_point <= 0x7f) {
    // Fast path the common case of one byte.
    output->push_back(code_point);
    return 1;
  }

  // CBU8_APPEND_UNSAFE can append up to 4 bytes.
  size_t char_offset = output->length();
  size_t original_char_offset = char_offset;
  output->resize(char_offset + CBU8_MAX_LENGTH);

  CBU8_APPEND_UNSAFE(&(*output)[0], char_offset, code_point);

  // CBU8_APPEND_UNSAFE will advance our pointer past the inserted character, so
  // it will represent the new length of the string.
  output->resize(char_offset);
  return char_offset - original_char_offset;
}

// ^(STRING type wholething)
ExprAST* parseString(pTree t) {
  std::string wholething = contentsOfStringWithQuotesAndRawMarker(t);

  std::string quo = textOf(child(t, 0));
  int quotes = (quo == "TDQU" || quo == "TRTK") ? 3 : 1;

  // ANTLR puts us between a rock and a hard place when it comes to handling
  // strings. If we use lexer rules to capture string syntax, ANTLR can enforce
  // but not inform us of the internal structure of a legal string.
  // However, if we use grammar rules, the grammar becomes ambigous
  // (for example, wrapping an ident with quotes changes its parse class).
  // So, we're forced to essentially re-parse the string here, looking for
  // escape codes and such.
  std::string::iterator it = wholething.begin(), end = wholething.end();
  if (wholething[0] == 'r') {
    // Raw string; don't interpret the contents in any way, shape, or form...
    return new StringAST(std::string(wholething.begin() + quotes + 1,
                                     wholething.end()   - quotes), false, rangeOf(t));
  } else {
    bool bytes = wholething[0] == 'b';
    // Non-raw string: walk through it and interpret escape codes.
    std::string parsed; parsed.reserve(wholething.size());
    it += quotes + bytes; end -= quotes;
    while (it != end) {
      if (*it != '\\') {
        if (*it == '\n' && quotes == 1) {
          ASSERT(false) << "embedded newlines not allowed within single-delimiter strings"
                        << show(rangeOf(t));
        }
        if (!(*it == '\n' && bytes)) { // byte literals ignore newlines
          parsed.push_back(*it);
        }
        ++it;
      } else {
        ++it;
        // Escape sequence started...
             if (*it == 't')  { parsed.push_back('\t'); ++it; }
        else if (*it == 'n')  { parsed.push_back('\n'); ++it; }
        else if (*it == 'r')  { parsed.push_back('\r'); ++it; }
        else if (*it == '"')  { parsed.push_back('"'); ++it; }
        else if (*it == '\'') { parsed.push_back('\''); ++it; }
        else if (*it == '\\') { parsed.push_back('\\'); ++it; }
        else if (*it == 'x' && bytes) { ++it;
            // This is appropriate for raw bytes, but not text (Unicode...)
            char c_hi = *it; ++it;
            char c_lo = *it; ++it;
            char x_hi = hexbits(c_hi);
            char x_lo = hexbits(c_lo);
            char byte = ((x_hi << 4) | x_lo);
            parsed.push_back(byte);
        }
        else if (*it == 'u') { ++it;
          if (*it == '{') { ++it;
            // pretty much arbitrary stuff until a matching '}'
            std::string stuff;
            bool looksLikeHex = true;
            while (*it != '}') {
               if (!  isxdigit(*it)) { looksLikeHex = false; }
               stuff.push_back(*it); ++it;
            }
            ++it;

            ASSERT(looksLikeHex) << "Handling arbitrary unicode names is a TODO!"
                    << "\nparsed out:" << stuff
                    << "\n" << show(rangeOf(t));
            ASSERT(stuff.size() <= 6) << "Unicode escapes can have at most 6 hex digits."
                                      << "\n" << show(rangeOf(t));

            uint32_t codepoint = strtol(stuff.c_str(), NULL, 16);
            ASSERT(base::IsValidCharacter(codepoint)) << "Unicode escapes must be valid characters!"
                                                      << "\n" << show(rangeOf(t));
            WriteUnicodeCharacter(codepoint, &parsed);
          } else {
            ASSERT(false) << "Unicode escapes require curly braces."
                          << "\n" << show(rangeOf(t));
          }
        } else {
          ASSERT(false) << "unexpected escape code " << str(*it) << " in string: "
                        << "\n" << wholething
                        << "\n" << spaces(it - wholething.begin()) << "^";
        }
      }
    }
    return new StringAST(parsed, bytes, rangeOf(t));
  }
}

std::vector<Pattern*> noPatterns() { std::vector<Pattern*> f; return f; }

std::vector<Pattern*> getPatterns(pTree tree) {
  std::vector<Pattern*> f;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    f.push_back(parsePattern(child(tree, i)));
  }
  return f;
}

std::vector<Pattern*> getPatternAtomsFrom1(pTree tree) {
  std::vector<Pattern*> f;
  for (size_t i = 1; i < getChildCount(tree); ++i) {
    f.push_back(parsePatternAtom(child(tree, i)));
  }
  return f;
}

Pattern* parseTuplePattern(pTree t) {
  if (getChildCount(t) == 1) {
    return parsePattern(child(t, 0));
  } return new TuplePattern(rangeOf(t), getPatterns(t));
}

// ^(CTOR x)
VariableAST* parseCtor(pTree t) {
  ASSERT(typeOf(t) == CTOR);
  return parseTermVar(child(t, 0));
}

ExprAST* parseAtom(pTree tree);
Pattern* parsePatternAtom(pTree t) {

  int token = typeOf(t);
  if ((token == PHRASE)
    || (token == TERM)) { ASSERT(false); }

    if (token == CTOR ) { return new CtorPattern(rangeOf(t), textOfVar(child(t, 0)), noPatterns()); }
  if (token == WILDCARD) { return new WildcardPattern(rangeOf(t)); }
  if (token == TUPLE)    { return parseTuplePattern(t); }
  if (token == TERMNAME) { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_VAR, parseTermVar(t)); }
  if (token == LIT_NUM)  { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_NUM, parseAtom(t)); }
  if (token == BOOL   )  { return new LiteralPattern(rangeOf(t), LiteralPattern::LP_BOOL, parseAtom(t)); }
  //if (token == STRING ) { return new LiteralPattern(LiteralPattern::LP_STR, parseAtom(t)); }

  display_pTree(t, 2);
  ASSERT(false) << "returning NULL Pattern for parsePatternAtom token " << str(t->getToken(t));
  return NULL;
}

// ^(MU patom) (may be ctor)
// ^(MU pctor patom*)
Pattern* parsePattern(pTree t) {
  if (getChildCount(t) == 1) {
    return parsePatternAtom(child(t, 0));
  } return new CtorPattern(rangeOf(t), parseCtor(child(t, 0))->getName(),
                           getPatternAtomsFrom1(t));
}

// ^(CASE p e? stmts)
CaseBranch* parseCaseBranch(pTree t) {
  if (getChildCount(t) == 3) {
    return new CaseBranch(parsePattern(child(t, 0)),
                          ExprAST_from(child(t, 1)),
                          parseStmts(  child(t, 2)));
  } else {
    return new CaseBranch(parsePattern(child(t, 0)),
                          NULL,
                          parseStmts(  child(t, 1)));
  }
}

// ^(CASE e pmatch+)
ExprAST* parseCase(pTree t) {
  ExprAST* scrutinee = ExprAST_from(child(t, 0));
  std::vector<CaseBranch*> branches;
  for (size_t i = 1; i < getChildCount(t); ++i) {
    branches.push_back(parseCaseBranch(child(t, i)));
  }
  return new CaseExpr(scrutinee, branches, rangeOf(t));
}

ExprAST* parseAtom(pTree tree) {
  int token = typeOf(tree);

  if (token == VAL_ABS)  { return parseValAbs(tree); }
  if (token == LETS)     { return parseLets(tree); }
  if (token == LETREC)   { return parseLetRec(tree); }
  if (token == TUPLE)    { return parseTuple(tree); }
  if (token == TYANNOT)  { return parseTyCheck(tree); }
  if (token == PARSE_DECL){return parseParseDecl(tree); }
  if (token == TERMNAME) { return parseTermVar(tree); }
  if (token == LIT_NUM)  { return parseNumFrom(tree); }
  if (token == IF)       { return parseIf(tree); }
  if (token == COMPILES) { return parseBuiltinCompiles(tree); }
  if (token == CASE)     { return parseCase(tree); }
  if (token == CTOR)     { return parseCtor(tree); }
  if (token == BOOL)     { return parseBool(tree); }
  if (token == STRING)   { return parseString(tree); }

  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL ExprAST for parseAtom token " << str(tree->getToken(tree));
  return NULL;
}

ExprAST* parseSubscript(ExprAST* base, pTree tree) {
  return CallPrimAST::two("subscript", base, ExprAST_from(child(tree, 0)), rangeOf(tree));
}

ExprAST* parseDeref(ExprAST* base, pTree tree) {
  return CallPrimAST::one("deref", base, rangeOf(tree));
}

// ^(VAL_TYPE_APP t*)
ExprAST* parseValTypeApp(ExprAST* base, pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    types.push_back(TypeAST_from(child(tree, i)));
  }
  return new ETypeAppAST(NULL, base, types, rangeOf(tree));
}

// ^(VAL_APP)
ExprAST* parseValApp(ExprAST* base, pTree tree) {
  ASSERT(getChildCount(tree) == 0);
  return new CallAST(base, Exprs(), rangeOf(tree));
}

ExprAST* parseSuffix(ExprAST* base, pTree tree) {
  int token = typeOf(tree);

  if (token == SUBSCRIPT) { return parseSubscript(base, tree); }
  if (token == DEREF)     { return parseDeref(base, tree); }
  if (token == VAL_APP)   { return parseValApp(base, tree); }
  if (token == VAL_TYPE_APP) { return parseValTypeApp(base, tree); }
  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL ExprAST for parseSuffix token " << str(tree->getToken(tree));
  return NULL;
}

// ^(LVALUE atom suffix*)
ExprAST* parseLValue(pTree tree) {
  ExprAST* acc = parseAtom(child(tree, 0));
  for (size_t i = 1; i < getChildCount(tree); ++i) {
     acc = parseSuffix(acc, child(tree, i));
  }
  return acc;
}

ExprAST* parseCall(pTree tree) {
  bool is_negated = typeOf(child(tree, 0)) == MINUS;
  unsigned  index = is_negated ? 1 : 0;

  if (is_negated) {
    EDiag() << "no support yet for negated expressions" << show(rangeOf(tree));
    // In particular, we need a better story about overloading,
    // so we can support, e.g.,  -(a *f64 b) rather than ((0.0 -f64 a) *f64 b).
    return NULL;
  }

  ExprAST* base = parseLValue(child(tree, index));
  if (getChildCount(tree) == index + 1 && !is_negated) { return base; }
  Exprs exprs;
  for (size_t i = index + 1; i < getChildCount(tree); ++i) {
    exprs.push_back(parseLValue(child(tree, i)));
  }
  return new CallAST(base, exprs, rangeOf(tree));
}

ExprAST* parsePrimApp(pTree tree) {
  ASSERT(getChildCount(tree) >= 1) << "prim app with no name?!?";
  string name = textOf(child(tree, 0));

  std::vector<TypeAST*> types;
  // ^(MU ^(VAL_TYPE_APP ...)?)
  pTree _mu = child(tree, 1);
  if (getChildCount(_mu) == 1) {
    pTree _tyapp = child(_mu, 0);
    for (size_t i = 0; i < getChildCount(_tyapp); ++i) {
      types.push_back(TypeAST_from(child(_tyapp, i)));
    }
  }

  Exprs exprs;
  for (size_t i = 2; i < getChildCount(tree); ++i) {
    exprs.push_back(parseLValue(child(tree, i)));
  }
  return new CallPrimAST(name, exprs, types, rangeOf(tree));
}

// ^(PHRASE '-'? lvalue+) | ^(PRIMAPP id lvalue*)
ExprAST* parsePhrase(pTree tree) {
  int token = typeOf(tree);
  if (token == PHRASE) { return parseCall(tree); }
  if (token == PRIMAPP) { return parsePrimApp(tree); }

  display_pTree(tree, 2);
  ASSERT(false) << "Unknown token type in parsePhrase()!" << token;
  return NULL;
}

ExprAST* parseBinops(pTree tree) {
  display_pTree(tree, 2);
  foster::EDiag() << "returning NULL TypeAST for parseBinops token " << str(tree->getToken(tree));
  return NULL;
}

// Returns the punctuation chars at the start of the given string.
// This isn't quite right in the presence of user-defined operators,
// since we'd want .e.g +++ to behave like +.
std::string oprPrefixOf(std::string s) {
  if (!s.empty() && !ispunct(s[0])) {
    return s; // for "and", "or", etc.
  }
  std::string::iterator b, e;
  b = s.begin(); e = s.end();
  while (b != e && ispunct(*b)) { ++b; }
  return std::string(s.begin(), b);
}

typedef std::pair<VariableAST*, std::string> VarOpPair;

void leftAssoc(std::vector<VarOpPair>& opstack,
               std::vector<ExprAST*>& argstack) {
  ExprAST*  y = argstack.back(); argstack.pop_back();
  ExprAST*  x = argstack.back(); argstack.pop_back();
  VarOpPair p =  opstack.back();  opstack.pop_back();
  const std::string& o = p.second;

  if (o == ">^") {
    // TODO move this switch to desugaring in me.
    argstack.push_back(CallPrimAST::two("store", x, y, rangeFrom(x, y)));
  } else {
    Exprs exprs;
    exprs.push_back(x);
    exprs.push_back(y);
    argstack.push_back(new CallAST(p.first, exprs, rangeFrom(x, y)));
  }
}

ExprAST* parseBinopChain(ExprAST* first, pTree binOpPairs) {
  if (getChildCount(binOpPairs) == 0) {
    return first;
  }

  std::vector< std::pair<VarOpPair, ExprAST*> > pairs;

  for (size_t i = 0; i < getChildCount(binOpPairs); i += 2) {
    pairs.push_back(std::make_pair(
                     VarOpPair(parseVarDirect(child(binOpPairs, i)),
                           oprPrefixOf(textOf(child(binOpPairs, i)))),
                     parsePhrase(child(binOpPairs, i + 1))));
  }

  std::vector<VarOpPair> opstack;
  std::vector<ExprAST*> argstack;
  argstack.push_back(first);
  argstack.push_back(pairs[0].second);
  opstack.push_back(pairs[0].first);

  for (size_t i = 1; i < pairs.size(); ++i) {
    while (!opstack.empty()) {
      const std::string& top = opstack.back().second;
      const std::string& opd = pairs[i].first.second;
      foster::OperatorPrecedenceTable::OperatorRelation rel =
                           ParsingContext::getOperatorRelation(top, opd);
      if (rel != foster::OperatorPrecedenceTable::kOpBindsTighter) {
        break;
      }
      leftAssoc(opstack, argstack);
    }

    argstack.push_back(pairs[i].second);
    opstack.push_back( pairs[i].first);
  }

  while (!opstack.empty()) {
    leftAssoc(opstack, argstack);
  }

  ASSERT(argstack.size() == 1);
  return argstack[0];
}

// ^(TERM ^(MU opr?) ^(MU phrase) ^(MU binops?))
ExprAST* parseTerm(pTree tree) {
  pTree pTmaybeOpr = child(tree, 0);
  pTree pTphrase   = child(tree, 1);
  pTree pTmaybeBin = child(tree, 2);
  ExprAST* base = parsePhrase(child(pTphrase, 0));

  if (getChildCount(pTmaybeOpr) > 0) {
    VariableAST* opvar = parseTermVar(pTmaybeOpr);
    // TODO move this check so it is caught by __COMPILES__
    ASSERT(opvar->getName() == "-")
                       << "For now, only unary - is allowed, not unary "
                       << "'" << opvar->getName() << "'"
                       << show(rangeOf(pTmaybeOpr));
    // If we have            - f x y (+ ...) ...,
    // interpret this as ((-) (f x y)) (+ ...) ...
    std::vector<ExprAST*> exprs; exprs.push_back(base);
    base = new CallAST(opvar, exprs, rangeFrom(pTmaybeOpr, pTphrase));
  }

  return parseBinopChain(base, pTmaybeBin);
}

ExprAST* ExprAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TERM) { return parseTerm(tree); }

  // Should have handled all keywords by now...
  if (ParsingContext::isKeyword(text)) {
    EDiag() << "illegal use of keyword '" << text << "'" << show(sourceRange);
    return NULL;
  }

  if (ParsingContext::isReservedKeyword(text)) {
    EDiag() << "cannot use reserved keyword '" << text << "'"
            << show(sourceRange);
    return NULL;
  }

  string name = str(tree->getToken(tree));
  ASSERT(false) << "returning NULL ExprAST for ExprAST_from token " << name
                  << "with text '" << text << "'"
                  << foster::show(sourceRange);
  return NULL;
}

TypeAST* parseTypeAtom(pTree tree);

// ^(OF dctor tatom*)
DataCtorAST* parseDataCtor(pTree t) {
  //foster::SourceRange sourceRange = rangeOf(t);
  std::vector<TypeAST*> types;
  for (size_t i = 1; i < getChildCount(t); ++i) {
    types.push_back(parseTypeAtom(child(t, i)));
  }
  return new DataCtorAST(parseCtor(child(t, 0))->getName(), types, rangeOf(t));
}

// ^(MU data_ctor*)
std::vector<DataCtorAST*> parseDataCtors(pTree t) {
  std::vector<DataCtorAST*> ctors;
  for (size_t i = 0; i < getChildCount(t); ++i) {
    ctors.push_back(parseDataCtor(child(t, i)));
  }
  return ctors;
}

void tryMarkTypeAsProc(TypeAST* typ) {
  TypeAST* mb_fty = NULL;

  if (ForallTypeAST* fa = dynamic_cast<ForallTypeAST*>(typ)) {
           mb_fty = fa->getQuantifiedType();
  } else { mb_fty = typ; }

  if (FnTypeAST* fty = dynamic_cast<FnTypeAST*>(mb_fty)) {
    fty->markAsProc();
  }
}

ModuleAST* parseTopLevel(pTree root_tree, std::string moduleName,
                         std::string hash,
                         std::queue<std::pair<string, string> >& out_imports) {
  // The top level is composed of declarations and definitions.
  std::vector<Decl*> decls;
  std::vector<Defn*> defns;
  std::vector<Data*> datas;

  pTree imports = child(root_tree, 0);
  for (size_t i = 0; i < getChildCount(imports); ++i) {
    pTree imp = child(imports, i);
    std::string imp_name = textOf(child(imp, 0));
    std::string imp_text = contentsOfDoubleQuotedStringWithoutQuotes(child(imp, 1));
    out_imports.push(std::make_pair(imp_name, imp_text));
  }

  for (size_t i = 1; i < getChildCount(root_tree); ++i) {
    pTree c = child(root_tree, i);
    int token = typeOf(c);

    if (token == DEFN) { // ^(DEFN x atom)
      string name = textOfVar(child(c, 0));
      ExprAST* atom = parseAtom(child(c, 1));
      defns.push_back(new Defn(name, atom));

      if (ValAbs* fn = dynamic_cast<ValAbs*>(atom)) { fn->name = name; }
    } else if (token == DECL) {
      pTree typevar = child(c, 0);
      pTree type    = child(c, 1);
      TypeAST* typ  = TypeAST_from(type);
      // Make sure that fn types for top-level declarations are marked as procs.
      tryMarkTypeAsProc(typ);
      decls.push_back(new Decl(textOfVar(typevar), typ));
    } else if (token == DATATYPE) { // ^(DATATYPE tyvar_decl ^(MU tyvar_decl*) ^(MU data_ctor*)
      datas.push_back(new Data(
                       parseTypeFormal(child(c, 0), getBoxedKind()),
                       parseTyFormals(child(c, 1), getBoxedKind()),
                       parseDataCtors(child(c, 2)),
                       rangeOf(c)));
    } else {
      EDiag() << "ANTLRtoFosterAST.cpp: "
              << "Unexpected top-level element with token ID " << token;
      //display_pTree(c, 8);
      //display_pTree(root_tree, 4);
      DDiag() << show(rangeOf(c));
    }
  }
  return new ModuleAST(decls, defns, datas, moduleName, hash);
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

bool tryGetBindingName(std::string& s, Binding& b) {
  if (LiteralPattern* lp = dynamic_cast<LiteralPattern*>(b.patt)) {
    if (lp->variety == LiteralPattern::LP_VAR) {
      s = dynamic_cast<VariableAST*>(lp->pattern)->getName();
      return true;
    }
  }
  return false;
}

// ^(FUNC_TYPE t+)
// ^(BINDING binding+)
void parseAnnots(std::map<string, string>& annots,
                 pTree tree) {
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    Binding b = parseBinding(child(tree, i));
    string  v;
    string  k;

    ASSERT(tryGetBindingName(k, b)) << "for now, annots only support literal patterns.";

    if (VariableAST* q = dynamic_cast<VariableAST*>(b.body)) {
      v = q->getName();
    } else
    if (IntAST* q = dynamic_cast<IntAST*>(b.body)) {
      v = q->getOriginalText();
    } else
    if (BoolAST* q = dynamic_cast<BoolAST*>(b.body)) {
      v = q->boolValue ? "true" : "false";
    }

    if (v == "") {
      EDiag() << "Annotation failed to parse value string from "
              << string(b.body->tag) << show(b.body);
    } else {
      annots[k] = v;
    }
  }
}

// ^(FUNC_TYPE ^(TUPLE t+) ^(MU val_abs?) tannots?)
TypeAST* parseFuncType(pTree tree) {
  std::vector<TypeAST*> types = getTypes(child(tree, 0));
  TypeAST* rt = types.back(); types.pop_back();

  pTree tprecond = child(tree, 1);
  ValAbs* precond = (tprecond && getChildCount(tprecond) == 1)
                       ? parseValAbs(child(tprecond, 0))
                       : NULL;

  std::map<string, string> annots;
  if (getChildCount(tree) == 3) {
    parseAnnots(annots, child(tree, 2));
  }

  // Lambdas default to fastcc, procs default to ccc.
  bool isProc = annots.find("proc") != annots.end()
             && annots["proc"] == "true";

  if (annots["callconv"] == "") {
    annots["callconv"] = isProc ? "ccc" : "fastcc";
  }
  return new FnTypeAST(rt, types, precond, annots);
}

// ^(TYPEVAR a)
NamedTypeAST* parseTypeVar(pTree tree) {
  TypeAST* ty = NULL;
  return new NamedTypeAST(textOf(child(tree, 0)), ty, rangeOf(tree));
}

// ^(TYPE_PLACEHOLDER ^(TYPEVAR a))
TypeAST* parseTypePlaceholder(pTree tree) {
  NamedTypeAST* tv = parseTypeVar(child(tree, 0));
  tv->is_placeholder = true;
  return tv;
}

TypeAST* parseTupleType(pTree tree) {
  if (getChildCount(tree) == 1) {
    return TypeAST_from(child(tree, 0));
  } else {
    return TupleTypeAST::get(getTypes(tree));
  }
}

TypeAST* parseTypeAtom(pTree tree) {
  int token = typeOf(tree);

  if (token == FUNC_TYPE) { return parseFuncType(tree); }
  if (token == TUPLE)     { return parseTupleType(tree); }
  if (token == TYPENAME)  { return parseTypeVar(tree); }
  if (token == TYPE_PLACEHOLDER) { return parseTypePlaceholder(tree); }

  display_pTree(tree, 2);
  ASSERT(false) << "parseTypeAtom";
  return NULL;
}

std::vector<TypeAST*> getTypes(pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    TypeAST* ast = TypeAST_from(child(tree, i));
    ASSERT(ast != NULL) << "getTypes: parsing type " << i;
    types.push_back(ast);
  }
  return types;
}

std::vector<TypeAST*> getTypeAtoms(pTree tree) {
  std::vector<TypeAST*> types;
  for (size_t i = 0; i < getChildCount(tree); ++i) {
    TypeAST* ast = parseTypeAtom(child(tree, i));
    ASSERT(ast != NULL) << "getTypeAtoms: parsing type atom " << i;
    types.push_back(ast);
  }
  return types;
}

// ^(TYPE_TYP_APP tatom tatom+)
TypeAST* parseTypeTypeApp(pTree tree) {
  return TypeTypeAppAST::get(getTypeAtoms(tree));
}

// ^(FORALL_TYPE tyformal+ t)
TypeAST* parseForallType(pTree tree) {
  std::vector<TypeFormal> tyformals;
  for (size_t i = 0; i < getChildCount(tree) - 1; ++i) {
    tyformals.push_back(parseTypeFormal(child(tree, i), getBoxedKind()));
  }
  return new ForallTypeAST(tyformals,
                           TypeAST_from(child(tree, getChildCount(tree) - 1)),
                           rangeOf(tree));
}

// ^(REFINED name ty expr)
TypeAST* parseRefinedType(pTree tree) {
  return new RefinedTypeAST(textOfVar(child(tree, 0)),
                            TypeAST_from(child(tree, 1)),
                            ExprAST_from(child(tree, 2)),
                            rangeOf(tree));
}

TypeAST* TypeAST_from(pTree tree) {
  if (!tree) return NULL;

  int token = typeOf(tree);
  string text = textOf(tree);
  foster::SourceRange sourceRange = rangeOf(tree);

  if (token == TYPE_ATOM)    { return parseTypeAtom(child(tree, 0)); }
  if (token == TYPE_TYP_APP) { return parseTypeTypeApp(tree); }
  if (token == FORALL_TYPE)  { return parseForallType(tree); }
  if (token == REFINED)      { return parseRefinedType(tree); }

  string name = str(tree->getToken(tree));
  foster::EDiag() << "returning NULL TypeAST for tree token " << name
                  << foster::show(sourceRange);
  return NULL;
}

////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////

namespace foster {

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

    if (tok->channel == 0) {
      ParsingContext::sawNonHiddenToken();
    }
    if (tok->channel != 0) {
      if (tok->type == NL
       || tok->type == LINE_COMMENT
       || tok->type == NESTING_COMMENT) {
        ParsingContext::sawHiddenToken(tok); // note: WS not included.
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

  pANTLR3_TOKEN_SOURCE newFosterIndentingTokenSource(pANTLR3_TOKEN_SOURCE src) {
    FosterIndentingTokenSource* s = new FosterIndentingTokenSource;
    s->originalSource = src;
    // Set all the fields required for an ANTLR3_TOKEN_SOURCE.
    s->eofToken   = src->eofToken;
    s->fileName   = src->fileName;
    s->skipToken  = src->skipToken;
    s->strFactory = src->strFactory;
    s->super      = (void*) s;
    s->nextToken  = fosterNextTokenFunc;
    return s;
  }

  struct ANTLRContext {
    string filename;
    pANTLR3_INPUT_STREAM input;
    pfosterLexer lxr;
    pANTLR3_COMMON_TOKEN_STREAM tstream;
    pfosterParser psr;

    ~ANTLRContext() {
      psr     ->free  (psr);      psr     = NULL;
      tstream ->free  (tstream);  tstream = NULL;
      lxr     ->free  (lxr);      lxr     = NULL;
      input   ->close (input);    input   = NULL;
    }
  };

  namespace {
    uint128 getMemoryBufferHash(llvm::MemoryBuffer* buf) {
      return CityHash128(buf->getBufferStart(), buf->getBufferSize());
    }

    uint128 getFileHash(const InputFile& file) {
      return getMemoryBufferHash(file.getBuffer()->getMemoryBuffer());
    }

    void createParser(foster::ANTLRContext&    ctx,
                      const string&            filepath,
                      foster::InputTextBuffer* textbuf) {
      llvm::MemoryBuffer* buf = textbuf->getMemoryBuffer();
      ASSERT(buf->getBufferSize() <= ((ANTLR3_UINT32)-1)
             && "Trying to parse files larger than 4GB makes me cry.");
      ctx.filename = filepath;
      ctx.input = antlr3NewAsciiStringInPlaceStream(
                                    (pANTLR3_UINT8) buf->getBufferStart(),
                                    (ANTLR3_UINT32) buf->getBufferSize(),
                                    NULL);
      ctx.lxr = fosterLexerNew(ctx.input);
      if (ctx.lxr == NULL) {
        ANTLR3_FPRINTF(stderr, "Unable to create lexer\n");
        exit(ANTLR3_ERR_NOMEM);
      }

      pANTLR3_TOKEN_SOURCE customSource
                = newFosterIndentingTokenSource(TOKENSOURCE(ctx.lxr));

      ctx.tstream = antlr3CommonTokenStreamSourceNew(ANTLR3_SIZE_HINT,
                                                     customSource);

      if (ctx.tstream == NULL) {
        ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate token stream.\n");
        exit(ANTLR3_ERR_NOMEM);
      }

      ctx.psr = fosterParserNew(ctx.tstream);
      if (ctx.psr == NULL) {
        ANTLR3_FPRINTF(stderr, "Out of memory trying to allocate parser.\n");
        exit(ANTLR3_ERR_NOMEM);
      }
    }

    void createParser(foster::ANTLRContext& ctx,
                      const foster::InputFile& infile) {
      createParser(ctx,
                   infile.getPath(),
                   infile.getBuffer());
    }

    void installTreeTokenBoundaryTracker(pANTLR3_BASE_TREE_ADAPTOR adaptor);
  } // unnamed namespace

  void deleteANTLRContext(ANTLRContext* ctx) { delete ctx; }

  // Note: Modules are parsed iteratively, not nestedly.
  // Parsing contexts can be stacked, but we no longer use that functionality.
  void parseModule(WholeProgramAST* pgm,
                   const foster::InputFile& file,
                   unsigned* outNumANTLRErrors,
                   std::queue<std::pair<string, string> >& out_imports) {
    uint128 hash = getFileHash(file);
    if (pgm->seen.count(hash) == 1) {
      return;
    }
    char hashcstr[33] = {0};
    sprintf(hashcstr, "%08" PRIx64 "%08" PRIx64,
                     Uint128Low64(hash), Uint128High64(hash));
    std::string hashstr(hashcstr);
    printf("Hash of file %s is %s\n", getShortName(&file).c_str(), hashcstr);

    ANTLRContext* ctx = new ANTLRContext();
    createParser(*ctx, file);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    gInputFile = &file; // used when creating source ranges
    gInputTextBuffer = file.getBuffer(); // also used for source ranges

    fosterParser_module_return langAST = ctx->psr->module(ctx->psr);
    *outNumANTLRErrors += ctx->psr->pParser->rec->state->errorCount;

    ModuleAST* m = parseTopLevel(langAST.tree, getShortName(&file), hashstr, out_imports);
    m->buf = file.getBuffer();
    m->hiddenTokens = ParsingContext::getHiddenTokens();

    pgm->seen[hash] = m;
    pgm->modules.push_back(m);
  }


  foster::InputFile* resolveModulePath(const std::vector<std::string>& searchPaths,
                                       const std::string& spath);

  WholeProgramAST* parseWholeProgram(const InputFile& startfile,
                                     const std::vector<std::string> searchPaths,
                                     unsigned* outNumANTLRErrors) {
    WholeProgramAST* pgm = new WholeProgramAST();
    *outNumANTLRErrors = 0;

    //llvm::sys::TimeValue parse_beg = llvm::sys::TimeValue::now();
    std::queue<std::pair<string, string> > pending_imports;
    parseModule(pgm, startfile, outNumANTLRErrors, pending_imports);

    while (*outNumANTLRErrors == 0 && !pending_imports.empty()) {
      std::pair<string, string> imp = pending_imports.front();
                                      pending_imports.pop();
      std::string localname = imp.first;
      std::string imp_path  = imp.second;
      std::cout << "pending import: " << imp.first << " " << imp.second << std::endl;
      if (foster::InputFile* f = resolveModulePath(searchPaths, imp_path)) {
        parseModule(pgm, *f, outNumANTLRErrors, pending_imports);
      } else {
        return NULL;
      }
    }

    //llvm::sys::TimeValue parse_end = llvm::sys::TimeValue::now();
    //llvm::outs() << "ANTLR  parsing: " << (parse_mid - parse_beg).msec() << "\n";
    //llvm::outs() << "Foster parsing: " << (parse_end - parse_mid).msec() << "\n";

    return pgm;
  }

  void pathConcat(const std::string& searchPath,
                  const std::string& spath, llvm::SmallString<256>& path) {
      path.clear();

      if (searchPath.empty()) {
        llvm::sys::path::append(path, ".");
      } else {
        llvm::sys::path::append(path, searchPath);
      }

      llvm::sys::path::append(path, spath);
  }

  // spath will be something like "foo/bar"
  // We'll want to check for searchPath[i]/foo/bar.foster
  //                and also searchPath[i]/foo/bar/bar.foster
  foster::InputFile* resolveModulePath(const std::vector<std::string>& searchPaths,
                                       const std::string& spath) {
    std::vector<std::string> failedPaths;
    for (auto searchPath : searchPaths) {
      llvm::SmallString<256> path;
      // Start with searchPaths[i]/foo/bar

      // Try foo/bar.foster
      pathConcat(searchPath, spath, path);
      llvm::sys::path::replace_extension(path, "foster");
      if (llvm::sys::fs::exists(path.str())) {
        return new foster::InputFile(path.str());
      } else {
        failedPaths.push_back(path.str());
      }

      // Try foo/bar/bar.foster
      pathConcat(searchPath, spath, path);
      llvm::sys::path::append(path, llvm::sys::path::stem(spath));
      llvm::sys::path::replace_extension(path, "foster");
      if (llvm::sys::fs::exists(path.str())) {
        return new foster::InputFile(path.str());
      } else {
        failedPaths.push_back(path.str());
      }
    }
    EDiag() << "Unable to resolve import path: " << spath;
    llvm::errs() << "  tried the following paths:\n";
    for (auto p : failedPaths) { llvm::errs() << "    " << p << "\n"; }

    return NULL;
  }

  ////////////////////////////////////////////////////////////////////

  // Ugly ANTLR-C token boundary customization.
  namespace {
    typedef void                  (*setTokenBoundariesFunc)
    (struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
     pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken);

    static setTokenBoundariesFunc sgDefaultSTB;

    static void customSetTokenBoundariesFunc
    (struct ANTLR3_BASE_TREE_ADAPTOR_struct * adaptor, void * t,
     pANTLR3_COMMON_TOKEN startToken, pANTLR3_COMMON_TOKEN stopToken) {
      sgDefaultSTB(adaptor, t, startToken, stopToken);
      ParsingContext::setTokenRange((pTree) t, startToken, stopToken);
    }

    // This is a vaguely unpleasant (but terrifically accurate) hack
    // to monitor the token boundaries computed for tree nodes, which
    // are unfortunately (and strangely) not actually stored in the nodes
    // themselves, but rather in shadow parent nodes inaccessible from
    // the tree nodes themselves. Anyways, we just replace the function pointer
    // in the virtual table with a thin shim, above.
    void installTreeTokenBoundaryTracker(pANTLR3_BASE_TREE_ADAPTOR adaptor) {
      sgDefaultSTB = adaptor->setTokenBoundaries;
      adaptor->setTokenBoundaries = customSetTokenBoundariesFunc;
    }
  } // unnamed namespace

} // namespace foster
const char* ANTLR_VERSION_STR = PACKAGE_VERSION;
