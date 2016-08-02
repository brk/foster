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

#include "cbor.h"

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

void display_pTree(pTree t, int nspaces);

size_t getChildCount(pTree tree) {
  return (tree ? static_cast<size_t>(tree->getChildCount(tree)) : 0);
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
    tok = tree->getToken(tree);
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

  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, getChildCount(node) - 1);
    tok = ParsingContext::getEndToken(node);
  }
  if (!tok) {
    tok = tree->getToken(tree);
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

foster::SourceRange rangeFrom(pANTLR3_COMMON_TOKEN stok,
                              pANTLR3_COMMON_TOKEN etok) {
  return foster::SourceRange(foster::gInputFile,
    getStartLocation(stok),
    getEndLocation(etok),
    foster::gInputTextBuffer);
}

foster::SourceRange rangeFrom(pTree start, pTree end) {
  pANTLR3_COMMON_TOKEN stok = getStartToken(start);
  pANTLR3_COMMON_TOKEN etok = getEndToken(end);
  return rangeFrom(stok, etok);
}

foster::SourceRange rangeOf(pTree tree) {
  return rangeFrom(tree, tree);
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

std::string contentsOfDoubleQuotedStringWithoutQuotes(pTree t) {
  std::string s = textOf(t);
  size_t offset = s[0] == 'r' ? 2 : 1;
  ASSERT(s.size() > (offset + 1));
  return std::string(s.begin() + offset, s.end() - 1);
  EDiag() << "Unable to determine what kind of string this is!" << s << "\n" << show(rangeOf(t));
}

void extractImports(pTree root_tree,
                    std::queue<std::pair<string, string> >& out_imports) {
  pTree imports = child(root_tree, 0);
  for (size_t i = 0; i < getChildCount(imports); ++i) {
    pTree imp = child(imports, i);
    std::string imp_name = textOf(child(imp, 0));
    std::string imp_text = contentsOfDoubleQuotedStringWithoutQuotes(child(imp, 1));
    out_imports.push(std::make_pair(imp_name, imp_text));
  }
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

    bool isMatchingTokenOpen(pANTLR3_COMMON_TOKEN tok) {
      return tok->type == OPEN_PAREN
          || tok->type == OPEN_CURLY
          || tok->type == OPEN_SQRBR
          || tok->type == OPEN_COLON_SQRBR;
    }

    bool isMatchingTokenClose(pANTLR3_COMMON_TOKEN tok) {
      return tok->type == CLOSE_PAREN
          || tok->type == CLOSE_CURLY
          || tok->type == CLOSE_SQRBR;
    }

    ANTLR3_UINT32 matchingTokenType(pANTLR3_COMMON_TOKEN opn) {
      if (opn->type == OPEN_PAREN) return CLOSE_PAREN;
      if (opn->type == OPEN_CURLY) return CLOSE_CURLY;
      if (opn->type == OPEN_SQRBR) return CLOSE_SQRBR;
      if (opn->type == OPEN_COLON_SQRBR) return CLOSE_SQRBR;
      return 0;
    }

    void doTokenMatchingPrepass(const foster::InputFile& infile) {
      auto buf = infile.getBuffer()->getMemoryBuffer();
      auto filepath = infile.getPath();
      auto input = antlr3StringStreamNew(
                                    (pANTLR3_UINT8) buf->getBufferStart(),
                                                    ANTLR3_ENC_8BIT,
                                    (ANTLR3_UINT32) buf->getBufferSize(),
                                    (pANTLR3_UINT8) const_cast<char*>(filepath.c_str()));
      auto lxr = fosterLexerNew(input);
      auto tsr = TOKENSOURCE(lxr);
      bool failed = false;

      pANTLR3_COMMON_TOKEN tok = NULL;
      std::vector<pANTLR3_COMMON_TOKEN> matchingTokens;
      do {
        tok = tsr->nextToken(tsr);
        if (isMatchingTokenOpen(tok)) {
          matchingTokens.push_back(tok);
        } else if (isMatchingTokenClose(tok)) {
          if (matchingTokens.empty()) {
            EDiag() << "Unexpectedly saw a closing brace without a matching opening brace!"
                    << show(rangeFrom(tok, tok)) << "\n";
            failed = true;
          } else {
            auto matchingTok = matchingTokens.back();
            if (matchingTokenType(matchingTok) != tok->type) {
              EDiag() << "You know, I was expecting to find a buddy for this little guy here:\n" << show(rangeFrom(matchingTok, matchingTok))
                      << "but instead this unexpected token came outta nowhere:\n" << show(rangeFrom(tok, tok));
              failed = true;
            } else {
              matchingTokens.pop_back();
            }
          }
        }
      } while (tok != &tsr->eofToken);

      if (!matchingTokens.empty()) {
        auto matchingTok = matchingTokens.back();
        EDiag() << "You know, I was expecting to find a buddy for this little guy here:\n" << show(rangeFrom(matchingTok, matchingTok))
                << "but I never did...\n"
                << "The culprit is probably a stray friend of his, somewhere later on in your program,\n"
                << "that snatched away his buddy. If you think you know where his buddy is, try\n"
                << "checking what token the buddy actually matches up with.\n"
                << "The culprit should be somewhere in between...\n";
        failed = true;
      }

      //tsr ->free (tsr);  tsr = NULL;
      lxr->free  (lxr);  lxr = NULL;

      if (failed) {
        llvm::errs() << "Bailing out due to mismatched tokens...\n";
        exit(1);
      }
    }

    void createParser(foster::ANTLRContext&    ctx,
                      const string&            filepath,
                      foster::InputTextBuffer* textbuf) {
      llvm::MemoryBuffer* buf = textbuf->getMemoryBuffer();
      ASSERT(buf->getBufferSize() <= ((ANTLR3_UINT32)-1)
             && "Trying to parse files larger than 4GB makes me cry.");

      ctx.filename = filepath;
      ctx.input = antlr3StringStreamNew(
                    (pANTLR3_UINT8) const_cast<char*>(buf->getBufferStart()),
                                    ANTLR3_ENC_8BIT,  // TODO: _UTF8
                    (ANTLR3_UINT32) buf->getBufferSize(),
                    (pANTLR3_UINT8) const_cast<char*>(filepath.c_str()));
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
  void parseModule(InputWholeProgram* pgm,
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
    //printf("Hash of file %s is %s\n", getShortName(&file).c_str(), hashcstr);

    ANTLRContext* ctx = new ANTLRContext();
    createParser(*ctx, file);

    installTreeTokenBoundaryTracker(ctx->psr->adaptor);
    // TODO for some malformed input (with stray ; nodes) this produces
    // wrong results -- no parse && no errors, only warnings reported.
    foster::installRecognitionErrorFilter(ctx->psr->pParser->rec);

    gInputFile = &file; // used when creating source ranges
    gInputTextBuffer = file.getBuffer(); // also used for source ranges

    doTokenMatchingPrepass(file);

    fosterParser_module_return langAST = ctx->psr->module(ctx->psr);
    *outNumANTLRErrors += ctx->psr->pParser->rec->state->errorCount;

    InputModule* m = new InputModule(langAST.tree, &file, hashstr, ParsingContext::getHiddenTokens());
    extractImports(langAST.tree, out_imports);

    pgm->seen[hash] = m;
    pgm->modules.push_back(m);
  }


  foster::InputFile* resolveModulePath(const std::vector<std::string>& searchPaths,
                                       const std::string& spath);

  InputWholeProgram* parseWholeProgram(const InputFile& startfile,
                                     const std::vector<std::string> searchPaths,
                                     unsigned* outNumANTLRErrors) {
    InputWholeProgram* pgm = new InputWholeProgram();
    *outNumANTLRErrors = 0;

    //llvm::sys::TimeValue parse_beg = llvm::sys::TimeValue::now();
    std::queue<std::pair<string, string> > pending_imports;
    parseModule(pgm, startfile, outNumANTLRErrors, pending_imports);

    while (*outNumANTLRErrors == 0 && !pending_imports.empty()) {
      std::pair<string, string> imp = pending_imports.front();
                                      pending_imports.pop();
      std::string localname = imp.first;
      std::string imp_path  = imp.second;
      //std::cout << "pending import: " << imp.first << " " << imp.second << std::endl;
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

void dumpToCbor(cbor::encoder& e, foster::SourceRange r) {
  e.write_array(4);
  e.write_int(r.begin.line);
  e.write_int(r.begin.column);
  e.write_int(r.end.line);
  e.write_int(r.end.column);
}

// An ANTLR tree node is dumped as an array
// [TypeIDNum, StringValue, SourceRange, child0, ..., childN]
void dumpToCbor(cbor::encoder& e, pTree p) {
  auto cc = p->getChildCount(p);
  auto tt = p->getType(p);
  e.write_array(4);
  e.write_int(tt);
  if (false && (tt == SNAFUINCLUDE || tt == TERMNAME || tt == LVALUE || tt == LIT_NUM
    || tt == MU || tt == VAL_ABS || tt == PHRASE || tt == TERM || tt == FORMALS
    || tt == STMTS || tt == ABINDING || tt == DEFN || tt == TYPENAME || tt == STRING
    || tt == BINDING || tt == TUPLE || tt == TYPE_TYP_APP || tt == FORMAL
    || tt == SUBSCRIPT || tt == PRIMAPP || tt == DECL || tt == TYPE_ATOM
    || tt == FUNC_TYPE || tt == WILDCARD || tt == DQUO)) {
    e.write_string("");
  } else {
    e.write_string(str(p->getText(p)));
  }
  dumpToCbor(e, rangeOf(p));
  e.write_array(cc);
  for (unsigned i = 0; i < cc; ++i) {
    dumpToCbor(e, (pTree) p->getChild(p, i));
  }
}

void dumpToCbor(cbor::encoder& e, pANTLR3_COMMON_TOKEN tok) {
  if (!tok) { // NULL pointers inserted by calls to sawNonHiddenToken()
    return;
  } else if (foster::isNewlineToken(tok)) {
    e.write_array(3);
    e.write_string("NEWLINE");
    e.write_int(tok->getLine(tok) - 1          );
    e.write_int(tok->getCharPositionInLine(tok));
  } else {
    e.write_array(4);
    e.write_string("COMMENT");
    e.write_int(tok->getLine(tok) - 1          );
    e.write_int(tok->getCharPositionInLine(tok));
    e.write_string((const char*) tok->getText(tok)->chars);
  }
}

// A module is dumped as the filename, hash, the tree, the original lines,
// and hidden tokens.
void dumpToCbor(cbor::encoder& e, InputModule* mod) {
  e.write_array(5);
  e.write_string(getShortName(mod->source));
  e.write_string(mod->hash);
  dumpToCbor(e, mod->tree);

  const foster::InputTextBuffer* buf = mod->source->getBuffer();
  int nlines = buf ? buf->getLineCount() : 0;
  e.write_array(nlines);
  for (int i = 0; i < nlines; ++i) {
    e.write_string(buf->getLine(i));
  }

  int countHiddenTokens = 0;
  for (auto t : mod->hiddenTokens) { if (t) { ++countHiddenTokens; } }
  e.write_array(countHiddenTokens);
  for (auto t : mod->hiddenTokens) {
    dumpToCbor(e, t);
  }
}

// A program is dumped as an array of the modules
void dumpToCbor(cbor::encoder& e, InputWholeProgram* wp) {
  e.write_array(wp->modules.size());
  for (auto m : wp->modules) {
    dumpToCbor(e, m);
  }
}
