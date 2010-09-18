// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

// This file collects various utility functions for
// ANTLRtoFosterAST.cpp

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
  return static_cast<size_t>(tree->getChildCount(tree));
}

string textOf(pTree tree) {
  if (!tree) {
    currentErrs() << "Error! Can't get text of a null node!" << "\n";
    return "<NULL pTree>";
  }
  return str(tree->getText(tree));
}

pTree child(pTree tree, int i) {
  if (!tree) {
    currentErrs() << "Error! Can't take child of null pTree!" << "\n";
    return NULL;
  }
  return (pTree) tree->getChild(tree, i);
}

int typeOf(pTree tree) { return tree->getType(tree); }

pANTLR3_COMMON_TOKEN getStartToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = CompilationContext::getStartToken(tree);
  if (tok) return tok;

  // Some nodes we're okay with having no token info for...
  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }

  // Usually, ANTLR will have annotated the tree directly;
  // however, in some cases, only subtrees will have token
  // information. In such cases, we search along the edge of the
  // parse tree to find the first edge child with token info.
  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, 0);
    tok = CompilationContext::getStartToken(node);
  }
  if (!tok) {
    currentOuts() << "Warning: unable to find start token for ANTLR parse tree"
              << " node " << textOf(tree) << " @ " << tree
              << " , " << typeOf(tree) << "\n";
  }
  return tok;
}

pANTLR3_COMMON_TOKEN getEndToken(pTree tree) {
  if (!tree) return NULL;
  pANTLR3_COMMON_TOKEN tok = CompilationContext::getEndToken(tree);
  if (tok) return tok;

  if (getChildCount(tree) == 0) {
    int tag = typeOf(tree);
    if (tag == OUT || tag == IN || tag == BODY
     || tag == ANTLR3_TOKEN_INVALID) {
      return NULL;
    }
  }

  pTree node = tree;
  while (!tok && getChildCount(node) > 0) {
    node = child(node, getChildCount(node) - 1);
    tok = CompilationContext::getEndToken(node);
  }
  if (!tok) {
    currentOuts() << "Warning: unable to find end token for ANTLR parse tree"
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
  if (false && (!stok || !etok)) {
    currentOuts() << "rangeFrom " << start << " => " << stok << " ;; "
              << end << " => " << etok << "\n";
    if (!stok) { display_pTree(start, 2); }
    if (!etok) { display_pTree(  end, 2); }
  }
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


string spaces(int n) { return string(n, ' '); }

void display_pTree(pTree t, int nspaces) {
  if (!t) {
    currentOuts() << spaces(nspaces) << "<NULL tree>" << "\n";
    return;
  }

  int token = t->getType(t);
  string text = textOf(t);
  int nchildren = getChildCount(t);
  std::stringstream ss;
  ss << spaces(nspaces) << "<" << text << "; ";
  currentOuts() << ss.str() << spaces(70 - ss.str().size())
            << token << " @ " << t;
  currentOuts() << " (";
  currentOuts() << (CompilationContext::getStartToken(t) ? '+' : '-');
  currentOuts() << (CompilationContext::getEndToken(t)   ? '+' : '-');
  currentOuts() << ")" << "\n";
  for (int i = 0; i < nchildren; ++i) {
    display_pTree(child(t, i), nspaces+2);
  }
  currentOuts() << spaces(nspaces) << "/" << text << ">" << "\n";
}

void dumpANTLRTreeNode(std::ostream& out, pTree tree, int depth) {
  out << string(depth, ' ');
  out << "text:"<< str(tree->getText(tree)) << " ";
  out << "line:"<< tree->getLine(tree) << " ";
  out << "charpos:"<< tree->getCharPositionInLine(tree) << " ";
  out << "\n";
}

void dumpANTLRTree(std::ostream& out, pTree tree, int depth) {
  int nchildren = tree->getChildCount(tree);
  out << "nchildren:" << nchildren << "\n";
  for (int i = 0; i < nchildren; ++i) {
    dumpANTLRTree(out, (pTree) tree->getChild(tree, i), depth + 1);
  }
  dumpANTLRTreeNode(out, tree, depth);
}
