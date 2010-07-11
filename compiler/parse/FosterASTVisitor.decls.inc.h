// Make sure non-transformation passes don't need to return a useless value
#ifndef FOSTER_AST_RETVAL
#define FOSTER_AST_RETVAL void
#endif

#define FOSTER_AST_INCLUDED_VIA_DECLS_H
#include "parse/FosterASTVisitor.base.inc.h"
#undef  FOSTER_AST_INCLUDED_VIA_DECLS_H
