// Make sure non-transformation passes don't need to return a useless value
#define FOSTER_AST_RETVAL void

#define FOSTER_AST_INCLUDED_VIA_DECLS_H
#include "FosterASTVisitor.base.inc.h"
#undef  FOSTER_AST_INCLUDED_VIA_DECLS_H
