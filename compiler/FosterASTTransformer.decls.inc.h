// Make sure the retval defaults to the type of each separate AST node
#ifdef FOSTER_AST_RETVAL
#undef FOSTER_AST_RETVAL
#endif

#define FOSTER_AST_INCLUDED_VIA_DECLS_H
#include "FosterASTVisitor.base.inc.h"
#undef  FOSTER_AST_INCLUDED_VIA_DECLS_H
