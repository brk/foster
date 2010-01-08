
#ifndef H_4b2d1929175588_52157406
#define H_4b2d1929175588_52157406

/** @file
    @brief
    */

#include <antlr3defs.h>
#include <string>

typedef pANTLR3_BASE_TREE pTree;

class ExprAST;

ExprAST* ExprAST_from(pTree tree);
void initMaps();

std::string str(pANTLR3_STRING pstr);

std::string str(pANTLR3_COMMON_TOKEN tok);

#endif // header guard

