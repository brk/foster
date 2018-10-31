#include <stdio.h>

/*static const*/
struct {
  int lhs;       /* Symbol on the left-hand side of the rule */
  signed char nrhs;     /* Negative of the number of RHS symbols in the rule */
} yyRuleInfo[] = {
  {  140,   -1 }, /* (0) direct_declarator ::= NAME */
  {  144,   -1 }  /* (1) external_declaration ::= function_definition */
};

int main() {
  printf("%d\n", yyRuleInfo[0].lhs);
  return 0;
}
