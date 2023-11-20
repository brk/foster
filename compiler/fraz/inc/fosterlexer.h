#ifndef FOSTERLEXER_H
#define FOSTERLEXER_H

typedef struct {
  int tok;
  int line;
  int col;
  int endline;
  int endcol;
} Token;

typedef struct {
  char* buf;
  int num_errors;

  int ptr;
  int cur;
  int top;
  int commentdepth;
  int line;
  int linepos;
  int linepos_prev;
} Scanner;

void scan_token_start(Scanner* s, Token* t, int buff_end);
#endif
