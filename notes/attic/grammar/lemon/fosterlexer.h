#ifndef FOSTERLEXER_H
#define FOSTERLEXER_H

#include "fostertokens.h"

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

// Return: 0 for normal tokens; 99 for whitespace or comments.
int scan_token(Scanner* scanner, Token* t, int buffer_size, unsigned char* yych);

#endif
