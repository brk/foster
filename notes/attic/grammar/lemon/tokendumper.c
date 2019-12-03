#include "fosterlexer.h"

#include <stdio.h>
#include <stdlib.h>

// Re-generate with
//     awk '{ print "    case " $2 ": return \"" $2 "\";" }' < parser.h
const char* tokName(int tok) {
  switch (tok) {
    case WHITESPACE: return "WHITESPACE";
    case LINECOMMENT: return "LINECOMMENT";
    case BLOCKCOMMENT: return "BLOCKCOMMENT";
    case NEWLINE: return "NEWLINE";
    case FINI: return "FINI";
    case INCLUDE: return "INCLUDE";
    case SEMI: return "SEMI";
    case DCOLON: return "DCOLON";
    case EQUAL: return "EQUAL";
    case TYPE: return "TYPE";
    case CASE: return "CASE";
    case EFFECT: return "EFFECT";
    case FOREIGN: return "FOREIGN";
    case IMPORT: return "IMPORT";
    case LPAREN: return "LPAREN";
    case RPAREN: return "RPAREN";
    case OF: return "OF";
    case DARROW: return "DARROW";
    case AS: return "AS";
    case DOLLAR: return "DOLLAR";
    case OPRNAME: return "OPRNAME";
    case SMALLIDENT: return "SMALLIDENT";
    case UPPERIDENT: return "UPPERIDENT";
    case UNDERIDENT: return "UNDERIDENT";
    case REC: return "REC";
    case UNDERSCORE: return "UNDERSCORE";
    case LET: return "LET";
    case COMMA: return "COMMA";
    case SYMBOL: return "SYMBOL";
    case BACKTICK: return "BACKTICK";
    case PRIM: return "PRIM";
    case CARET: return "CARET";
    case LBRACK: return "LBRACK";
    case RBRACK: return "RBRACK";
    case BANG: return "BANG";
    case END: return "END";
    case COMPILES: return "COMPILES";
    case LCURLY: return "LCURLY";
    case RCURLY: return "RCURLY";
    case COLON: return "COLON";
    case FORALL: return "FORALL";
    case HANDLE: return "HANDLE";
    case SARROW: return "SARROW";
    case HASH: return "HASH";
    case IF: return "IF";
    case OR: return "OR";
    case NUM: return "NUM";
    case STR: return "STR";
    case THEN: return "THEN";
    case ELSE: return "ELSE";
    case PERCENT: return "PERCENT";
    default: return "<UNKNOWN>";
    }
}

void chompchomp(Scanner* s, long size) {
  Token t;
  unsigned char yych = 0;
  while(1) {
    int chan = scan_token(s, &t, size, &yych);
    if(t.tok == FINI) {
      break;
    }

    printf("%30s: (range %d %d  %d %d)\n", tokName(t.tok),
            t.line, t.col, t.endline, t.endcol);
  }
}

int main(int argc, char** argv) {

  FILE *fp;
  long size;
  char *buff;
  char name_str[64];
  size_t bytes;
  int name_length;
  Scanner scanner;
  void *parser;

  if (argc != 2) {
    printf("Usage: %s <input.foster>\n", argv[0]);
    exit(1);
  }

  /* Open input file */
  fp = fopen(argv[1], "r");
  if(fp == NULL) {
    fprintf(stderr, "Can't open test file: %s\n", argv[1]);
    exit(-1);
  }

  /* Get file size */
  fseek(fp, 0, SEEK_END);
  size = ftell(fp);
  rewind(fp);

  /* Allocate buffer and read */
  buff = (char*) malloc(size * sizeof(char));
  bytes = fread(buff, 1, size, fp);  
  if (bytes != size) {
    fprintf(stderr, "Error reading input file\n");
    exit(-1);
  }

  /* Initialize scanner */
  scanner.buf = buff;
  scanner.top = 0;
  scanner.cur = 0;
  scanner.commentdepth = 0;
  scanner.linepos = 0;
  scanner.linepos_prev = 0;
  scanner.num_errors = 0;
  scanner.line = 1;

  chompchomp(&scanner, size);

  /* Close files and deallocate */
  fclose(fp);
  free(buff);
  return(0);
}
