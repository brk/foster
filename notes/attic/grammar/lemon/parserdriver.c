#include "fosterlexer.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "vector.h"


void* ParseAlloc();
void ParseFree(
  void *p,                    /* The parser to be deleted */
  void (*freeProc)(void*)     /* Function used to reclaim memory */
);
void Parse(
  void *yyp,                   /* The parser */
  int yymajor,                 /* The major token code number */
  int yyminor                  /* The value for the token */
);

int main(int argc, char** argv) {

  FILE *fp;
  //FILE *traceFile;
  long size;
  char *buff;
  char name_str[64];
  size_t bytes;
  int name_length, token;
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

  /* Open trace file */
  //traceFile = fopen("trace.out", "w");
  //if(traceFile == NULL) {
  //  fprintf(stderr, "Can't open trace file\n");
  //  exit(-1);
  //}

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
  memset(&scanner, 0, sizeof(scanner));
  scanner.buf = buff;
  scanner.line = 1;

  /* Create parser and set up tracing */
  parser = ParseAlloc();
  //ParseTrace(traceFile, "parser >> ");

  Token* tokens = NULL;
  while(1) {
    Token t = { 0 };
    unsigned char yych = 0;
    int chan = scan_token(&scanner, &t, size, &yych);
    if (t.tok == FINI) { break; }
    if (chan == 0) {
      vector_push_back(tokens, t);
    }
  }

  printf("Number of lexical errors found: %d\n", scanner.num_errors);
  printf("Number of tokens found: %lu\n", vector_size(tokens));

  int sz = vector_size(tokens);
  for (int i = 0; i < sz; ++i) {
    Token t = tokens[i];
    Parse(parser, t.tok, 0);
    #if 0
    // Send strings to the parser with NAME tokens
    if(token == NAME) {
      name_length = scanner.cur - scanner.top;
      strncpy(name_str, &scanner.buf[scanner.top], name_length);
      name_str[name_length] = '\0';
      Parse(parser, token, name_str, &pCount);
    }
    else {
      Parse(parser, token, "", &pCount);
    }
    #endif
  }

  Parse(parser, 0, 0);

  printf("success!\n");

  /* Deallocate parser */
  ParseFree(parser, free);
  vector_free(tokens);

  /* Close files and deallocate */
  fclose(fp);
  //fclose(traceFile);
  free(buff);
  return(0);
}
