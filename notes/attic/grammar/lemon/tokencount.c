#include "fosterlexer.h"

#include <stdio.h>
#include <stdlib.h>

void chompchomp(Scanner* s, long size) {
  Token t;
  int n = 0;
  unsigned char yych;
  while(1) {
    int chan = scan_token(s, &t, size, &yych);
    if(t.tok == FINI) {
      break;
    }
    ++n;
  }
  printf("%d tokens\n", n);
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
