#include "base64.inc.h"

int main() {
  init_decode_table();

  const int STR_SIZE = 10000000;
  const int TRIES = 100;

  char *str = (char*) malloc(STR_SIZE + 1);
  for (int i = 0; i < STR_SIZE; i++) { str[i] = 'a'; }
  str[STR_SIZE] = '\0';

  int s = 0;
  clock_t t = clock();
  for (int i = 0; i < TRIES; i++) {
    char *str2;
    int str2_size;
    encode(STR_SIZE, str, &str2_size, &str2);
    s += str2_size;
    free(str2);
  }
  printf("encode: %d, %.2f\n", s, (float)(clock() - t)/CLOCKS_PER_SEC);

  return 0;
}