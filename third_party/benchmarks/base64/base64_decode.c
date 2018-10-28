#include "base64.inc.h"

int main() {
  init_decode_table();

  const int STR_SIZE = 10000000;
  const int TRIES = 100;

  char *str = (char*) malloc(STR_SIZE + 1);
  for (int i = 0; i < STR_SIZE; i++) { str[i] = 'a'; }
  str[STR_SIZE] = '\0';

  char *str2;
  int str2_size;
  encode(STR_SIZE, str, &str2_size, &str2);

  s = 0;
  t = clock();
  for (int i = 0; i < TRIES; i++) {
    char *str3;
    int str3_size;
    if (decode(str2_size, str2, &str3_size, &str3) != 0) {
      printf("error when decoding");
    }
    s += str3_size;
    free(str3);
  }
  printf("decode: %d, %.2f\n", s, (float)(clock() - t)/CLOCKS_PER_SEC);
  return 0;
}