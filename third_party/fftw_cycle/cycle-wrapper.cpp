#include "cycle.h"
#include <stdint.h>

extern "C" {

int64_t foster__getticks_start() {
  return int64_t(getticks_start());
}

int64_t foster__getticks_end() {
  return int64_t(getticks_end());
}

int64_t foster__getticks() {
  return int64_t(getticks());
}

double  foster__getticks_elapsed(int64_t t1, int64_t t2) {
  return elapsed(ticks(t2), ticks(t1));
}

}
