#include "timer.h"
#include <vector>

int main() {
  timings t;

  double sumlt = 0;
  int    suml = 0;
  {
    timer r(t, "suml");
    for (int i = 0; i < 1000000; ++i) {
      suml += i;
    }
    double sumlt = t.read("suml");
  }

  int sum = 0;
  {
    std::vector<int> v(1000000);
    for (int i = 0; i < v.size(); ++i) {
      v[i] = i;
    }
    timer r(t, "sumv");
    for (int i = 0; i < v.size(); ++i) {
      sum += v[i];
    }
  }
  std::cout << "sum  = " << sum << "\n";
  std::cout << "suml = " << suml << "\n";
  std::cout << t.summarize("sumv", "suml");
  return 0;
}
