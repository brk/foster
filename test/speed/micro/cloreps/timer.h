#include <string>
#include <sstream>
#include <iostream>
#include <map>
#include "cycle.h"

void clearcache() {
  int n = 16*1024*1024;
  int* a = new int[n];
  for (int i = 0; i < n; ++i) { a[i] = i; }
  delete [] a;
}

class timings {
  std::map<std::string, double> m;
 public:
  void print() {
    for ( std::map<std::string, double>::iterator it = m.begin(); it != m.end(); ++it) {
      std::cout << it->first << " : " << it->second << "\n";
    }
  }
  void incr(const std::string& s, double n) {
    m[s] += n;
  }
  double read(const std::string& s) { return m[s]; }

  std::string summarize(const std::string& s1,
	                const std::string& s2) {
    double a = read(s1);
    double b = read(s2);
    std::stringstream ss;
    ss << s1 << "/" << s2 << " = "
       << a  << "/" << b  << " = "
       << (a/b) << "\n";
    return ss.str();
  }
};

class timer {
  const std::string s;
  timings& t;
  ticks start;
public:
  timer(timings& t, const std::string& x) : s(x), t(t) {
    clearcache();
    start = getticks();
  }
  ~timer() {
    //std::cout << "~timer '" << s << "': " << getticks() << " :: "<< elapsed(getticks(), start) << "\n";
    t.incr(s, elapsed(getticks(), start));
    clearcache();
  }
};

