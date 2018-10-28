#include "timer.h"
#include <vector>

int count = 0;

/////////////

typedef void (*fn_0)(void*);
struct env_ii { int a; int b; };
struct clo_ii {
  env_ii* e;
  fn_0    f;
};

void f_ii(void* env) {
  env_ii* e = (env_ii*) env;
  count += (e->a  + e->b);
}

/////////////

struct cloenv_ii {
  fn_0 g;
  env_ii e;
};

void g_ii(void* cloenv) {
  cloenv_ii* e = (cloenv_ii*) cloenv;
  count += (e->e.a  + e->e.b);
}

/////////////

void h_ii(int a, int b) {
  count += (a  + b);
}

/////////////

void test_f_ii(timings& t, int n) {
  { std::vector<clo_ii> cs(n);
    for (int i = 0; i < n; ++i) {
      cs[i].f    = f_ii;
      cs[i].e    = new env_ii;
      cs[i].e->a = 1;
      cs[i].e->b = 2;
    }

    timer r(t, "f");
    for (int i = 0; i < n; ++i) {
      clo_ii* c = &cs[i];
      c->f(c->e);
    }
  }
}

void test_f2_ii(timings& t, int n) {
  { std::vector<cloenv_ii> cs(n);
    for (int i = 0; i < n; ++i) {
      cs[i].g = f_ii;
      cs[i].e.a = 1;
      cs[i].e.b = 2;
    }

    timer r(t, "f2");
    for (int i = 0; i < n; ++i) {
      cloenv_ii* c = &cs[i];
      c->g(&c->e);
    }
  }
}

void test_g_ii(timings& t, int n) {
  { std::vector<cloenv_ii> cs(n);
    for (int i = 0; i < n; ++i) {
      cs[i].g = g_ii;
      cs[i].e.a = 1;
      cs[i].e.b = 2;
    }

    timer r(t, "g");
    for (int i = 0; i < n; ++i) {
      cloenv_ii* c = &cs[i];
      c->g(c);
    }
  }
}

void test_h_ii(timings& t, int n) {
  { std::vector<env_ii> es(n);
    for (int i = 0; i < n; ++i) {
      es[i].a = 1;
      es[i].b = 2;
    }

    timer r(t, "h");
    for (int i = 0; i < n; ++i) {
      h_ii(es[i].a, es[i].b);
    }
  }
}

int main() {
  timings t;

  int n = 10000000;
  test_f_ii(t, n);
  test_g_ii(t, n);
  test_h_ii(t, n);
  test_f2_ii(t, n);

  std::cout << t.summarize("f", "h");
  std::cout << t.summarize("g", "h");
  std::cout << t.summarize("f", "g");
  std::cout << t.summarize("f", "f2");
  return 0;
}
