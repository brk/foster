// Copyright (c) 2010 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <iostream>
#include "cycle.h"
#include <cstdlib>

using namespace std;

struct Base {
  virtual void func() = 0;
};

struct D1 : public Base { virtual void func() {} };
struct D2 : public Base { virtual void func() {} };
struct D3 : public Base { virtual void func() {} };

extern void f1();
extern void f2();
extern void f3();

const int N = 1024;

typedef int* IntPtr;
int** random_ints() {
  int** ints = new IntPtr[N];
  for (int i = 0; i < N; ++i) {
    ints[i] = new int((rand()%3) + 1);
  }
  return ints;
}

typedef Base* BasePtr;
BasePtr* random_Ds() {
  BasePtr* Ds = new BasePtr[N];
  for (int i = 0; i < N; ++i) {
    switch( rand() % 3 ) {
      case 1:  Ds[i] = new D1(); break;
      case 2:  Ds[i] = new D2(); break;
      default: Ds[i] = new D3(); break;
    }
  }
  return Ds;
}

double withdirect(int C) {
  ticks start = getticks();
  for (int j = 0; j < N * C; ++j) {
    for (int i = 0; i < N; ++i) {
      f1();
    }
  }
  ticks end = getticks();
  return elapsed(end, start);
}

double withswitch(int C) {
  int** ints = random_ints();

  ticks start = getticks();
  for (int j = 0; j < N * C; ++j) {
    for (int i = 0; i < N; ++i) {
      switch(*ints[i]) {
        case 1: f1(); break;
        case 2: f2(); break;
        case 3: f3(); break;
        default: exit(1);
      }
    }
  }
  ticks end = getticks();
  return elapsed(end, start);
}

double withvtable(int C) {
  Base** Ds = random_Ds();

  ticks start = getticks();
  for (int j = 0; j < N * C; ++j) {
    for (int i = 0; i < N; ++i) {
      Ds[i]->func();
    }
  }
  ticks end = getticks();
  return elapsed(end, start);
}

int main() {
  const int C = 128;
  double dtime = withdirect(C);
  double stime = withswitch(C);
  double vtime = withvtable(C);
  double mintime = std::min(dtime, std::min(stime, vtime));
  std::cout << "direct time: " << (dtime / mintime) << "\n";
  std::cout << "switch time: " << (stime / mintime) << "\n";
  std::cout << "vtable time: " << (vtime / mintime) << "\n";
  return 0;
}

