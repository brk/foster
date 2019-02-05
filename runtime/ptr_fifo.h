template<int n>
class ptr_fifo {
  void* buf[n];
  unsigned read;
  unsigned size;
public:
  ptr_fifo()  {
      reset();
  }
  ~ptr_fifo() {}
  unsigned mask(unsigned x) { return x % n; }
  // Note: resets to being full of null pointers, *not* empty.
  void reset() { read = 0; size = 0; }
  bool empty() { return size == 0; }
  //size_t size() { return size; }
  bool full() { return size == n; }
  void* pull() { --size; auto prev = read; read = mask(read + 1); return buf[prev]; }
  void  push(void* p) { buf[mask(read + size)] = p; ++size; }
  // Precondition: full()
  void* pull_and_push(void* p) {
    void* old = buf[read];
    buf[read] = p;
    read = mask(read + 1);
    return old;
  }
};

class ptr_fifo_2 {
  void* buf[2];
  unsigned char read;
public:
  ptr_fifo_2()  { reset(); }
  ~ptr_fifo_2() {}
  void reset() { read = 0; buf[0] = 0; buf[1] = 0; }
  void* pull_and_push(void* p) {
    void* old = buf[read];
    buf[read] = p;
    read = read ^ 1;
    return old;
  }
};



/*
template<int n>
class ptr_fifo {
  void* buf[n];
  unsigned read;
  unsigned poke;
public:
  ptr_fifo()  {
      reset();
  }
  ~ptr_fifo() {}
  unsigned mask(unsigned x) { return x % n; }
  // Note: resets to being full of null pointers, *not* empty.
  void reset() { read = 0; poke = 0; }
  bool empty() { return poke == read; }
  size_t size() { return poke - read; }
  bool full() { return size() == n; }
  void* pull() { return buf[mask(read++)]; }
  void  push(void* p) { buf[mask(poke++)] = p; }
  void* pull_and_push(void* p) {
    if (full()) {
      void* old = pull();
      push(p);
      return old;
    } else {
      push(p);
      return nullptr;
    }
  }
};
*/
