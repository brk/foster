#include <iostream>
#include <sstream>
#include <cstdio>
#include <string>
#include <vector>

using namespace std;

struct SHA256 {
  SHA256() { reset(); }
  SHA256(const void* values, unsigned size) : SHA256() { data(values, size); }

  auto reset() -> void {
    for(auto n : input) n = 0;
    for(auto n : w) n = 0;
    for (int i = 0; i < 8; ++i) h[i] = square(i);
    queued = length = 0;
  }

  auto data(uint8_t value) -> void {
    byte(value);
    length++;
  }

  auto data(const void* values, unsigned size) -> void {
    length += size;
    auto p = (const uint8_t*)values;
    while(size--) byte(*p++);
  }

  auto value() const -> vector<uint8_t> {
    SHA256 self(*this);
    self.finish();
    vector<uint8_t> result;
    for(int n = 0; n < 32; ++n) result.push_back(self.h[n >> 2] >> ((3 - (n & 3)) << 3));
    return result;
  }

private:
  auto byte(uint8_t value) -> void {
    auto shift = (3 - (queued & 3)) * 8;
    input[queued >> 2] &= ~(0xff << shift);
    input[queued >> 2] |= (value << shift);
    if(++queued == 64) block(), queued = 0;
  }

  auto block() -> void {
    for(int n = 0; n < 16; ++n) w[n] = input[n];
    for(int n = 16; n < 64; ++n) {
      uint32_t a = ror(w[n - 15],  7) ^ ror(w[n - 15], 18) ^ (w[n - 15] >>  3);
      uint32_t b = ror(w[n -  2], 17) ^ ror(w[n -  2], 19) ^ (w[n -  2] >> 10);
      w[n] = w[n - 16] + w[n - 7] + a + b;
    }
    uint32_t t[8];
    for(int n = 0; n < 8; ++n) t[n] = h[n];
    for(int n = 0; n < 64; ++n) {
      uint32_t a = ror(t[0], 2) ^ ror(t[0], 13) ^ ror(t[0], 22);
      uint32_t b = ror(t[4], 6) ^ ror(t[4], 11) ^ ror(t[4], 25);
      uint32_t c = (t[0] & t[1]) ^ (t[0] & t[2]) ^ (t[1] & t[2]);
      uint32_t d = (t[4] & t[5]) ^ (~t[4] & t[6]);
      uint32_t e = t[7] + w[n] + cube(n) + b + d;
      t[7] = t[6]; t[6] = t[5]; t[5] = t[4]; t[4] = t[3] + e;
      t[3] = t[2]; t[2] = t[1]; t[1] = t[0]; t[0] = a + c + e;
    }
    for (int n = 0; n < 8; ++n)h[n] += t[n];
  }

  auto finish() -> void {
    byte(0x80);
    while(queued != 56) byte(0x00);
    for (int n = 0; n < 8; ++n)byte((length << 3) >> ((7 - n) << 3));
  }

  auto ror(uint32_t x, uint32_t n) -> uint32_t {
    return (x >> n) | (x << (32 - n));
  }

  auto square(unsigned n) -> uint32_t {
    static const uint32_t value[8] = {
      0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
    };
    return value[n];
  }

  auto cube(unsigned n) -> uint32_t {
    static const uint32_t value[64] = {
      0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
      0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
      0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
      0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
      0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
      0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
      0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
      0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
    };
    return value[n];
  }

  uint32_t input[16];
  uint32_t queued;
  uint32_t w[64];
  uint32_t h[8];
  uint64_t length;
};

std::string slurpInput() {
  ios_base::sync_with_stdio(false);
/*
  stringstream ss;
  string line;
  while (cin) { getline(cin, line); ss << line << "\n"; }
  return ss.str();
  */

  stringstream ss; ss << cin.rdbuf();
  return ss.str();
}

int main () {
  SHA256 sha;
  std::string s = slurpInput();
  sha.data(s.c_str(), s.size());
  std::vector<uint8_t> v = sha.value();
  for (int i = 0; i < v.size(); ++i) { printf("%02x", v[i]); }
  printf("\n");
  return 0;
}

/* Reference C++ code:

 Performance counter stats for './sha256.cpp.exe':

        438.362945      task-clock (msec)         #    0.997 CPUs utilized          
                 2      context-switches          #    0.005 K/sec                  
                 0      cpu-migrations            #    0.000 K/sec                  
             3,963      page-faults               #    0.009 M/sec                  
     1,534,243,082      cycles                    #    3.500 GHz                    
     4,673,492,997      instructions              #    3.05  insn per cycle         
       197,979,989      branches                  #  451.635 M/sec                  
         2,387,930      branch-misses             #    1.21% of all branches        

       0.439770452 seconds time elapsed


Foster code (with appropriate lambda lifting and eliminated bounds checks): 16% overhead

 Performance counter stats for './test-tmpdir/sha256/sha256':

        509.656307      task-clock (msec)         #    0.997 CPUs utilized          
                 4      context-switches          #    0.008 K/sec                  
                 0      cpu-migrations            #    0.000 K/sec                  
             3,331      page-faults               #    0.007 M/sec                  
     1,783,763,206      cycles                    #    3.500 GHz                    
     5,640,198,811      instructions              #    3.16  insn per cycle         
       305,386,991      branches                  #  599.202 M/sec                  
         2,398,063      branch-misses             #    0.79% of all branches        

       0.510941253 seconds time elapsed

With above optimizations, and disabled GC code:
 Performance counter stats for './test-tmpdir/sha256/sha256 --foster-heap-MB 64': 7% overhead

        470.121803      task-clock (msec)         #    0.996 CPUs utilized          
                 8      context-switches          #    0.017 K/sec                  
                 1      cpu-migrations            #    0.002 K/sec                  
             3,336      page-faults               #    0.007 M/sec                  
     1,645,365,545      cycles                    #    3.500 GHz                    
     5,680,563,229      instructions              #    3.45  insn per cycle         
       304,664,670      branches                  #  648.055 M/sec                  
         2,396,274      branch-misses             #    0.79% of all branches        

       0.472141513 seconds time elapsed

   */
