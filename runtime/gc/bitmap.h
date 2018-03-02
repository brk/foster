#include <stdint.h>

class bitmap {
  /*
private:
  size_t num_bytes;
  uint8_t* bytes;
  */

public:
  /*
  bitmap(int num_bits) {
    // Invariant: can treat bytes as an array of uint64_t.
    num_bytes = roundUpToNearestMultipleWeak(num_bits / 8, 8);
    bytes = (uint8_t*) malloc(num_bytes);
  }

  ~bitmap() { free(bytes); bytes = 0; }

  void clear() { memset(bytes, 0, num_bytes); }
  */

  static uint8_t get_bit(size_t n, uint8_t* bytes) {
    size_t byte_offset = n / 8;
    size_t bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    uint8_t bit = (val >> bit_offset) & 1;
    return bit;
  }

  static void set_bit_to(size_t n, uint8_t bit, uint8_t* bytes) {
    size_t byte_offset = n / 8;
    size_t bit_offset  = n % 8;
    uint8_t val = bytes[byte_offset];
    bytes[byte_offset] = val | (bit << bit_offset);
  }
  /*

  uint8_t get_bit(int n) { return bitmap::get_bit(n, bytes); }
  void    set_bit(int n) {        bitmap::set_bit(n, bytes); }

  // For object start/finish bitmaps, we expect the bitmap to be dense
  // and thus this loop will execute a very small number of times, and
  // searching by byte is likely to be noise/overhead.
  int prev_bit_onebyone(int n) {
    while (n --> 0) {
      if (get_bit(n)) return n;
    }
    return -1;
  }
  */
};
