#include <stdio.h>
#include <stdint.h>

static int16_t func_31(uint32_t a, int32_t b) { return a + b; }

static uint32_t  func_1(uint16_t  p_12) {
    int32_t l_26 = 0x0031AA08;
    int32_t l_16 = 0xCF30836B;
    uint32_t l_59 = 0xDB7A8971;
    int32_t l_24 = (-1);
    if (0) return 0;
    func_31(1,2);
    (void)func_31(1,2);
    l_24 = ((int16_t)((int16_t)(((func_31(((int16_t)0x3CA4 << (int16_t)p_12), p_12) != l_26) || 0xCDD5) & l_16) << (int16_t)l_26) % (int16_t)l_59);
    return l_24;
}

int main() { printf("%d\n", func_1(0)); return 0; }
