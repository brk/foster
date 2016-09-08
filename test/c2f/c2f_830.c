#include <stdio.h>

int main()
{
    const char* argv[] = { "example", "0", "12345678901234567890", "0xAbcDEf", "0B0", "0b1010101", "0x", NULL };
    int argc = 7;
    for (int i = 1; i < argc; ++i) {
        printf("%s\n", argv[i]);
    }
    return 0;
}
