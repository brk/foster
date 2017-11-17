// The Computer Language Benchmarks Game
// http://benchmarksgame.alioth.debian.org/
//
// http://benchmarksgame.alioth.debian.org/u32/program.php?test=mandelbrot&lang=gcc&id=9
//
// Contributed by Jeremy Zerfas

// This is the square of the limit that pixels will need to exceed in order to
// escape from the Mandelbrot set.
#define LIMIT_SQUARED      4.0
// This controls the maximum amount of iterations that are done for each pixel.
#define MAXIMUM_ITERATIONS   50

#include <stdint.h>
#include <stdlib.h>
#include <stdio.h>

// intptr_t should be the native integer type on most sane systems.
typedef intptr_t intnative_t;

int main(int argc, char ** argv){
   // Ensure image_Width_And_Height are multiples of 8.
   const intnative_t image_Width_And_Height=(atoi(argv[1])+7)/8*8;

   // Precompute the initial real and imaginary values for each x and y
   // coordinate in the image.
   double initial_r[image_Width_And_Height], initial_i[image_Width_And_Height];
   #pragma omp parallel for
   for(intnative_t xy=0; xy<image_Width_And_Height; xy++){
      initial_r[xy]=2.0/image_Width_And_Height*xy - 1.5;
      initial_i[xy]=2.0/image_Width_And_Height*xy - 1.0;
   }

   fprintf(stdout, "P4\n%jd %jd\n", (intmax_t)image_Width_And_Height,
     (intmax_t)image_Width_And_Height);

   int w = image_Width_And_Height;
   uint8_t byte = 0;
   for(intnative_t y=0; y < w; y++){
     double ci = (2.0 * (double)y) / ((double) w) - 1.0;
     for (int x = 0; x < w; ++x) {
       double cr = (2.0 * (double)x) / ((double) w) - 1.5;
       int flag = 1;
       double zr = 0; double zi = 0;
       for (int i = 0; i < MAXIMUM_ITERATIONS; ++i) {
          double zii = 2.0 * zr * zi + ci;
          zr = zr * zr - zi * zi + cr;
          zi = zii;
          if (zr * zr + zi * zi > LIMIT_SQUARED) {
            flag = 0;
            break;
          }
       }
       byte = (byte << 1) | flag;
       if ((x & 0x7) == 7) { fputc(byte, stdout); }
     }
     byte = 0;
   }

   return 0;
}
