/*
  Name:     rounding.c
  Purpose:  Demonstrates rounding modes.
  Author:   M. J. Fromberger <http://spinning-yarns.org/michael/>
  Info:     $Id: rounding.c 635 2008-01-08 18:19:40Z sting $

  Bugs:  The rounding mode can only be specified by value, not name.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>

#include "imath.h"
#include "imrat.h"

int main(int argc, char *argv[])
{
  mp_result  mode, len, res = 0;
  mp_size    prec, radix;
  mpq_t      value;
  char      *buf;

  if(argc < 5) {
    fprintf(stderr, "Usage: rounding <mode> <precision> <radix> <value>\n");
    return 1;
  }

  if((res = mp_rat_init(&value)) != MP_OK) {
    fprintf(stderr, "Error initializing: %s\n", mp_error_string(res));
    return 2;
  }

  mode = atoi(argv[1]);
  prec = atoi(argv[2]);
  radix = atoi(argv[3]);
  
  printf("Rounding mode:   %d\n"
	 "Precision:       %u digits\n"
	 "Radix:           %u\n"
	 "Input string:    \"%s\"\n", mode, prec, radix, argv[4]);
  
  if((res = mp_rat_read_decimal(&value, radix, argv[4])) != MP_OK) {
    fprintf(stderr, "Error reading input string: %s\n", 
	    mp_error_string(res));
    goto CLEANUP;
  }

  len = mp_rat_decimal_len(&value, radix, prec);
  buf = malloc(len);

  if((res = mp_rat_to_decimal(&value, radix, prec, mode, buf, len)) != MP_OK)
    fprintf(stderr, "Error converting output: %s\n",
	    mp_error_string(res));

  printf("Result string:   \"%s\"\n", buf);
  free(buf);

 CLEANUP:
  mp_rat_clear(&value);
  return res;
}

/* Here there be dragons */
