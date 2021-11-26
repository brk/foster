// Copyright (c) 2021 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdio>
#include <cstring> // for strlen
#include <cstdlib> // for malloc/free

#include "libfoster.h"

extern "C" {
FILE* c2f_stdin__autowrap() { return stdin; }
FILE* c2f_stdout__autowrap() { return stdout; }
FILE* c2f_stderr__autowrap() { return stderr; }

FILE* CFile_nil__autowrap() { return NULL; }
bool CFile_isnil__autowrap(FILE* f) { return f == NULL; }

// Copies a byte array (Array Int8) from the Foster heap
// to the C heap, adding a null terminator.
char* foster__cstr(foster_bytes* not_assumed_null_terminated) {
  size_t len = not_assumed_null_terminated->cap;
  char* rv = (char*) malloc(len + 1);
  memcpy(rv, not_assumed_null_terminated->bytes, len);
  rv[len] = '\0';
  return rv;
}

// Yields a direct pointer into the Foster heap,
// typed for use in C. Note that the returned C pointer
// does not point to a null terminated buffer!
char* foster__cdataptr_unsafe(foster_bytes* b, int32_t offset) {
  return (char*) &b->bytes[0] + offset;
}

void foster__cstr_free(char* s) { free(s); }


// Currently unused
double foster_strtof64(foster_bytes* b, int32_t roundmode) {
  char* c = foster__cstr(b);
  double f = atof(c);
  free(c);
  return f;
}

// Currently unused
void* foster_gdtoa64__autowrap(double f, int32_t mode, int32_t ndig, int32_t rounding, int32_t* decpt) {
  char buf[64];
  sprintf(buf, "%g", f);
  return foster_emit_string_of_cstring(buf, strlen(buf));
}



void* foster_sprintf_i32__autowrap(int32_t x, int8_t specifier, int8_t flag,
                         int32_t width, int32_t precision) {
  char fmt[256];
  char buf[512];
  const char* flagc =
                (flag ==  0) ? "" : // no flags; default
                (flag ==  1) ? "+" : // signed positives
                (flag ==  2) ? " " : // space before positives
                (flag ==  3) ? "#" : // 0x prefix (not meaningful for d)
                (flag ==  4) ? "0" : // left pad with zeros not spaces
                (flag == 10) ? "-" : // as above, but left justified.
                (flag == 11) ? "-+" : 
                (flag == 12) ? "- " : 
                (flag == 13) ? "-#" : 
                (flag == 14) ? "-0" : "";
  if (!(specifier == 'd' || specifier == 'x' || specifier == 'X'
     || specifier == 'u' || specifier == 'c')) { specifier = 'd'; }

  if (precision < 0) {
    int status = sprintf(fmt, "%%%s%d%c", flagc, width, specifier);
    //                         ^^ ^ ^ ^
    //                         |/ | |  specifier 
    //                         |  | width
    //                         |  flags
    //                         ^^ literal percent sign
    if (status < 0 || status == 256) {
      foster__assert(false, "error in foster_sprintf_i32");
    }
  } else {
    int status = sprintf(fmt, "%%%s%d.%d%c", flagc, width, precision, specifier);
    //                         ^^ ^ ^ ^  ^
    //                         |/ | | |  specifier 
    //                         |  | | precision
    //                         |  | width
    //                         |  flags
    //                         ^^ literal percent sign
    if (status < 0 || status == 256) {
      foster__assert(false, "error in foster_sprintf_i32");
    }
  }
  int rv = snprintf(buf, 512, fmt, x);
  return foster_emit_string_of_cstring(buf, strlen(buf));
}

void* foster_sprintf_i64__autowrap(int64_t x, int8_t specifier, int8_t flag,
                         int32_t width, int32_t precision) {
  char fmt[256];
  char buf[512];
  const char* flagc =
                (flag ==  0) ? "" : // no flags; default
                (flag ==  1) ? "+" : // signed positives
                (flag ==  2) ? " " : // space before positives
                (flag ==  3) ? "#" : // 0x prefix (not meaningful for d)
                (flag ==  4) ? "0" : // left pad with zeros not spaces
                (flag == 10) ? "-" : // as above, but left justified.
                (flag == 11) ? "-+" : 
                (flag == 12) ? "- " : 
                (flag == 13) ? "-#" : 
                (flag == 14) ? "-0" : "";
  if (!(specifier == 'd' || specifier == 'x' || specifier == 'X'
     || specifier == 'u' || specifier == 'c')) { specifier = 'd'; }

  if (precision < 0) {
    int status = sprintf(fmt, "%%%s%dll%c", flagc, width, specifier);
    //                         ^^ ^ ^ ^
    //                         |/ | |  specifier 
    //                         |  | width
    //                         |  flags
    //                         ^^ literal percent sign
    if (status < 0 || status == 256) {
      foster__assert(false, "error in foster_sprintf_i64");
    }
  } else {
    int status = sprintf(fmt, "%%%s%d.%dll%c", flagc, width, precision, specifier);
    //                         ^^ ^ ^ ^  ^
    //                         |/ | | |  specifier 
    //                         |  | | precision
    //                         |  | width
    //                         |  flags
    //                         ^^ literal percent sign
    if (status < 0 || status == 256) {
      foster__assert(false, "error in foster_sprintf_i64");
    }
  }
  int rv = snprintf(buf, 512, fmt, x);
  return foster_emit_string_of_cstring(buf, strlen(buf));
}

}
