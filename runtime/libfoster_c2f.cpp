// Copyright (c) 2021 Ben Karel. All rights reserved.
// Use of this source code is governed by a BSD-style license that can be
// found in the LICENSE.txt file or at http://eschew.org/txt/bsd.txt

#include <cstdio>
#include <cstring> // for strlen

#include "libfoster.h"

extern "C" {
FILE* c2f_stdin__autowrap() { return stdin; }
FILE* c2f_stdout__autowrap() { return stdout; }
FILE* c2f_stderr__autowrap() { return stderr; }

FILE* CFile_nil() { return NULL; }
bool CFile_isnil__autowrap(FILE* f) { return f == NULL; }


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
