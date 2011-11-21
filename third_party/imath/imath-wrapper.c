/**
 * This file serves as a hook for LLVM to generate a Module
 * corresponding to the definitions in imath.h.
 *
 * In order for LLVM to have actual code to put in the Module,
 * we provide implementation wrappers around the function-like
 * macros from imath.h. Similarly, #define-d constants are
 * redefined as actual constants. In both cases, the non-macro
 * definitions have a "foster_" prefix to establish that they
 * are intended to be externally-availble symbols.
 *
 * Finally, in order to force LLVM to include declarations for
 * the functions from imath.h we wish to have included in the
 * Module, we have a function (force_inclusion_in_module) to
 * ensure that the declarations we want will appear in the Module.
 *
 **/

#include "_generated_/imath.h"

mp_digit* foster_mp_digits(mp_int z) { return MP_DIGITS(z); }
mp_size   foster_mp_alloc(mp_int z) { return MP_ALLOC(z); }
mp_size   foster_mp_used(mp_int z) { return MP_USED(z); }
mp_size   foster_mp_sign(mp_int z) { return MP_SIGN(z); }

const int foster_MP_DIGIT_BIT   = MP_DIGIT_BIT;
const int foster_MP_WORD_BIT    = MP_WORD_BIT;

int foster_mp_int_is_odd(mp_int z) { return mp_int_is_odd(z); }
int foster_mp_int_is_even(mp_int z) { return !foster_mp_int_is_odd(z); }

mp_result foster_mp_int_mod_value(mp_int a, mp_small v, mp_small* r) {
  return mp_int_mod_value(a, v, r);
}

mp_result foster_mp_int_sqrt(mp_int a, mp_int c) { return mp_int_sqrt(a, c); }

void force_inclusion_in_module() {
  mp_int a  = mp_int_alloc();
  mp_int b  = mp_int_alloc();
  mp_int c  = mp_int_alloc();
  mp_int q  = mp_int_alloc();
  mp_int r  = mp_int_alloc();
  mp_small sm;
  mp_small* p_sm = &sm;
  mp_int_init(a);

  mp_int_init_value(a, 0);
  mp_int_set_value(a, 0);
  mp_int_init_copy(c, a);
  mp_int_to_int(a, p_sm);

  mp_int_clear(a);
  mp_int_free(a);

  mp_int_copy(c, a);
  mp_int_swap(c, a);
  mp_int_zero(a);

  mp_int_abs(a, c);
  mp_int_neg(a, c);
  mp_int_add(a, b, c);
  mp_int_add_value(a, 0, c);

  mp_int_sub(a, b, c);
  mp_int_sub_value(a, 0, c);

  mp_int_mul(a, b, c);
  mp_int_mul_value(a, 0, c);
  mp_int_mul_pow2(a, 0, c);

  mp_int_sqr(a, c);

  mp_int_div(a, b, q, r);
  mp_int_div_value(a, 0, q, p_sm);
  mp_int_div_pow2(a, 0, q, r);
  mp_int_mod(a, b, c);

  mp_int_expt(a, 3, c);
  mp_int_expt_value(4, 3, c);

  mp_int_compare(a, b);
  mp_int_compare_unsigned(a, b);
  mp_int_compare_zero(a);
  mp_int_compare_value(a, 1);

  mp_int_divisible_value(a, 3);
  mp_int_is_pow2(a);

  mp_result res;
  res = MP_OK;
  res = MP_FALSE;
  res = MP_TRUE;
  res = MP_MEMORY;
  res = MP_RANGE;
  res = MP_TRUNC;
  res = MP_UNDEF;
  res = MP_BADARG;
  res = MP_MINERR;
}

// TODO: these should be translated into functions with signatures like
// tryConvertIntTo_i32 :: Int => Maybe i32
/* Convert to a small int, if representable; else MP_RANGE */
//mp_result mp_int_to_int(mp_int z, mp_small *out);
//mp_result mp_int_to_uint(mp_int z, mp_usmall *out);


//mp_result mp_int_init_size(mp_int z, mp_size prec);
//mp_result mp_int_exptmod(mp_int a, mp_int b, mp_int m,
//			 mp_int c);                    /* c = a^b (mod m) */
//mp_result mp_int_exptmod_evalue(mp_int a, mp_small value,
//				mp_int m, mp_int c);   /* c = a^v (mod m) */
//mp_result mp_int_exptmod_bvalue(mp_small value, mp_int b,
//				mp_int m, mp_int c);   /* c = v^b (mod m) */
//mp_result mp_int_exptmod_known(mp_int a, mp_int b,
//			       mp_int m, mp_int mu,
//			       mp_int c);              /* c = a^b (mod m) */
//mp_result mp_int_redux_const(mp_int m, mp_int c);
//
//mp_result mp_int_invmod(mp_int a, mp_int m, mp_int c); /* c = 1/a (mod m) */
//
//mp_result mp_int_gcd(mp_int a, mp_int b, mp_int c);    /* c = gcd(a, b)   */
//
//mp_result mp_int_egcd(mp_int a, mp_int b, mp_int c,    /* c = gcd(a, b)   */
//		      mp_int x, mp_int y);             /* c = ax + by     */
//
//mp_result mp_int_lcm(mp_int a, mp_int b, mp_int c);    /* c = lcm(a, b)   */
//
//mp_result mp_int_root(mp_int a, mp_small b, mp_int c);


/* *************** IO operations, handled by the runtime ******************/

///* Convert to nul-terminated string with the specified radix, writing at
//   most limit characters including the nul terminator  */
//mp_result mp_int_to_string(mp_int z, mp_size radix,
//			   char *str, int limit);
//
///* Return the number of characters required to represent
//   z in the given radix.  May over-estimate. */
//mp_result mp_int_string_len(mp_int z, mp_size radix);
//
///* Read zero-terminated string into z */
//mp_result mp_int_read_string(mp_int z, mp_size radix, const char *str);
//mp_result mp_int_read_cstring(mp_int z, mp_size radix, const char *str,
//			      char **end);
//
///* Return the number of significant bits in z */
//mp_result mp_int_count_bits(mp_int z);
//
///* Convert z to two's complement binary, writing at most limit bytes */
//mp_result mp_int_to_binary(mp_int z, unsigned char *buf, int limit);
//
///* Read a two's complement binary value into z from the given buffer */
//mp_result mp_int_read_binary(mp_int z, unsigned char *buf, int len);
//
///* Return the number of bytes required to represent z in binary. */
//mp_result mp_int_binary_len(mp_int z);
//
///* Convert z to unsigned binary, writing at most limit bytes */
//mp_result mp_int_to_unsigned(mp_int z, unsigned char *buf, int limit);
//
///* Read an unsigned binary value into z from the given buffer */
//mp_result mp_int_read_unsigned(mp_int z, unsigned char *buf, int len);
//
///* Return the number of bytes required to represent z as unsigned output */
//mp_result mp_int_unsigned_len(mp_int z);
//
///* Return a statically allocated string describing error code res */
//const char *mp_error_string(mp_result res);
