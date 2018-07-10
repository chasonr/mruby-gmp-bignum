/* bignum-gem.c */

#include <ctype.h>
#include <limits.h>
#include <math.h>
#include <stdint.h>
#include <stdlib.h>
#include <mruby.h>
#include <mruby/array.h>
#include <mruby/class.h>
#include <mruby/data.h>
#include <mruby/string.h>
#include "gmp.h"

/* Enable default conversion to Fixnum if this is true */
#ifdef MRB_BIGNUM_INTEGRATION
#define FIXNUM_CONVERT TRUE
#else
#define FIXNUM_CONVERT FALSE
#endif

#if MRB_INT_BIT == 16
  typedef uint16_t mrb_uint;
#elif MRB_INT_BIT == 32
  typedef uint32_t mrb_uint;
#else
  typedef uint64_t mrb_uint;
#endif

/* For the math functions */
#ifdef MRB_USE_FLOAT
# define F(x) x##f
#else
# define F(x) x
#endif

struct Bignum {
  mpz_t num;
};

#define MPZ(x) (((struct Bignum *)DATA_PTR(x))->num)

/* Free memory belonging to a Bignum */
static void
bn_free(mrb_state *mrb, void *num_)
{
  struct Bignum *num = (struct Bignum *)num_;
  mpz_clear(num->num);
  mrb_free(mrb, num);
}

/* Data type structure for the class */
static struct mrb_data_type bignum_type = {
  "Bignum", bn_free
};

/* Identify the object as a numeric type */
enum num_type {
  num_none,
  num_fixnum,
  num_bignum,
  num_float
};

static enum num_type
num_identify(mrb_state *mrb, mrb_value obj)
{
  switch (mrb_type(obj)) {
  case MRB_TT_FIXNUM:
    return num_fixnum;
  case MRB_TT_FLOAT:
    return num_float;
  case MRB_TT_DATA:
    return DATA_TYPE(obj) == &bignum_type ? num_bignum : num_none;
  default:
    return num_none;
  }
}

static void
uint64_to_bignum(mpz_t big, uint64_t fix)
{
  if (fix <= ULONG_MAX) {
    mpz_set_ui(big, (unsigned long)fix);
  } else {
    mpz_set_ui(big, fix >> 32);
    mpz_mul_2exp(big, big, 32);
    mpz_add_ui(big, big, (unsigned long)fix & 0xFFFFFFFF);
  }
}

static void
int64_to_bignum(mpz_t big, int64_t fix)
{
  if (fix < 0) {
    mpz_set_ui(big, -fix >> 32);
    mpz_mul_2exp(big, big, 32);
    mpz_add_ui(big, big, (unsigned long)-fix & 0xFFFFFFFF);
    mpz_neg(big, big);
  } else {
    mpz_set_ui(big, +fix >> 32);
    mpz_mul_2exp(big, big, 32);
    mpz_add_ui(big, big, (unsigned long)+fix & 0xFFFFFFFF);
  }
}

/* Convert a Bignum to int64_t; return INT64_MIN if not possible */
/* For the <<, >> and ** operators when the right side is a Bignum */
static int64_t
bignum_to_int64(mpz_t num)
{
  /* Quick conversion for numbers fitting in signed long */
  if (mpz_fits_slong_p(num)) {
    return mpz_get_si(num);
  }

#if INT64_MIN < LONG_MIN || LONG_MAX < INT64_MAX
  /* Check for number outside of bignum limits */
  {
    mrb_bool big_ok;
    mpz_t limit;
    mpz_init_set_ui(limit, 1);
    mpz_mul_2exp(limit, limit, 63);
    big_ok = mpz_cmp(num, limit) > 0;
    if (big_ok) {
      mpz_neg(limit, limit);
      big_ok = mpz_cmp(num, limit) < 0;
    }
    mpz_clear(limit);
    if (!big_ok) { return INT64_MIN; }
  }

  /* OK to convert */
  /* This can only be reached if long is less than 64 bits */
  {
    mpz_t upper, lower;
    unsigned long ufix, lfix;
    uint64_t fix;

    mpz_init(upper);
    mpz_init(lower);
    mpz_tdiv_q_2exp(upper, num, 32);
    mpz_tdiv_r_2exp(lower, num, 32);
    ufix = mpz_get_ui(upper);
    lfix = mpz_get_ui(lower);
    fix = ((uint64_t)ufix << 32) | lfix;
    mpz_clear(upper);
    mpz_clear(lower);
    return mpz_cmp_ui(num, 0) < 0 ? (int64_t)-fix : (int64_t)+fix;
  }
#else
  return INT64_MIN;
#endif
}

/* Convert a Bignum to a Fixnum; return nil if not possible */
static mrb_value
bignum_to_fixnum(mpz_t num)
{
  /* Quick conversion for numbers fitting in signed long */
  if (mpz_fits_slong_p(num)) {
    long fix = mpz_get_si(num);
    if (MRB_INT_MIN <= fix && fix <= MRB_INT_MAX) {
      return mrb_fixnum_value((mrb_int)fix);
    }
    else {
      /* Reached only if mrb_int is smaller than long */
      return mrb_nil_value();
    }
  }

#if MRB_INT_MIN < LONG_MIN || LONG_MAX < MRB_INT_MAX
  /* Check for number outside of bignum limits */
  /* TODO:  always fails if mrb_int is at least as large as long */
  {
    mrb_bool big_ok;
    mpz_t limit;

    /* Lower limit:  -(2**(MRB_INT_BIT-1)) */
    mpz_init_set_si(limit, -1);
    mpz_mul_2exp(limit, limit, MRB_INT_BIT - 1);
    big_ok = mpz_cmp(num, limit) >= 0;
    /* Upper limit:  +(2**(MRB_INT_BIT-1)) - 1 */
    if (big_ok) {
      mpz_neg(limit, limit);
      big_ok = mpz_cmp(num, limit) >= 0;
    }
    mpz_clear(limit);
    if (!big_ok) {
      return mrb_nil_value();
    }
  }

  /* OK to convert */
  /* This can only be reached if Fixnum is 64 bits and long is less than that */
  {
    mpz_t upper, lower;
    unsigned long ufix, lfix;
    uint64_t fix;

    mpz_init(upper);
    mpz_init(lower);
    mpz_tdiv_q_2exp(upper, num, 32);
    mpz_tdiv_r_2exp(lower, num, 32);
    ufix = mpz_get_ui(upper);
    lfix = mpz_get_ui(lower);
    fix = ((uint64_t)ufix << 32) | lfix;
    mpz_clear(upper);
    mpz_clear(lower);
    return mrb_fixnum_value(
          mpz_cmp_ui(num, 0) < 0 ? (mrb_int)-fix : (mrb_int)+fix);
  }
#else
  return mrb_nil_value();
#endif
}

/* Create a new Bignum or Fixnum as a Ruby object */
static mrb_value
new_bignum(mrb_state *mrb, mpz_t num, mrb_bool fixnum_conv)
{
  struct Bignum *b;

  /* Can we return a Fixnum? */
  if (fixnum_conv) {
    mrb_value fix = bignum_to_fixnum(num);
    if (mrb_fixnum_p(fix)) {
      /* Return a Fixnum */
      return fix;
    }
  }

  /* Return a Bignum */
  b = mrb_malloc(mrb, sizeof(*b));
  mpz_init_set(b->num, num);
  return mrb_obj_value(mrb_data_object_alloc(mrb,
        mrb_class_get(mrb, "Bignum"), b, &bignum_type));
}

/* ------------------------------------------------------------------------*/
/* "<=>" */
/* ------------------------------------------------------------------------*/

/* Use when the right hand side is not Integer or Float */
static mrb_value
cmp_coerce(mrb_state *mrb, mrb_value self, mrb_value other)
{
  mrb_value v;

  if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "coerce"))) {
    mrb_raise(mrb, E_ARGUMENT_ERROR, "float expected");
  }

  v = mrb_funcall(mrb, other, "coerce", 1, self);
  if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
    mrb_value f = mrb_ary_entry(v, 0);
    mrb_value s = mrb_ary_entry(v, 1);
    return mrb_funcall(mrb, f, "<=>", 1, s);
  }
  else {
    return mrb_nil_value();
  }
}

/* Bignum <=> Fixnum */
static int
big_fix_cmp(mrb_state *mrb, mrb_value left, mrb_int right)
{
#if MRB_INT_MIN < LONG_MIN || LONG_MAX < MRB_INT_MAX
  if (right < LONG_MIN || LONG_MAX < right) {
    /* Use this if the Fixnum won't fit in signed long */
    int cmp;
    mpz_t bigright;

    mpz_init(bigright);
    int64_to_bignum(bigright, right);
    cmp = mpz_cmp(MPZ(left), bigright);
    mpz_clear(bigright);
    return cmp;
  }
#endif

  return mpz_cmp_si(MPZ(left), (long)right);
}

/* Fixnum <=> Float */
static int
cmp_fix_flt(mrb_state *mrb, mrb_int left, mrb_float right)
{
  if (left < right) {
    return -1;
  }
  else if (left > right) {
    return +1;
  }
  else {
    return 0;
  }
}

/* 15.2.8.3.1  Fixnum#<=> */
static mrb_value
fixnum_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  int cmp;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum <=> Fixnum */
    {
      mrb_int fixother = mrb_fixnum(other);
      if (fixself < fixother) {
        cmp = -1;
      }
      else if (fixself > fixother) {
        cmp = +1;
      }
      else {
        cmp = 0;
      }
    }
    break;
  case num_bignum:
    /* Fixnum <=> Bignum */
    cmp = -big_fix_cmp(mrb, other, fixself);
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

static mrb_value
fixnum_lt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = fixnum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) < 0);
}

static mrb_value
fixnum_le(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = fixnum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) <= 0);
}

static mrb_value
fixnum_gt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = fixnum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) > 0);
}

static mrb_value
fixnum_ge(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = fixnum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) >= 0);
}

/* 15.2.8.3.1  Bignum#<=> */
static mrb_value
bignum_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  int cmp;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum <=> Fixnum */
    cmp = +big_fix_cmp(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum <=> Bignum */
    cmp = mpz_cmp(MPZ(self), MPZ(other));
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

static mrb_value
bignum_lt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = bignum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) < 0);
}

static mrb_value
bignum_le(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = bignum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) <= 0);
}

static mrb_value
bignum_gt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = bignum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) > 0);
}

static mrb_value
bignum_ge(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = bignum_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) >= 0);
}

/* 15.2.8.3.1  Float#<=> */
static mrb_value
float_cmp(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  int cmp;

  if (isnan(fltself)) {
    return mrb_nil_value();
  }

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float <=> Fixnum */
    {
      mrb_float fixother = mrb_fixnum(other);
      cmp = -cmp_fix_flt(mrb, fixother, fltself);
    }
    break;
  case num_bignum:
    /* Float <=> Bignum */
    cmp = -mpz_cmp_d(MPZ(other), fltself);
    break;
  case num_float:
    /* Float <=> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (isnan(fltother)) {
        return mrb_nil_value();
      }
      if (fltself < fltother) {
        cmp = -1;
      }
      else if (fltself > fltother) {
        cmp = +1;
      }
      else {
        cmp = 0;
      }
    }
    break;
  default:
    return cmp_coerce(mrb, self, other);
  }

  return mrb_fixnum_value(cmp);
}

static mrb_value
float_lt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = float_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) < 0);
}

static mrb_value
float_le(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = float_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) <= 0);
}

static mrb_value
float_gt(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = float_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) > 0);
}

static mrb_value
float_ge(mrb_state *mrb, mrb_value self)
{
  mrb_value cmp = float_cmp(mrb, self);
  return mrb_bool_value(mrb_fixnum(cmp) >= 0);
}

/* ------------------------------------------------------------------------*/
/* "==" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.2  Integer#== */
static mrb_value
fixnum_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum == Fixnum */
    eq = fixself == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Fixnum == Bignum */
    eq = big_fix_cmp(mrb, other, fixself) == 0;
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* 15.2.8.3.2  Integer#== */
static mrb_value
bignum_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum == Fixnum */
    eq = big_fix_cmp(mrb, self, mrb_fixnum(other)) == 0;
    break;
  case num_bignum:
    /* Bignum == Bignum */
    eq = mpz_cmp(MPZ(self), MPZ(other)) == 0;
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* 15.2.9.3.2  Float#== */
static mrb_value
float_eq(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_bool eq;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float == Fixnum */
    eq = fltself == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Float == Bignum */
    eq = mpz_cmp_d(MPZ(other), fltself) == 0;
    break;
  case num_float:
    /* Float == Float */
    eq = fltself == mrb_float(other);
    break;
  default:
    return mrb_funcall(mrb, other, "==", 1, self);
  }

  return mrb_bool_value(eq);
}

/* ------------------------------------------------------------------------*/
/* "+" */
/* ------------------------------------------------------------------------*/

/* Coerce operands when the right side is not Integer or Float */
static mrb_value
op_coerce(mrb_state *mrb, mrb_value x, mrb_value y, char const *op)
{
  mrb_value v;

  if (!mrb_respond_to(mrb, y, mrb_intern_lit(mrb, "coerce"))) {
    mrb_raise(mrb, E_TYPE_ERROR, "expected Numeric");
  }

  v = mrb_funcall(mrb, y, "coerce", 1, x);
  if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
    mrb_value f = mrb_ary_entry(v, 0);
    mrb_value s = mrb_ary_entry(v, 1);
    return mrb_funcall(mrb, f, op, 1, s);
  }
  else {
    mrb_raise(mrb, E_TYPE_ERROR, "expected Numeric");
    return mrb_nil_value();
  }
}

/* Fixnum + Fixnum */
static mrb_value
fix_fix_plus(mrb_state *mrb, mrb_int x, mrb_int y, mrb_bool subtract)
{
  mrb_bool sx, sy;
  mrb_uint ux, uy;
  mrb_bool ssum;
  mrb_uint usum;
  mrb_value sum;

#ifndef MRB_WORD_BOXING
  /* Because overflow in signed arithmetic invokes undefined behavior, the
     signed arithmetic is converted to unsigned.  This has the added effect
     of avoiding overflow altogether, except in one single corner case; and
     even that does not occur if word boxing is enabled, because that narrows
     Fixnum by one bit without changing the mrb_uint type. */
  if (!subtract && x == MRB_INT_MIN && y == MRB_INT_MIN) {
    mpz_t bsum;
    mpz_init_set_si(bsum, -1);
    mpz_mul_2exp(bsum, bsum, MRB_INT_BIT);
    sum = new_bignum(mrb, bsum, TRUE);
    mpz_clear(bsum);
    return sum;
  }
#endif

  sx = x < 0;
  ux = x < 0 ? -(mrb_uint)x : +(mrb_uint)x;
  sy = (y < 0) ^ (subtract != 0);
  uy = y < 0 ? -(mrb_uint)y : +(mrb_uint)y;
  if (sx == sy) {
    /* Add */
    ssum = sx;
    usum = ux + uy;
  }
  else {
    /* Subtract */
    if (ux >= uy) {
      ssum = sx;
      usum = ux - uy;
    }
    else {
      ssum = sy;
      usum = uy - ux;
    }
  }
  /* Propagate carry */
  if (( ssum && usum > (mrb_uint)MRB_INT_MAX+1)
  ||  (!ssum && usum > (mrb_uint)MRB_INT_MAX+0)) {
    /* Overflow; return a Bignum */
    mpz_t bsum;
    mpz_init(bsum);
    uint64_to_bignum(bsum, usum);
    if (ssum) {
      mpz_neg(bsum, bsum);
    }
    sum = new_bignum(mrb, bsum, TRUE);
  }
  else {
    /* Return a Fixnum */
    sum = mrb_fixnum_value((mrb_int)(ssum ? -usum : +usum));
  }

  return sum;
}

/* Bignum + Fixnum */
static mrb_value
big_fix_plus(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);

#if MRB_INT_MIN < LONG_MIN || LONG_MAX < MRB_INT_MAX
  if (right < LONG_MIN || LONG_MAX < right) {
    /* Use this if the Fixnum won't fit in signed long */
    mpz_t bigright;

    mpz_init(bigright);
    int64_to_bignum(bigright, right);
    mpz_add(sum, MPZ(left), bigright);
    mpz_clear(bigright);
  }
  else
#endif
  {
    if (right >= 0) {
      mpz_add_ui(sum, MPZ(left), +(unsigned long)right);
    }
    else {
      mpz_sub_ui(sum, MPZ(left), -(unsigned long)right);
    }
  }

  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* Bignum + Bignum */
static mrb_value
big_big_plus(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);
  mpz_add(sum, DATA_PTR(left), DATA_PTR(right));
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* 15.2.8.3.3  Integer#+ */
static mrb_value
fixnum_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum + Fixnum */
    out = fix_fix_plus(mrb, fixself, mrb_fixnum(other), FALSE);
    break;
  case num_bignum:
    /* Fixnum + Bignum */
    out = big_fix_plus(mrb, other, fixself);
    break;
  case num_float:
    /* Fixnum + Float */
    out = mrb_float_value(mrb, fixself + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* 15.2.8.3.3  Integer#+ */
static mrb_value
bignum_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum + Fixnum */
    out = big_fix_plus(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum + Bignum */
    out = big_big_plus(mrb, self, other);
    break;
  case num_float:
    /* Bignum + Float */
    out = mrb_float_value(mrb, mpz_get_d(MPZ(self)) + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* 15.2.9.3.3  Float#+ */
static mrb_value
float_plus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float + Fixnum */
    out = mrb_float_value(mrb, fltself + mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float + Bignum */
    out = mrb_float_value(mrb, fltself + mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Float + Float */
    out = mrb_float_value(mrb, fltself + mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "+");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "-" */
/* ------------------------------------------------------------------------*/

/* Fixnum - Bignum */
static mrb_value
fix_big_minus(mrb_state *mrb, mrb_int left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);

  if (left < 0 || ULONG_MAX < left) {
    /* Use this if the Fixnum won't fit in unsigned long */
    mpz_t bigleft;

    mpz_init(bigleft);
    uint64_to_bignum(bigleft, left);
    mpz_sub(sum, bigleft, MPZ(right));
    mpz_clear(bigleft);
  }
  else {
    mpz_ui_sub(sum, (unsigned long)left, MPZ(right));
  }

  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* Bignum - Fixnum */
static mrb_value
big_fix_minus(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);

#if MRB_INT_MIN < LONG_MIN || LONG_MAX < MRB_INT_MAX
  if (right < LONG_MIN || LONG_MAX < right) {
    /* Use this if the Fixnum won't fit in signed long */
    mpz_t bigright;

    mpz_init(bigright);
    int64_to_bignum(bigright, right);
    mpz_sub(sum, MPZ(left), bigright);
    mpz_clear(bigright);
  }
  else
#endif
  {
    if (right >= 0) {
      mpz_sub_ui(sum, MPZ(left), +(unsigned long)right);
    }
    else {
      mpz_add_ui(sum, MPZ(left), -(unsigned long)right);
    }
  }

  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* Bignum - Bignum */
static mrb_value
big_big_minus(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);
  mpz_sub(sum, DATA_PTR(left), DATA_PTR(right));
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* 15.2.8.3.4  Integer#- */
static mrb_value
fixnum_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum - Fixnum */
    out = fix_fix_plus(mrb, fixself, mrb_fixnum(other), TRUE);
    break;
  case num_bignum:
    /* Fixnum - Bignum */
    out = fix_big_minus(mrb, fixself, other);
    break;
  case num_float:
    /* Fixnum - Float */
    out = mrb_float_value(mrb, fixself - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* 15.2.8.3.4  Integer#- */
static mrb_value
bignum_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum - Fixnum */
    out = big_fix_minus(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum - Bignum */
    out = big_big_minus(mrb, self, other);
    break;
  case num_float:
    /* Bignum - Float */
    out = mrb_float_value(mrb, mpz_get_d(MPZ(self)) - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* 15.2.9.3.4  Float#- */
static mrb_value
float_minus(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float - Fixnum */
    out = mrb_float_value(mrb, fltself - mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float - Bignum */
    out = mrb_float_value(mrb, fltself - mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Float - Float */
    out = mrb_float_value(mrb, fltself - mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "-");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "*" */
/* ------------------------------------------------------------------------*/

/* Fixnum * Fixnum */
static mrb_value
fix_fix_mul(mrb_state *mrb, mrb_int left, mrb_int right)
{
  /* Fixnums with absolute value not exceeding mul_max never overflow when
     multiplied */
#ifdef MRB_WORD_BOXING
#  if MRB_INT_BIT == 32
  static const mrb_int mul_max = 32767;
#  else
  static const mrb_int mul_max = 2147483647;
#  endif
#else
#  if MRB_INT_BIT == 16
  static const mrb_int mul_max = 181;
#  elif MRB_INT_BIT == 32
  static const mrb_int mul_max = 46340;
#  else
  static const mrb_int mul_max = 3037000499;
#  endif
#endif

  mpz_t out, left2, right2;
  mrb_value value;

  if (-mul_max <= left && left <= +mul_max
  &&  -mul_max <= right && right <= +mul_max) {
    /* Small number optimization; product will never overflow */
    return mrb_fixnum_value(left * right);
  }

  mpz_init(left2);
  mpz_init(right2);
  mpz_init(out);
  int64_to_bignum(left2, left);
  int64_to_bignum(right2, right);
  mpz_mul(out, left2, right2);
  value = new_bignum(mrb, out, TRUE);
  mpz_clear(left2);
  mpz_clear(right2);
  mpz_clear(out);
  return value;
}

/* Bignum * Fixnum */
static mrb_value
big_fix_mul(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t prod;
  mrb_value out;

  mpz_init(prod);

#if MRB_INT_MIN < LONG_MIN || LONG_MAX < MRB_INT_MAX
  if (right < LONG_MIN || LONG_MAX < right) {
    /* Use this if the Fixnum won't fit in signed long */
    mpz_t bigright;

    mpz_init(bigright);
    int64_to_bignum(bigright, right);
    mpz_mul(prod, MPZ(left), bigright);
    mpz_clear(bigright);
  }
  else
#endif
  {
    mpz_mul_si(prod, MPZ(left), right);
  }

  out = new_bignum(mrb, prod, FIXNUM_CONVERT);
  mpz_clear(prod);
  return out;
}

/* Bignum * Bignum */
static mrb_value
big_big_mul(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t prod;
  mrb_value out;

  mpz_init(prod);

  mpz_mul(prod, MPZ(left), MPZ(right));

  out = new_bignum(mrb, prod, FIXNUM_CONVERT);
  mpz_clear(prod);
  return out;
}

/* 15.2.8.3.5  Integer#* */
static mrb_value
fixnum_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum * Fixnum */
    out = fix_fix_mul(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum * Bignum */
    out = big_fix_mul(mrb, other, fixself);
    break;
  case num_float:
    /* Fixnum * Float */
    out = mrb_float_value(mrb, fixself * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* 15.2.8.3.5  Integer#* */
static mrb_value
bignum_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum * Fixnum */
    out = big_fix_mul(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum * Bignum */
    out = big_big_mul(mrb, self, other);
    break;
  case num_float:
    /* Bignum * Float */
    out = mrb_float_value(mrb, mpz_get_d(MPZ(self)) * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* 15.2.9.3.5  Float#* */
static mrb_value
float_mul(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float * Fixnum */
    out = mrb_float_value(mrb, fltself * mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float * Bignum */
    out = mrb_float_value(mrb, fltself * mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Float * Float */
    out = mrb_float_value(mrb, fltself * mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "*");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "/" */
/* ------------------------------------------------------------------------*/

/* Fixnum / Fixnum */
static mrb_value
fix_fix_div(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_int quo;

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  /* This is the only way that division of Fixnums can overflow */
  if (x == MRB_INT_MIN && y == -1) {
    mpz_t quo;
    mrb_value out;

    mpz_init_set_ui(quo, 1);
    mpz_mul_2exp(quo, quo, MRB_INT_BIT - 1);
    out = new_bignum(mrb, quo, FALSE);
    mpz_clear(quo);
    return out;
  }

  quo = x / y;
  if ((x >= 0) != (y >= 0) && x % y != 0) {
    --quo;
  }

  return mrb_fixnum_value(quo);
}

/* Fixnum / Bignum */
static mrb_value
fix_big_div(mrb_state *mrb, mrb_int self, mrb_value other)
{
  mpz_t bigself;
  mpz_t quo;
  mrb_value out;

  if (mpz_cmp_ui(MPZ(other), 0) == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(bigself);
  mpz_init(quo);
  int64_to_bignum(bigself, self);
  mpz_fdiv_q(quo, bigself, MPZ(other));
  out = new_bignum(mrb, quo, FIXNUM_CONVERT);
  mpz_clear(bigself);
  mpz_clear(quo);

  return out;
}

/* Bignum / Fixnum */
static mrb_value
big_fix_div(mrb_state *mrb, mrb_value self, mrb_int other)
{
  mpz_t bigother;
  mpz_t quo;
  mrb_value out;

  if (other == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(bigother);
  mpz_init(quo);
  int64_to_bignum(bigother, other);
  mpz_fdiv_q(quo, MPZ(self), bigother);
  out = new_bignum(mrb, quo, FIXNUM_CONVERT);
  mpz_clear(bigother);
  mpz_clear(quo);

  return out;
}

/* Bignum / Bignum */
static mrb_value
big_big_div(mrb_state *mrb, mrb_value self, mrb_value other)
{
  mpz_t quo;
  mrb_value out;

  if (mpz_cmp_ui(MPZ(other), 0) == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(quo);
  mpz_fdiv_q(quo, MPZ(self), MPZ(other));
  out = new_bignum(mrb, quo, FIXNUM_CONVERT);
  mpz_clear(quo);

  return out;
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
fixnum_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum / Fixnum */
    out = fix_fix_div(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum / Bignum */
    out = fix_big_div(mrb, fixself, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
bignum_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum / Fixnum */
    out = big_fix_div(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum / Bignum */
    out = big_big_div(mrb, self, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* 15.2.8.3.6  Integer#/ */
static mrb_value
float_div(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float / Fixnum */
    out = mrb_float_value(mrb, fltself / mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float / Bignum */
    out = mrb_float_value(mrb, fltself / mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Float / Float */
    out = mrb_float_value(mrb, fltself / mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "/");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "%" */
/* ------------------------------------------------------------------------*/

/* Fixnum % Fixnum */
static mrb_value
fix_fix_mod(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_int rem;

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  rem = x % y;
  if ((x >= 0) != (y >= 0) && rem != 0) {
    rem += y;
  }

  return mrb_fixnum_value(rem);
}

/* Fixnum % Bignum */
static mrb_value
fix_big_mod(mrb_state *mrb, mrb_int self, mrb_value other)
{
  mpz_t bigself;
  mpz_t rem;
  mrb_value out;

  if (mpz_cmp_ui(MPZ(other), 0) == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(bigself);
  mpz_init(rem);
  int64_to_bignum(bigself, self);
  mpz_fdiv_r(rem, bigself, MPZ(other));
  out = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(bigself);
  mpz_clear(rem);

  return out;
}

/* Bignum % Fixnum */
static mrb_value
big_fix_mod(mrb_state *mrb, mrb_value self, mrb_int other)
{
  mpz_t bigother;
  mpz_t rem;
  mrb_value out;

  if (other == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(bigother);
  mpz_init(rem);
  int64_to_bignum(bigother, other);
  mpz_fdiv_r(rem, MPZ(self), bigother);
  out = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(bigother);
  mpz_clear(rem);

  return out;
}

/* Bignum % Bignum */
static mrb_value
big_big_mod(mrb_state *mrb, mrb_value self, mrb_value other)
{
  mpz_t rem;
  mrb_value out;

  if (mpz_cmp_ui(MPZ(other), 0) == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  mpz_init(rem);
  mpz_fdiv_r(rem, MPZ(self), MPZ(other));
  out = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(rem);

  return out;
}

/* 15.2.8.3.7  Integer#% */
static mrb_value
fixnum_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum % Fixnum */
    out = fix_fix_mod(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum % Bignum */
    out = fix_big_mod(mrb, fixself, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* 15.2.8.3.7  Integer#% */
static mrb_value
bignum_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum % Fixnum */
    out = big_fix_mod(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum % Bignum */
    out = big_big_mod(mrb, self, other);
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* 15.2.9.3.7  Float#% */
static mrb_value
float_mod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float % Fixnum */
    out = mrb_float_value(mrb, F(fmod)(fltself, mrb_fixnum(other)));
    break;
  case num_bignum:
    /* Float % Bignum */
    out = mrb_float_value(mrb, F(fmod)(fltself, mpz_get_d(MPZ(other))));
    break;
  case num_float:
    /* Float % Float */
    out = mrb_float_value(mrb, F(fmod)(fltself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "%");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "divmod" */
/* ------------------------------------------------------------------------*/

/* Fixnum.divmod(Fixnum) */
static mrb_value
fix_fix_divmod(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mrb_value out[2];

  if (y == 0) {
    mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"), "divided by 0");
  }

  if (x == MRB_INT_MIN && y == -1) {
    /* Fixnum division overflows */
    mpz_t quo;

    mpz_init_set_ui(quo, 1);
    mpz_mul_2exp(quo, quo, MRB_INT_BIT - 1);
    out[0] = new_bignum(mrb, quo, FALSE);
    mpz_clear(quo);
    out[1] = mrb_fixnum_value(0);
  }
  else {
    mrb_int q = x / y;
    mrb_int r = x % y;
    /* Division rounds down */
    if (q < 0 && r != 0) {
      --q;
      r += y;
    }
    out[0] = mrb_fixnum_value(q);
    out[1] = mrb_fixnum_value(r);
  }

  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Float.divmod(Float) */
static mrb_value
flt_flt_divmod(mrb_state *mrb, mrb_float x, mrb_float y)
{
  mrb_float q, r;
  mrb_value out[2];

  q = F(floor)(x/y);
  r = x - q*y;

  out[0] = mrb_float_value(mrb, q);
  out[1] = mrb_float_value(mrb, r);

  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Bignum.divmod(Bignum) */
static mrb_value
big_big_divmod(mrb_state *mrb, mrb_value x, mrb_value y)
{
  mpz_t quo, rem;
  mrb_value out[2];

  mpz_init(quo);
  mpz_init(rem);
  mpz_fdiv_qr(quo, rem, MPZ(x), MPZ(y));
  out[0] = new_bignum(mrb, quo, FIXNUM_CONVERT);
  out[1] = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(quo);
  mpz_clear(rem);
  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Fixnum.divmod(Bignum) */
static mrb_value
fix_big_divmod(mrb_state *mrb, mrb_int x, mrb_value y)
{
  mpz_t bigx, quo, rem;
  mrb_value out[2];

  mpz_init(bigx);
  mpz_init(quo);
  mpz_init(rem);
  int64_to_bignum(bigx, x);
  mpz_fdiv_qr(quo, rem, bigx, MPZ(y));
  out[0] = new_bignum(mrb, quo, FIXNUM_CONVERT);
  out[1] = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(bigx);
  mpz_clear(quo);
  mpz_clear(rem);
  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Bignum.divmod(Fixnum) */
static mrb_value
big_fix_divmod(mrb_state *mrb, mrb_value x, mrb_int y)
{
  mpz_t bigy, quo, rem;
  mrb_value out[2];

  mpz_init(bigy);
  mpz_init(quo);
  mpz_init(rem);
  int64_to_bignum(bigy, y);
  mpz_fdiv_qr(quo, rem, MPZ(x), bigy);
  out[0] = new_bignum(mrb, quo, FIXNUM_CONVERT);
  out[1] = new_bignum(mrb, rem, FIXNUM_CONVERT);
  mpz_clear(bigy);
  mpz_clear(quo);
  mpz_clear(rem);
  return mrb_ary_new_from_values(mrb, 2, out);
}

/* Fixnum#divmod */
static mrb_value
fixnum_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.divmod(Fixnum) */
    out = fix_fix_divmod(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum.divmod(Bignum) */
    out = fix_big_divmod(mrb, fixself, other);
    break;
  case num_float:
    /* Fixnum.divmod(Float) */
    out = flt_flt_divmod(mrb, fixself, mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* Bignum#divmod */
static mrb_value
bignum_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.divmod(Fixnum) */
    out = big_fix_divmod(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum.divmod(Bignum) */
    out = big_big_divmod(mrb, self, other);
    break;
  case num_float:
    /* Bignum.divmod(Float) */
    out = flt_flt_divmod(mrb, mpz_get_d(MPZ(self)), mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* Float#divmod */
static mrb_value
float_divmod(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_float fltself = mrb_float(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float.divmod(Fixnum) */
    out = flt_flt_divmod(mrb, fltself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Float.divmod(Bignum) */
    out = flt_flt_divmod(mrb, fltself, mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Float.divmod(Float) */
    out = flt_flt_divmod(mrb, fltself, mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "divmod");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "quo" */
/* ------------------------------------------------------------------------*/

/* The CRuby documentation describes quo as returning the "most exact division
   (rational for integers, float for floats).  Because this gem does not
   implement rationals, quo always returns a float. */

static mrb_value
quo(mrb_state *mrb, mrb_value self, mrb_float fltself)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Numeric.quo(Fixnum) */
    out = mrb_float_value(mrb, fltself / mrb_fixnum(other));
    break;
  case num_bignum:
    /* Numeric.quo(Bignum) */
    out = mrb_float_value(mrb, fltself / mpz_get_d(MPZ(other)));
    break;
  case num_float:
    /* Numeric.quo(Float) */
    out = mrb_float_value(mrb, fltself / mrb_float(other));
    break;
  default:
    out = op_coerce(mrb, self, other, "quo");
    break;
  }

  return out;
}

/* Fixnum#quo */
static mrb_value
fixnum_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, mrb_fixnum(self));
}

/* Bignum#quo */
static mrb_value
bignum_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, mpz_get_d(MPZ(self)));
}

/* Float#quo */
static mrb_value
float_quo(mrb_state *mrb, mrb_value self)
{
  return quo(mrb, self, mrb_float(self));
}

/* ------------------------------------------------------------------------*/
/* "**" */
/* ------------------------------------------------------------------------*/

static mrb_value
big_fix_pow(mrb_state *mrb, mrb_value x, int64_t y, mrb_bool fixnum_conv)
{
  mpz_t z;
  mrb_value out;

  if (y == 0) {
    return mrb_fixnum_value(1);
  }
  if (mpz_fits_slong_p(MPZ(x))) {
    long xl = mpz_get_si(MPZ(x));

    switch (xl) {
    case +1:
      return mrb_fixnum_value(1);

    case -1:
      return mrb_fixnum_value(((y & 1) != 0) ? -1 : +1);

    case 0:
      if (y > 0) {
        return mrb_fixnum_value(0);
      }
      else {
        mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"),
                "negative power of zero");
        return mrb_nil_value();
      }
    }
  }

  if (y < 0) {
    return mrb_float_value(mrb, F(pow)(mpz_get_d(MPZ(x)), y));
  }

  if (y > ULONG_MAX) {
    mrb_raise(mrb, E_RANGE_ERROR, "exponent too big");
  }

  mpz_init(z);
  mpz_pow_ui(z, MPZ(x), y);
  out = new_bignum(mrb, z, fixnum_conv);
  mpz_clear(z);
  return out;
}

static mrb_value
fix_fix_pow(mrb_state *mrb, mrb_int x, mrb_int y)
{
  mpz_t bigx, z;
  mrb_value out;

  if (x == 1 || y == 0) {
    return mrb_fixnum_value(1);
  }
  if (x == 0) {
    if (y > 0) {
      return mrb_fixnum_value(0);
    }
    else {
      mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"),
              "negative power of zero");
      return mrb_nil_value();
    }
  }
  if (x == -1) {
    return mrb_fixnum_value((y & 1) ? -1 : +1);
  }

  if (y < 0) {
    return mrb_float_value(mrb, F(pow)(x, y));
  }

  if (y > ULONG_MAX) {
    mrb_raise(mrb, E_RANGE_ERROR, "exponent too big");
  }

  mpz_init(bigx);
  mpz_init(z);
  int64_to_bignum(bigx, x);
  mpz_pow_ui(z, bigx, y);
  out = new_bignum(mrb, z, TRUE);
  mpz_clear(bigx);
  mpz_clear(z);
  return out;
}

static mrb_value
big_big_pow(mrb_state *mrb, mrb_value x, mrb_value y, mrb_bool fixnum_conv)
{
  int ysign;
  mpz_t z;
  mrb_value out;

  ysign = mpz_cmp_si(MPZ(y), 0);
  if (ysign == 0) {
    return mrb_fixnum_value(1);
  }
  if (mpz_fits_slong_p(MPZ(x))) {
    long xl = mpz_get_si(MPZ(x));

    switch (xl) {
    case +1:
      return mrb_fixnum_value(1);

    case -1:
      return mrb_fixnum_value(mpz_tstbit(MPZ(y), 0) ? -1 : +1);

    case 0:
      if (ysign > 0) {
        return mrb_fixnum_value(0);
      }
      else {
        mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"),
                "negative power of zero");
        return mrb_nil_value();
      }
    }
  }

  if (ysign < 0) {
    out = mrb_float_value(mrb, F(pow)(mpz_get_d(MPZ(x)), mpz_get_d(MPZ(y))));
  }
  else {
    int64_t fixy = bignum_to_int64(MPZ(y));
    if (fixy == INT64_MIN || fixy > ULONG_MAX) {
      mrb_raise(mrb, E_RANGE_ERROR, "exponent too big");
    }
    mpz_init(z);
    mpz_pow_ui(z, MPZ(x), fixy);
    out = new_bignum(mrb, z, fixnum_conv);
    mpz_clear(z);
  }
  return out;
}

static mrb_value
fix_big_pow(mrb_state *mrb, mrb_int x, mrb_value y)
{
  int ysign;
  mpz_t bigx, z;
  mrb_value out;

  ysign = mpz_cmp_si(MPZ(y), 0);
  if (x == 1 || ysign == 0) {
    return mrb_fixnum_value(1);
  }
  if (x == 0) {
    if (ysign > 0) {
      return mrb_fixnum_value(0);
    }
    else {
      mrb_raise(mrb, mrb_class_get(mrb, "ZeroDivisionError"),
              "negative power of zero");
      return mrb_nil_value();
    }
  }
  if (x == -1) {
    return mrb_fixnum_value(mpz_tstbit(MPZ(y), 0) ? -1 : +1);
  }

  if (ysign < 0) {
    out = mrb_float_value(mrb, F(pow)(x, mpz_get_d(MPZ(y))));
  }
  else {
    int64_t fixy = bignum_to_int64(MPZ(y));
    if (fixy == INT64_MIN || fixy > ULONG_MAX) {
      mrb_raise(mrb, E_RANGE_ERROR, "exponent too big");
    }
    mpz_init(bigx);
    mpz_init(z);
    int64_to_bignum(bigx, x);
    mpz_pow_ui(z, bigx, fixy);
    out = new_bignum(mrb, z, TRUE);
    mpz_init(bigx);
    mpz_clear(z);
  }
  return out;
}

/* Fixnum#** */
static mrb_value
fixnum_pow(mrb_state *mrb, mrb_value self)
{
  mrb_int fixself = mrb_fixnum(self);
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum ** Fixnum */
    out = fix_fix_pow(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum ** Bignum */
    out = fix_big_pow(mrb, fixself, other);
    break;
  case num_float:
    /* Fixnum ** Float */
    out = mrb_float_value(mrb, F(pow)(fixself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* Bignum#** */
static mrb_value
bignum_pow(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum ** Fixnum */
    out = big_fix_pow(mrb, self, mrb_fixnum(other), FIXNUM_CONVERT);
    break;
  case num_bignum:
    /* Bignum ** Bignum */
    out = big_big_pow(mrb, self, other, FIXNUM_CONVERT);
    break;
  case num_float:
    /* Bignum ** Float */
    out = mrb_float_value(mrb, F(pow)(mpz_get_d(MPZ(self)), mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* Float#** */
static mrb_value
float_pow(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Float ** Fixnum */
    out = mrb_float_value(mrb, F(pow)(fltself, mrb_fixnum(other)));
    break;
  case num_bignum:
    /* Float ** Bignum */
    out = mrb_float_value(mrb, F(pow)(fltself, mpz_get_d(MPZ(other))));
    break;
  case num_float:
    /* Float ** Float */
    out = mrb_float_value(mrb, F(pow)(fltself, mrb_float(other)));
    break;
  default:
    out = op_coerce(mrb, self, other, "**");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "~" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.8  Integer#~ */
static mrb_value
bignum_rev(mrb_state *mrb, mrb_value self)
{
  mpz_t rev;
  mrb_value out;

  mpz_init(rev);
  mpz_com(rev, MPZ(self));
  out = new_bignum(mrb, rev, FIXNUM_CONVERT);
  mpz_clear(rev);
  return out;
}

/* ------------------------------------------------------------------------*/
/* "&" */
/* ------------------------------------------------------------------------*/

static mrb_value
bitwise_coerce(mrb_state *mrb, mrb_value x, mrb_value y, char const *op)
{
  if (mrb_respond_to(mrb, y, mrb_intern_lit(mrb, "coerce"))) {
    mrb_value v;
    v = mrb_funcall(mrb, y, "coerce", 1, x);
    if (mrb_array_p(v) && RARRAY_LEN(v) >= 2) {
      mrb_value f = mrb_ary_entry(v, 0);
      mrb_value s = mrb_ary_entry(v, 1);
      struct RClass *integer = mrb_class_get(mrb, "Integer");
      if (mrb_obj_is_kind_of(mrb, f, integer)
      &&  mrb_obj_is_kind_of(mrb, s, integer)) {
        return mrb_funcall(mrb, f, op, 1, s);
      }
    }
  }

  mrb_raise(mrb, E_TYPE_ERROR, "bitwise arithmetic requires Integer");
  return mrb_nil_value();
}

/* Bignum & Fixnum */
static mrb_value
big_fix_and(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t sum;
  mpz_t bigright;
  mrb_value out;

  mpz_init(sum);
  mpz_init(bigright);
  int64_to_bignum(bigright, right);
  mpz_and(sum, MPZ(left), bigright);
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  mpz_clear(bigright);
  return out;
}

/* Bignum & Bignum */
static mrb_value
big_big_and(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);
  mpz_and(sum, MPZ(left), MPZ(right));
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* 15.2.8.3.9  Integer#& */
static mrb_value
fixnum_and(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum & Fixnum */
    out = mrb_fixnum_value(fixself & mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum & Bignum */
    out = big_fix_and(mrb, other, fixself);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "&");
    break;
  }

  return out;
}

/* 15.2.8.3.9  Integer#& */
static mrb_value
bignum_and(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum & Fixnum */
    out = big_fix_and(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum & Bignum */
    out = big_big_and(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "&");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "|" */
/* ------------------------------------------------------------------------*/

/* Bignum | Fixnum */
static mrb_value
big_fix_or(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t sum;
  mpz_t bigright;
  mrb_value out;

  mpz_init(sum);
  mpz_init(bigright);
  int64_to_bignum(bigright, right);
  mpz_ior(sum, MPZ(left), bigright);
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  mpz_clear(bigright);
  return out;
}

/* Bignum | Bignum */
static mrb_value
big_big_or(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);
  mpz_ior(sum, MPZ(left), MPZ(right));
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* 15.2.8.3.9  Integer#| */
static mrb_value
fixnum_or(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum | Fixnum */
    out = mrb_fixnum_value(fixself | mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum | Bignum */
    out = big_fix_or(mrb, other, fixself);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "|");
    break;
  }

  return out;
}

/* 15.2.8.3.9  Integer#| */
static mrb_value
bignum_or(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum | Fixnum */
    out = big_fix_or(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum | Bignum */
    out = big_big_or(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "|");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "^" */
/* ------------------------------------------------------------------------*/

/* Bignum ^ Fixnum */
static mrb_value
big_fix_xor(mrb_state *mrb, mrb_value left, mrb_int right)
{
  mpz_t sum;
  mpz_t bigright;
  mrb_value out;

  mpz_init(sum);
  mpz_init(bigright);
  int64_to_bignum(bigright, right);
  mpz_xor(sum, MPZ(left), bigright);
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  mpz_clear(bigright);
  return out;
}

/* Bignum ^ Bignum */
static mrb_value
big_big_xor(mrb_state *mrb, mrb_value left, mrb_value right)
{
  mpz_t sum;
  mrb_value out;

  mpz_init(sum);
  mpz_xor(sum, MPZ(left), MPZ(right));
  out = new_bignum(mrb, sum, FIXNUM_CONVERT);
  mpz_clear(sum);
  return out;
}

/* 15.2.8.3.9  Integer#^ */
static mrb_value
fixnum_xor(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum ^ Fixnum */
    out = mrb_fixnum_value(fixself ^ mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum ^ Bignum */
    out = big_fix_xor(mrb, other, fixself);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "^");
    break;
  }

  return out;
}

/* 15.2.8.3.9  Integer#^ */
static mrb_value
bignum_xor(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum ^ Fixnum */
    out = big_fix_xor(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum ^ Bignum */
    out = big_big_xor(mrb, self, other);
    break;
  default:
    out = bitwise_coerce(mrb, self, other, "^");
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "<<" */
/* ------------------------------------------------------------------------*/

static mrb_value
fix_fix_lshift_u(mrb_state *mrb, mrb_int self, uint64_t other)
{
  mpz_t bigself;
  mpz_t result;
  mrb_value out;

  /* The GMP shift function accepts an unsigned long */
  /* TODO:  how does GMP signal too big a shift? */
#if ULONG_MAX < UINT64_MAX
  if (other > ULONG_MAX) {
    mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
  }
#endif

  mpz_init(bigself);
  mpz_init(result);
  int64_to_bignum(bigself, self);
  mpz_mul_2exp(result, bigself, (unsigned long)other);
  out = new_bignum(mrb, result, FIXNUM_CONVERT);
  mpz_clear(bigself);
  mpz_clear(result);
  return out;
}

static mrb_value
fix_fix_rshift_u(mrb_state *mrb, mrb_int self, uint64_t other)
{
  /* Avoid undefined behavior */
  if (other >= MRB_INT_BIT) {
    return mrb_fixnum_value((self < 0) ? -1 : 0);
  }

  /* C does not specify whether signs are kept when a negative number is
     shifted right, so shift positive numbers only; also round division
     downward */
  if (self >= 0) {
    return mrb_fixnum_value(self >> other);
  }
  else {
    mrb_uint u1, u2;
    /* Compute as -(-self >> other) */
    u1 = -(mrb_uint)self;
    u2 = u1 >> other;
    if ((u2 << other) != u1) {
      ++u2;
    }
    return mrb_fixnum_value((mrb_int)-u2);
  }
}

static mrb_value
big_fix_lshift_u(mrb_state *mrb, mrb_value self, uint64_t other)
{
  mpz_t result;
  mrb_value out;

  /* The GMP shift function accepts an unsigned long */
  /* TODO:  how does GMP signal too big a shift? */
#if ULONG_MAX < UINT64_MAX
  if (other > ULONG_MAX) {
    mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
  }
#endif

  mpz_init(result);
  mpz_mul_2exp(result, MPZ(self), (unsigned long)other);
  out = new_bignum(mrb, result, FIXNUM_CONVERT);
  mpz_clear(result);
  return out;
}

/* Result of right shift that is deemed too large */
static mrb_value
big_rshift_large(mrb_state *mrb, mrb_value self)
{
  int result = (mpz_cmp_si(MPZ(self), 0) < 0) ? -1 : 0;
#if FIXNUM_CONVERT
  return mrb_fixnum_value(result);
#else
  mpz_t bigresult;
  mrb_value out;

  mpz_init_set_si(bigresult, result);
  out = new_bignum(mrb, bigresult, FALSE);
  mpz_clear(bigresult);
  return out;
#endif
}

static mrb_value
big_fix_rshift_u(mrb_state *mrb, mrb_value self, uint64_t other)
{
  mpz_t result;
  mrb_value out;

  /* The GMP shift function accepts an unsigned long */
  /* TODO:  how does GMP signal too big a shift? */
#if ULONG_MAX < UINT64_MAX
  if (other > ULONG_MAX) {
    return big_rshift_large(mrb, self);
  }
#endif

  mpz_init(result);
  mpz_fdiv_q_2exp(result, MPZ(self), (unsigned long)other);
  out = new_bignum(mrb, result, FIXNUM_CONVERT);
  mpz_clear(result);
  return out;
}

/* Fixnum << Fixnum */
static mrb_value
fix_fix_lshift(mrb_state *mrb, mrb_int self, int64_t other)
{
  if (other < 0) {
    return fix_fix_rshift_u(mrb, self, -(uint64_t)other);
  }
  else {
    return fix_fix_lshift_u(mrb, self, +(uint64_t)other);
  }
}

/* Bignum << Fixnum */
static mrb_value
big_fix_lshift(mrb_state *mrb, mrb_value self, int64_t other)
{
  if (other < 0) {
    return big_fix_rshift_u(mrb, self, -(uint64_t)other);
  }
  else {
    return big_fix_lshift_u(mrb, self, +(uint64_t)other);
  }
}

/* 15.2.8.3.12 Integer#<< */
static mrb_value
fixnum_lshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum << Fixnum */
    out = fix_fix_lshift(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum << Bignum */
    {
      int64_t fixother = bignum_to_int64(MPZ(other));
      if (fixother == INT64_MIN) {
        if (mpz_cmp_si(MPZ(other), 0) < 0) {
          out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = fix_fix_lshift(mrb, fixself, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum << Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother < INT64_MIN) {
        out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
      }
      else if (fltother > INT64_MAX) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = fix_fix_lshift(mrb, fixself, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* 15.2.8.3.12 Integer#<< */
static mrb_value
bignum_lshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum << Fixnum */
    out = big_fix_lshift(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum << Bignum */
    {
      int64_t fixother = bignum_to_int64(MPZ(other));
      if (fixother == INT64_MIN) {
        if (mpz_cmp_si(MPZ(other), 0) < 0) {
          out = big_rshift_large(mrb, self);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = big_fix_lshift(mrb, self, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum << Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother < INT64_MIN) {
        out = big_rshift_large(mrb, self);
      }
      else if (fltother > INT64_MAX) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = big_fix_lshift(mrb, self, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* ">>" */
/* ------------------------------------------------------------------------*/

/* Fixnum >> Fixnum */
static mrb_value
fix_fix_rshift(mrb_state *mrb, mrb_int self, int64_t other)
{
  if (other < 0) {
    return fix_fix_lshift_u(mrb, self, -(uint64_t)other);
  }
  else {
    return fix_fix_rshift_u(mrb, self, +(uint64_t)other);
  }
}

/* Bignum >> Fixnum */
static mrb_value
big_fix_rshift(mrb_state *mrb, mrb_value self, int64_t other)
{
  if (other < 0) {
    return big_fix_lshift_u(mrb, self, -(uint64_t)other);
  }
  else {
    return big_fix_rshift_u(mrb, self, +(uint64_t)other);
  }
}

/* 15.2.8.3.13 Integer#>> */
static mrb_value
fixnum_rshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_int fixself = mrb_fixnum(self);
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum >> Fixnum */
    out = fix_fix_rshift(mrb, fixself, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Fixnum >> Bignum */
    {
      int64_t fixother = bignum_to_int64(MPZ(other));
      if (fixother == INT64_MIN) {
        if (mpz_cmp_si(MPZ(other), 0) >= 0) {
          out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = fix_fix_rshift(mrb, fixself, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum >> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother > INT64_MAX) {
        out = mrb_fixnum_value(fixself < 0 ? -1 : 0);
      }
      else if (fltother < INT64_MIN) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = fix_fix_rshift(mrb, fixself, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* 15.2.8.3.13 Integer#>> */
static mrb_value
bignum_rshift(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value out;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum >> Fixnum */
    out = big_fix_rshift(mrb, self, mrb_fixnum(other));
    break;
  case num_bignum:
    /* Bignum >> Bignum */
    {
      int64_t fixother = bignum_to_int64(MPZ(other));
      if (fixother == INT64_MIN) {
        if (mpz_cmp_si(MPZ(other), 0) >= 0) {
          out = big_rshift_large(mrb, self);
        }
        else {
          mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
          out = mrb_nil_value();
        }
      }
      else {
        out = big_fix_rshift(mrb, self, fixother);
      }
    }
    break;
  case num_float:
    /* Fixnum >> Float */
    {
      mrb_float fltother = mrb_float(other);
      if (fltother > INT64_MAX) {
        out = big_rshift_large(mrb, self);
      }
      else if (fltother < INT64_MIN) {
        mrb_raise(mrb, E_RANGE_ERROR, "shift width too big");
        out = mrb_nil_value();
      }
      else {
        out = big_fix_rshift(mrb, self, fltother);
      }
    }
    break;
  default:
    mrb_raise(mrb, E_TYPE_ERROR, "expected Integer");
    out = mrb_nil_value();
    break;
  }

  return out;
}

/* ------------------------------------------------------------------------*/
/* "eql?" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.16 Integer#eql? */
static mrb_value
fixnum_eql(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eql;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.eql?(Fixnum) */
    eql = mrb_fixnum(self) == mrb_fixnum(other);
    break;
  case num_bignum:
    /* Fixnum.eql?(Bignum) */
    eql = big_fix_cmp(mrb, other, mrb_fixnum(self)) == 0;
    break;
  default:
    eql = FALSE;
    break;
  }

  return mrb_bool_value(eql);
}

/* 15.2.8.3.16 Integer#eql? */
static mrb_value
bignum_eql(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_bool eql;

  mrb_get_args(mrb, "o", &other);

  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.eql?(Fixnum) */
    eql = big_fix_cmp(mrb, self, mrb_fixnum(other)) == 0;
    break;
  case num_bignum:
    /* Bignum.eql?(Bignum) */
    eql = mpz_cmp(MPZ(self), MPZ(other)) == 0;
    break;
  default:
    eql = FALSE;
    break;
  }

  return mrb_bool_value(eql);
}

/* ------------------------------------------------------------------------*/
/* "hash" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.18 Integer#hash */
static mrb_value
bignum_hash(mrb_state *mrb, mrb_value self)
{
  size_t count;
  uint32_t *digits = mpz_export(NULL, &count, -1, sizeof(uint32_t), 0, 0, MPZ(self));
  mrb_uint key = 0;
  size_t i, j;

  for (i = 0; i < count; ++i) {
    uint32_t digit = digits[i];
    for (j = 0; j < sizeof(uint32_t); ++j) {
      key = key*65599 + (digit & 0xFF);
      digit >>= 8;
    }
  }

  /* TODO:  set the allocation functions */
  free(digits);
  return mrb_fixnum_value((mrb_int)(key + (key >> 5)));
}

/* ------------------------------------------------------------------------*/
/* "to_f" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.23 Integer#to_f */
static mrb_value
bignum_to_f(mrb_state *mrb, mrb_value self)
{
  return mrb_float_value(mrb, mpz_get_d(MPZ(self)));
}

/* ------------------------------------------------------------------------*/
/* "to_s" */
/* ------------------------------------------------------------------------*/

/* 15.2.8.3.25 Integer#to_s */
static mrb_value
bignum_to_s(mrb_state *mrb, mrb_value self)
{
  mrb_int base = 10;
  char *str;
  mrb_value rstr;

  mrb_get_args(mrb, "|i", &base);

  if (!((-36 <= base && base <= -2) || (+2 <= base && base <= +62))) {
    mrb_raisef(mrb, E_ARGUMENT_ERROR, "invalid radix %S", mrb_fixnum_value(base));
  }

  str = mpz_get_str(NULL, base, MPZ(self));
  rstr = mrb_str_new_cstr(mrb, str);
  /* TODO:  set the allocation functions */
  free(str);
  return rstr;
}

/* ------------------------------------------------------------------------*/
/* Float to Integer conversions */
/* ------------------------------------------------------------------------*/

/* 15.2.9.3.8 Float#ceil */
static mrb_value
float_ceil(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  mpz_t num;
  mrb_value out;

  if (isnan(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, "NaN");
  }
  if (isinf(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, fltself < 0 ? "-Infinity" : "Infinity");
  }

  mpz_init_set_d(num, F(ceil)(mrb_float(self)));
  out = new_bignum(mrb, num, FIXNUM_CONVERT);
  mpz_clear(num);
  return out;
}

/* 15.2.9.3.10 Float#floor */
static mrb_value
float_floor(mrb_state *mrb, mrb_value self)
{
  mrb_float fltself = mrb_float(self);
  mpz_t num;
  mrb_value out;

  if (isnan(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, "NaN");
  }
  if (isinf(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, fltself < 0 ? "-Infinity" : "Infinity");
  }

  mpz_init_set_d(num, F(floor)(mrb_float(self)));
  out = new_bignum(mrb, num, FIXNUM_CONVERT);
  mpz_clear(num);
  return out;
}

/* Convert a Float to Bignum or Fixnum */
static mrb_value
float_to_int(mrb_state *mrb, mrb_value self, mrb_bool fixnum_conv)
{
  mrb_float fltself = mrb_float(self);
  mpz_t num;
  mrb_value out;

  if (isnan(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, "NaN");
  }
  if (isinf(fltself)) {
    mrb_raise(mrb, E_FLOATDOMAIN_ERROR, fltself < 0 ? "-Infinity" : "Infinity");
  }

  F(modf)(fltself, &fltself);
  mpz_init_set_d(num, fltself);
  out = new_bignum(mrb, num, FIXNUM_CONVERT);
  mpz_clear(num);
  return out;
}

/* 15.2.9.3.15 Float#to_i */
/* 15.2.9.3.16 Float#truncate */
static mrb_value
float_to_i(mrb_state *mrb, mrb_value self)
{
  return float_to_int(mrb, self, FIXNUM_CONVERT);
}

/* ------------------------------------------------------------------------*/
/* String to Integer conversion */
/* ------------------------------------------------------------------------*/

static mrb_value
string_to_int(mrb_state *mrb, mrb_value self, mrb_bool fixnum_conv)
{
  mrb_int base = 10;
  char *str, *p, *q, *end;
  size_t str_len;
  mpz_t num;
  mrb_value out;

  mrb_get_args(mrb, "|i", &base);

  if (base < 0 || 62 < base || base == 1) {
    mrb_raisef(mrb, E_ARGUMENT_ERROR, "invalid radix %S", mrb_fixnum_value(base));
  }

  /* Process prefixes and underscores */
  str_len = RSTRING_LEN(self);
  str = mrb_malloc(mrb, str_len + 1);
  p = RSTRING_PTR(self);
  q = str;
  end = p + str_len;
  /* Skip initial whitespace */
  for (; p < end && isspace(*p); ++p) {}
  /* Include or skip the sign */
  if (p < end && (*p == '+' || *p == '-')) {
    if (*p == '-') {
      *(q++) = '-';
    }
    ++p;
  }
  /* Process any prefix */
  if (p+1 < end && *p == '0') {
    switch (p[1]) {
    case 'b':  case 'B':
      base = 2;
      p += 2;
      break;

    case 'o':  case 'O':
      base = 8;
      p += 2;
      break;

    case 'd':  case 'D':
      base = 10;
      p += 2;
      break;

    case 'x':  case 'X':
      base = 16;
      p += 2;
      break;
    }
  }
  else if (p < end && *p == '0' && base == 0) {
    base = 8;
  }
  if (base == 0) {
    base = 10;
  }
  /* Include digits; exclude underscores */
  for (; p < end; ++p) {
    if (*p != '_') {
      *(q++) = *p;
    }
  }
  *q = '\0';

  mpz_init_set_str(num, str, base);
  mrb_free(mrb, str);
  out = new_bignum(mrb, num, fixnum_conv);
  mpz_clear(num);
  return out;
}

/* 15.2.10.5.38 String#to_i */
static mrb_value
string_to_i(mrb_state *mrb, mrb_value self)
{
  return string_to_int(mrb, self, FIXNUM_CONVERT);
}

/* ------------------------------------------------------------------------*/
/* "to_bn" */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_to_big(mrb_state *mrb, mrb_value self)
{
  mpz_t num;
  mrb_value out;

  mpz_init(num);
  int64_to_bignum(num, mrb_fixnum(self));
  out = new_bignum(mrb, num, FALSE);
  mpz_clear(num);
  return out;
}

static mrb_value
bignum_to_big(mrb_state *mrb, mrb_value self)
{
  return self;
}

static mrb_value
float_to_big(mrb_state *mrb, mrb_value self)
{
  return float_to_int(mrb, self, FALSE);
}

static mrb_value
string_to_big(mrb_state *mrb, mrb_value self)
{
  return string_to_int(mrb, self, FALSE);
}

/* ------------------------------------------------------------------------*/
/* Conversion to Fixnum if small enough */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_to_fix(mrb_state *mrb, mrb_value self)
{
  return self;
}

static mrb_value
bignum_to_fix(mrb_state *mrb, mrb_value self)
{
  /* Can we return a Fixnum? */
  mrb_value fix = bignum_to_fixnum(MPZ(self));
  return mrb_fixnum_p(fix) ? fix : self;
}

/* ------------------------------------------------------------------------*/
/* Coerce (15.2.7.4.4) */
/* ------------------------------------------------------------------------*/

static mrb_value
fixnum_coerce(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value pair;

  mrb_get_args(mrb, "o", &other);

  pair = mrb_ary_new_capa(mrb, 2);
  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Fixnum.coerce(Fixnum) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, self);
    break;
  case num_bignum:
    /* Fixnum.coerce(Bignum) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, fixnum_to_big(mrb, self));
    break;
  case num_float:
    /* Fixnum.coerce(Float) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, mrb_fixnum(self)));
    break;
  default:
    {
      mrb_value fltother;

      if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "to_f"))) {
        goto coerce_fail;
      }
      fltother = mrb_funcall(mrb, other, "to_f", 0);
      if (!mrb_float_p(fltother)) {
        goto coerce_fail;
      }
      mrb_ary_set(mrb, pair, 0, fltother);
      mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, mrb_fixnum(self)));
    }
    break;
  }

  return pair;

coerce_fail:
  mrb_raise(mrb, E_TYPE_ERROR, "cannot convert to float");
  return mrb_nil_value();
}

static mrb_value
bignum_coerce(mrb_state *mrb, mrb_value self)
{
  mrb_value other;
  mrb_value pair;

  mrb_get_args(mrb, "o", &other);

  pair = mrb_ary_new_capa(mrb, 2);
  switch (num_identify(mrb, other)) {
  case num_fixnum:
    /* Bignum.coerce(Fixnum) */
    mrb_ary_set(mrb, pair, 0, fixnum_to_big(mrb, other));
    mrb_ary_set(mrb, pair, 1, self);
    break;
  case num_bignum:
    /* Bignum.coerce(Bignum) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, self);
    break;
  case num_float:
    /* Bignum.coerce(Float) */
    mrb_ary_set(mrb, pair, 0, other);
    mrb_ary_set(mrb, pair, 1, bignum_to_f(mrb, self));
    break;
  default:
    {
      mrb_float fltself = mpz_get_d(MPZ(self));
      mrb_value fltother;

      if (!mrb_respond_to(mrb, other, mrb_intern_lit(mrb, "to_f"))) {
        goto coerce_fail;
      }
      fltother = mrb_funcall(mrb, other, "to_f", 0);
      if (!mrb_float_p(fltother)) {
        goto coerce_fail;
      }
      mrb_ary_set(mrb, pair, 0, fltother);
      mrb_ary_set(mrb, pair, 1, mrb_float_value(mrb, fltself));
    }
    break;
  }

  return pair;

coerce_fail:
  mrb_raise(mrb, E_TYPE_ERROR, "cannot convert to float");
  return mrb_nil_value();
}

/* ------------------------------------------------------------------------*/
void
mrb_mruby_gmp_bignum_gem_init(mrb_state *mrb)
{
  struct RClass *integer = mrb_class_get(mrb, "Integer");
  struct RClass *fixnum  = mrb->fixnum_class;
  struct RClass *rfloat  = mrb->float_class;
  struct RClass *string  = mrb->string_class;

  struct RClass *bignum = mrb_define_class(mrb, "Bignum", integer);
  MRB_SET_INSTANCE_TT(bignum, MRB_TT_DATA);

  /* Redefined Fixnum methods */
  mrb_define_method(mrb, fixnum, "<=>",      fixnum_cmp,    MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, fixnum, "<",        fixnum_lt,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "<=",       fixnum_le,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, ">",        fixnum_gt,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, ">=",       fixnum_ge,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "==",       fixnum_eq,     MRB_ARGS_REQ(1)); /* 15.2.8.3.7  */
  mrb_define_method(mrb, fixnum, "+",        fixnum_plus,   MRB_ARGS_REQ(1)); /* 15.2.8.3.1  */
  mrb_define_method(mrb, fixnum, "-",        fixnum_minus,  MRB_ARGS_REQ(1)); /* 15.2.8.3.2  */
  mrb_define_method(mrb, fixnum, "*",        fixnum_mul,    MRB_ARGS_REQ(1)); /* 15.2.8.3.3  */
  mrb_define_method(mrb, fixnum, "/",        fixnum_div,    MRB_ARGS_REQ(1)); /* 15.2.8.3.4  */
  mrb_define_method(mrb, fixnum, "%",        fixnum_mod,    MRB_ARGS_REQ(1)); /* 15.2.8.3.5  */
  mrb_define_method(mrb, fixnum, "&",        fixnum_and,    MRB_ARGS_REQ(1)); /* 15.2.8.3.9  */
  mrb_define_method(mrb, fixnum, "|",        fixnum_or,     MRB_ARGS_REQ(1)); /* 15.2.8.3.10 */
  mrb_define_method(mrb, fixnum, "^",        fixnum_xor,    MRB_ARGS_REQ(1)); /* 15.2.8.3.11 */
  mrb_define_method(mrb, fixnum, "<<",       fixnum_lshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.12 */
  mrb_define_method(mrb, fixnum, ">>",       fixnum_rshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.13 */
  mrb_define_method(mrb, fixnum, "eql?",     fixnum_eql,    MRB_ARGS_REQ(1)); /* 15.2.8.3.16 */
  mrb_define_method(mrb, fixnum, "to_bn",    fixnum_to_big, MRB_ARGS_NONE());
  mrb_define_method(mrb, fixnum, "to_fix",   fixnum_to_fix, MRB_ARGS_NONE());
  mrb_define_method(mrb, fixnum, "divmod",   fixnum_divmod, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "quo",      fixnum_quo,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "**",       fixnum_pow,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, fixnum, "coerce",   fixnum_coerce, MRB_ARGS_REQ(1)); /* 15.2.7.4.4 */

  /* Bignum methods */
  mrb_define_method(mrb, bignum, "<=>",      bignum_cmp,    MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, bignum, "<",        bignum_lt,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "<=",       bignum_le,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, ">",        bignum_gt,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, ">=",       bignum_ge,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "==",       bignum_eq,     MRB_ARGS_REQ(1)); /* 15.2.8.3.7  */
  mrb_define_method(mrb, bignum, "+",        bignum_plus,   MRB_ARGS_REQ(1)); /* 15.2.8.3.1  */
  mrb_define_method(mrb, bignum, "-",        bignum_minus,  MRB_ARGS_REQ(1)); /* 15.2.8.3.2  */
  mrb_define_method(mrb, bignum, "*",        bignum_mul,    MRB_ARGS_REQ(1)); /* 15.2.8.3.3  */
  mrb_define_method(mrb, bignum, "/",        bignum_div,    MRB_ARGS_REQ(1)); /* 15.2.8.3.4  */
  mrb_define_method(mrb, bignum, "%",        bignum_mod,    MRB_ARGS_REQ(1)); /* 15.2.8.3.5  */
  mrb_define_method(mrb, bignum, "~",        bignum_rev,    MRB_ARGS_NONE()); /* 15.2.8.3.8  */
  mrb_define_method(mrb, bignum, "&",        bignum_and,    MRB_ARGS_REQ(1)); /* 15.2.8.3.9  */
  mrb_define_method(mrb, bignum, "|",        bignum_or,     MRB_ARGS_REQ(1)); /* 15.2.8.3.10 */
  mrb_define_method(mrb, bignum, "^",        bignum_xor,    MRB_ARGS_REQ(1)); /* 15.2.8.3.11 */
  mrb_define_method(mrb, bignum, "<<",       bignum_lshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.12 */
  mrb_define_method(mrb, bignum, ">>",       bignum_rshift, MRB_ARGS_REQ(1)); /* 15.2.8.3.13 */
  mrb_define_method(mrb, bignum, "eql?",     bignum_eql,    MRB_ARGS_REQ(1)); /* 15.2.8.3.16 */
  mrb_define_method(mrb, bignum, "hash",     bignum_hash,   MRB_ARGS_NONE()); /* 15.2.8.3.18 */
  mrb_define_method(mrb, bignum, "to_f",     bignum_to_f,   MRB_ARGS_NONE()); /* 15.2.8.3.23 */
  mrb_define_method(mrb, bignum, "to_s",     bignum_to_s,   MRB_ARGS_OPT(1)); /* 15.2.8.3.25 */
  mrb_define_method(mrb, bignum, "inspect",  bignum_to_s,   MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "to_bn",    bignum_to_big, MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "to_fix",   bignum_to_fix, MRB_ARGS_NONE());
  mrb_define_method(mrb, bignum, "divmod",   bignum_divmod, MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "quo",      bignum_quo,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "**",       bignum_pow,    MRB_ARGS_REQ(1));
  mrb_define_method(mrb, bignum, "coerce",   bignum_coerce, MRB_ARGS_REQ(1)); /* 15.2.7.4.4 */

  /* Redefined Float methods */
  mrb_define_method(mrb, rfloat, "<=>",      float_cmp,     MRB_ARGS_REQ(1)); /* 15.2.9.3.1  */
  mrb_define_method(mrb, rfloat, "<",        float_lt,      MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "<=",       float_le,      MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, ">",        float_gt,      MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, ">=",       float_ge,      MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "==",       float_eq,      MRB_ARGS_REQ(1)); /* 15.2.9.3.2  */
  mrb_define_method(mrb, rfloat, "+",        float_plus,    MRB_ARGS_REQ(1)); /* 15.2.9.3.3  */
  mrb_define_method(mrb, rfloat, "-",        float_minus,   MRB_ARGS_REQ(1)); /* 15.2.9.3.4  */
  mrb_define_method(mrb, rfloat, "*",        float_mul,     MRB_ARGS_REQ(1)); /* 15.2.9.3.5  */
  mrb_define_method(mrb, rfloat, "/",        float_div,     MRB_ARGS_REQ(1)); /* 15.2.9.3.6  */
  mrb_define_method(mrb, rfloat, "%",        float_mod,     MRB_ARGS_REQ(1)); /* 15.2.9.3.7  */
  mrb_define_method(mrb, rfloat, "ceil",     float_ceil,    MRB_ARGS_NONE()); /* 15.2.9.3.8  */
  mrb_define_method(mrb, rfloat, "floor",    float_floor,   MRB_ARGS_NONE()); /* 15.2.9.3.10 */
  mrb_define_method(mrb, rfloat, "to_i",     float_to_i,    MRB_ARGS_NONE()); /* 15.2.9.3.15 */
  mrb_define_method(mrb, rfloat, "to_int",   float_to_i,    MRB_ARGS_NONE());
  mrb_define_method(mrb, rfloat, "to_bn",    float_to_big,  MRB_ARGS_NONE());
  mrb_define_method(mrb, rfloat, "truncate", float_to_i,    MRB_ARGS_NONE()); /* 15.2.9.3.16 */
  mrb_define_method(mrb, rfloat, "divmod",   float_divmod,  MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "quo",      float_quo,     MRB_ARGS_REQ(1));
  mrb_define_method(mrb, rfloat, "**",       float_pow,     MRB_ARGS_REQ(1));

  /* Redefined String methods */
  mrb_define_method(mrb, string, "to_i",     string_to_i,   MRB_ARGS_OPT(1)); /* 15.2.9.3.15 */
  mrb_define_method(mrb, string, "to_int",   string_to_i,   MRB_ARGS_OPT(1));
  mrb_define_method(mrb, string, "to_bn",    string_to_big, MRB_ARGS_OPT(1));

  /* ZeroDivisionError */
  mrb_define_class(mrb, "ZeroDivisionError", mrb->eStandardError_class);
}

void
mrb_mruby_gmp_bignum_gem_final(mrb_state *mrb)
{
}
