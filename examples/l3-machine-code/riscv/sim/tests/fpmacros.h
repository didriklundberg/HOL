/* Macros for the batch B floating-point ELFs.  Every case leaves its
   result in a GPR, reads and clears fflags with fsflags, and stores both
   to the signature region (s11), so that compare.py compares values and
   accrued flags step by step against sail. */
#include "test.h"

#define SAVE(r)        sd r, 0(s11); addi s11, s11, 8
#define FLAGS          fsflags a1, zero; SAVE(a1)

/* single: operands as raw 32-bit patterns, boxed by fmv.w.x */
#define LS(f, v)       li t1, v; fmv.w.x f, t1
/* double: raw 64-bit patterns */
#define LD(f, v)       li t1, v; fmv.d.x f, t1

#define S2(op, rm, a, b)     LS(f1, a); LS(f2, b); op f3, f1, f2, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define S2N(op, a, b)        LS(f1, a); LS(f2, b); op f3, f1, f2; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define S1(op, rm, a)        LS(f1, a); op f3, f1, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define S3(op, rm, a, b, c)  LS(f1, a); LS(f2, b); LS(f4, c); op f3, f1, f2, f4, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define D2(op, rm, a, b)     LD(f1, a); LD(f2, b); op f3, f1, f2, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define D2N(op, a, b)        LD(f1, a); LD(f2, b); op f3, f1, f2; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define D1(op, rm, a)        LD(f1, a); op f3, f1, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define D3(op, rm, a, b, c)  LD(f1, a); LD(f2, b); LD(f4, c); op f3, f1, f2, f4, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
/* compare/classify: integer result */
#define SCMP(op, a, b)       LS(f1, a); LS(f2, b); op a0, f1, f2; SAVE(a0); FLAGS
#define DCMP(op, a, b)       LD(f1, a); LD(f2, b); op a0, f1, f2; SAVE(a0); FLAGS
#define SCLASS(a)            LS(f1, a); fclass.s a0, f1; SAVE(a0); FLAGS
#define DCLASS(a)            LD(f1, a); fclass.d a0, f1; SAVE(a0); FLAGS
/* float -> int */
#define FS2I(op, rm, a)      LS(f1, a); op a0, f1, rm; SAVE(a0); FLAGS
#define FD2I(op, rm, a)      LD(f1, a); op a0, f1, rm; SAVE(a0); FLAGS
/* int -> float, and float -> float conversions */
#define I2F(op, rm, v)       li t1, v; op f3, t1, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
/* exact conversions: the assembler takes no rm operand (it encodes rm=000) */
#define I2FX(op, v)          li t1, v; op f3, t1; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define D2S(rm, a)           LD(f1, a); fcvt.s.d f3, f1, rm; fmv.x.d a0, f3; SAVE(a0); FLAGS
#define S2D(a)               LS(f1, a); fcvt.d.s f3, f1; fmv.x.d a0, f3; SAVE(a0); FLAGS

#define ENABLE_FP            li t0, 0x6000; csrs mstatus, t0; fsflags zero
