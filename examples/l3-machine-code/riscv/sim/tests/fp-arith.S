/* Batch B acceptance ELF 1: F/D arithmetic, FMA, FMIN/FMAX, FCLASS and
   compares, with NaN, sNaN, infinity, subnormal and tie inputs in all four
   (non-RMM) rounding modes; fflags read and cleared after every case. */
#include "fpmacros.h"

        TEST_START
        ENABLE_FP

        /* ---- FADD/FSUB/FMUL/FDIV/FSQRT.S ---- */
        S2(fadd.s, rne, 0x3f800000, 0x40000000)     /* 1+2 exact */
        S2(fadd.s, rne, 0x3f800000, 0x30800000)     /* 1+2^-30 NX */
        S2(fadd.s, rne, 0x3f800000, 0x33800000)     /* tie: 1+2^-24 -> 1 */
        S2(fadd.s, rup, 0x3f800000, 0x33800000)     /* -> 1+ulp */
        S2(fadd.s, rdn, 0x3f800000, 0x33800000)
        S2(fadd.s, rtz, 0x3f800000, 0x33800000)
        S2(fadd.s, rne, 0x3f800000, 0x34400000)     /* tie to even upwards */
        S2(fadd.s, rne, 0xbf800000, 0xb3800000)     /* negative tie */
        S2(fadd.s, rup, 0xbf800000, 0xb3800000)
        S2(fadd.s, rdn, 0xbf800000, 0xb3800000)
        S2(fadd.s, rne, 0x3f800000, 0xbf800000)     /* 1-1 = +0 */
        S2(fadd.s, rdn, 0x3f800000, 0xbf800000)     /* 1-1 = -0 in RDN */
        S2(fadd.s, rne, 0x80000000, 0x80000000)     /* -0 + -0 = -0 */
        S2(fadd.s, rne, 0x7fc00001, 0x3f800000)     /* qNaN payload -> canonical */
        S2(fadd.s, rne, 0x7f800001, 0x3f800000)     /* sNaN NV */
        S2(fadd.s, rne, 0x3f800000, 0xff800001)     /* -sNaN in rs2 NV */
        S2(fadd.s, rne, 0x7f800000, 0xff800000)     /* inf-inf NV */
        S2(fadd.s, rne, 0x7f800000, 0x3f800000)     /* inf+1 */
        S2(fadd.s, rne, 0x00000001, 0x007fffff)     /* subnormal + subnormal = min normal */
        S2(fadd.s, rne, 0x00800000, 0x80000001)     /* min normal - min sub: exact subnormal */
        S2(fsub.s, rne, 0x7f800000, 0x7f800000)     /* inf-inf NV */
        S2(fsub.s, rdn, 0x40000000, 0x40000000)     /* 2-2 = -0 in RDN */
        S2(fsub.s, rup, 0x7f7fffff, 0xff7fffff)     /* overflow RUP -> inf */
        S2(fsub.s, rtz, 0x7f7fffff, 0xff7fffff)     /* overflow RTZ -> max */
        S2(fsub.s, rdn, 0x7f7fffff, 0xff7fffff)     /* overflow RDN -> max */
        S2(fmul.s, rne, 0x7f7fffff, 0x40000000)     /* OF NX */
        S2(fmul.s, rne, 0x00800000, 0x00800000)     /* UF NX -> 0 */
        S2(fmul.s, rup, 0x00800000, 0x00800000)     /* UF NX -> min sub */
        S2(fmul.s, rne, 0x00000001, 0x3f000000)     /* min sub * 0.5: tie -> 0, UF NX */
        S2(fmul.s, rne, 0x00000001, 0x3fc00000)     /* min sub * 1.5: tie -> 2 ulp */
        S2(fmul.s, rne, 0x00000003, 0x3f000000)     /* 3 ulp * 0.5 = 1.5 ulp -> 2 */
        S2(fmul.s, rne, 0x3f7fffff, 0x00800000)     /* tiny after rounding, UF NX */
        S2(fmul.s, rne, 0x00800000, 0x40000000)     /* exact */
        S2(fmul.s, rne, 0x7f800000, 0x00000000)     /* inf*0 NV */
        S2(fmul.s, rne, 0xff800000, 0x40000000)     /* -inf*2 */
        S2(fmul.s, rne, 0x80000000, 0x3f800000)     /* -0*1 = -0 */
        S2(fmul.s, rne, 0x7fc0beef, 0x40000000)     /* qNaN payload */
        S2(fdiv.s, rne, 0x3f800000, 0x00000000)     /* 1/0 DZ */
        S2(fdiv.s, rne, 0xbf800000, 0x00000000)     /* -1/0 DZ */
        S2(fdiv.s, rne, 0x00000000, 0x00000000)     /* 0/0 NV */
        S2(fdiv.s, rne, 0x7f800000, 0x7f800000)     /* inf/inf NV */
        S2(fdiv.s, rne, 0x7f800000, 0x00000000)     /* inf/0 = inf, no flag */
        S2(fdiv.s, rne, 0x3f800000, 0x40400000)     /* 1/3 NX */
        S2(fdiv.s, rup, 0x3f800000, 0x40400000)
        S2(fdiv.s, rdn, 0x3f800000, 0x40400000)
        S2(fdiv.s, rtz, 0xbf800000, 0x40400000)
        S2(fdiv.s, rne, 0x00800000, 0x40000000)     /* min normal / 2: exact subnormal */
        S2(fdiv.s, rne, 0x00800001, 0x40000000)     /* inexact subnormal UF NX */
        S2(fdiv.s, rne, 0x3f800000, 0xffc00001)     /* 1 / -qNaN */
        S1(fsqrt.s, rne, 0x40000000)                /* sqrt 2 NX */
        S1(fsqrt.s, rup, 0x40000000)
        S1(fsqrt.s, rne, 0x40800000)                /* sqrt 4 exact */
        S1(fsqrt.s, rne, 0xbf800000)                /* sqrt -1 NV */
        S1(fsqrt.s, rne, 0x80000000)                /* sqrt -0 = -0 */
        S1(fsqrt.s, rne, 0x7f800000)                /* sqrt inf */
        S1(fsqrt.s, rne, 0xff800000)                /* sqrt -inf NV */
        S1(fsqrt.s, rne, 0xffc00000)                /* sqrt -qNaN: no flag */
        S1(fsqrt.s, rne, 0x7f800001)                /* sqrt sNaN NV */
        S1(fsqrt.s, rne, 0x00000001)                /* sqrt min sub NX */
        S1(fsqrt.s, rdn, 0x007fffff)

        /* dynamic rounding mode */
        fsrmi   3
        S2(fadd.s, dyn, 0x3f800000, 0x33800000)     /* RUP via frm */
        fsrmi   2
        D2(fadd.d, dyn, 0xbff0000000000000, 0xbca0000000000000)  /* RDN via frm */
        fsrmi   1
        S2(fdiv.s, dyn, 0x3f800000, 0x40400000)     /* RTZ via frm */
        fsrm    zero                                /* not fsrmi 0: CSRRWI zimm=0 is F1 (WP2) */

        /* ---- FADD/FSUB/FMUL/FDIV/FSQRT.D ---- */
        D2(fadd.d, rne, 0x3ff0000000000000, 0x4000000000000000)
        D2(fadd.d, rne, 0x3ff0000000000000, 0x3c30000000000000)  /* NX */
        D2(fadd.d, rne, 0x3ff0000000000000, 0x3ca0000000000000)  /* tie */
        D2(fadd.d, rup, 0x3ff0000000000000, 0x3ca0000000000000)
        D2(fadd.d, rne, 0x3ff0000000000000, 0x3cb8000000000000)  /* tie to even up */
        D2(fadd.d, rne, 0x7ff8000000000001, 0x3ff0000000000000)  /* qNaN payload */
        D2(fadd.d, rne, 0x7ff0000000000001, 0x3ff0000000000000)  /* sNaN NV */
        D2(fadd.d, rne, 0x7ff0000000000000, 0xfff0000000000000)  /* inf-inf NV */
        D2(fadd.d, rne, 0x0000000000000001, 0x000fffffffffffff)  /* subnormals */
        D2(fsub.d, rdn, 0x4000000000000000, 0x4000000000000000)  /* -0 */
        D2(fsub.d, rne, 0xfff8000000000001, 0x3ff0000000000000)  /* -qNaN */
        D2(fmul.d, rne, 0x7fefffffffffffff, 0x4000000000000000)  /* OF NX */
        D2(fmul.d, rtz, 0x7fefffffffffffff, 0x4000000000000000)  /* OF NX -> max */
        D2(fmul.d, rne, 0x0010000000000000, 0x0010000000000000)  /* UF NX */
        D2(fmul.d, rne, 0x0000000000000001, 0x3fe0000000000000)  /* tie -> 0 */
        D2(fmul.d, rne, 0x0000000000000003, 0x3fe0000000000000)  /* 1.5 ulp -> 2 */
        D2(fmul.d, rne, 0x7ff0000000000000, 0x0000000000000000)  /* inf*0 NV */
        D2(fdiv.d, rne, 0x3ff0000000000000, 0x0000000000000000)  /* DZ */
        D2(fdiv.d, rne, 0x0000000000000000, 0x0000000000000000)  /* NV */
        D2(fdiv.d, rne, 0x3ff0000000000000, 0x4008000000000000)  /* 1/3 NX */
        D2(fdiv.d, rup, 0x3ff0000000000000, 0x4008000000000000)
        D2(fdiv.d, rdn, 0xbff0000000000000, 0x4008000000000000)
        D2(fdiv.d, rtz, 0xbff0000000000000, 0x4008000000000000)
        D2(fdiv.d, rne, 0x0010000000000001, 0x4000000000000000)  /* UF NX */
        D1(fsqrt.d, rne, 0x4000000000000000)
        D1(fsqrt.d, rdn, 0x4000000000000000)
        D1(fsqrt.d, rne, 0xbff0000000000000)                     /* NV */
        D1(fsqrt.d, rne, 0x8000000000000000)                     /* -0 */
        D1(fsqrt.d, rne, 0xfff8000000000000)                     /* -qNaN */
        D1(fsqrt.d, rne, 0x7ff0000000000001)                     /* sNaN NV */
        D1(fsqrt.d, rne, 0x0000000000000001)

        /* ---- FMA family ---- */
        S3(fmadd.s,  rne, 0x3f800001, 0x3f7ffffe, 0xbf800000)    /* fused: -2^-46 */
        S3(fmsub.s,  rne, 0x3f800001, 0x3f7ffffe, 0x3f800000)
        S3(fnmsub.s, rne, 0x3f800001, 0x3f7ffffe, 0x3f800000)
        S3(fnmadd.s, rne, 0x3f800001, 0x3f7ffffe, 0xbf800000)
        S3(fmadd.s,  rtz, 0x3f800001, 0x3f7ffffe, 0xbf800000)
        S3(fnmsub.s, rne, 0x3f800000, 0x3f800000, 0x3f800000)    /* +0 */
        S3(fnmadd.s, rup, 0x3f800000, 0x3f800000, 0x33800000)    /* -1 NX */
        S3(fnmadd.s, rdn, 0x3f800000, 0x3f800000, 0x33800000)
        S3(fmadd.s,  rdn, 0x3f800000, 0x3f800000, 0xbf800000)    /* -0 */
        S3(fnmadd.s, rne, 0x00000000, 0x3f800000, 0x00000000)    /* -0 */
        S3(fmsub.s,  rne, 0x00000000, 0x3f800000, 0x00000000)    /* +0 */
        S3(fmadd.s,  rne, 0x7f800000, 0x00000000, 0x7fc00000)    /* inf*0+qNaN NV */
        S3(fmadd.s,  rne, 0x00000000, 0xff800000, 0x7fc00000)    /* 0*-inf+qNaN NV */
        S3(fnmsub.s, rne, 0x7f800000, 0x00000000, 0x7fc00000)
        S3(fmadd.s,  rne, 0x7f800000, 0x00000000, 0x3f800000)    /* inf*0+1 NV */
        S3(fmadd.s,  rne, 0x7f800000, 0x40000000, 0x7fc00000)    /* inf*2+qNaN: no NV */
        S3(fmadd.s,  rne, 0x7f800000, 0x3f800000, 0xff800000)    /* inf-inf NV */
        S3(fmadd.s,  rne, 0x7f800001, 0x3f800000, 0x3f800000)    /* sNaN NV */
        S3(fmadd.s,  rne, 0x7f7fffff, 0x40000000, 0x00000000)    /* OF NX */
        S3(fmadd.s,  rne, 0x00800000, 0x00800000, 0x00000000)    /* UF NX */
        S3(fmadd.s,  rne, 0x00800000, 0x3f800000, 0x80000001)    /* exact subnormal */
        S3(fmadd.s,  rne, 0x40000000, 0x40400000, 0x3f800000)    /* 7 */
        D3(fmadd.d,  rne, 0x3ff0000000000001, 0x3feffffffffffffe, 0xbff0000000000000)
        D3(fnmsub.d, rne, 0x3ff0000000000000, 0x3ff0000000000000, 0x3ff0000000000000)
        D3(fnmadd.d, rup, 0x3ff0000000000000, 0x3ff0000000000000, 0x3c30000000000000)
        D3(fmsub.d,  rne, 0x3ff0000000000000, 0x7ff0000000000003, 0x3ff0000000000000)  /* sNaN */
        D3(fmadd.d,  rne, 0x7ff0000000000000, 0x0000000000000000, 0x7ff8000000000000)  /* NV */
        D3(fnmadd.d, rne, 0x8000000000000000, 0x3ff0000000000000, 0x0000000000000000)  /* +0 */
        D3(fmadd.d,  rne, 0x400b000000000000, 0xc01c000000000000, 0x3ff8000000000000)

        /* ---- FMIN/FMAX ---- */
        S2N(fmin.s, 0x00000000, 0x80000000)
        S2N(fmin.s, 0x80000000, 0x00000000)
        S2N(fmax.s, 0x00000000, 0x80000000)
        S2N(fmax.s, 0x80000000, 0x00000000)
        S2N(fmin.s, 0x7f800001, 0x3f800000)     /* sNaN: other operand, NV */
        S2N(fmax.s, 0x3f800000, 0xff800001)
        S2N(fmin.s, 0x7fc00001, 0x3f800000)     /* qNaN: other operand */
        S2N(fmin.s, 0x7fc00002, 0x7fc00001)     /* both NaN: canonical */
        S2N(fmax.s, 0x7f800001, 0x7fc00000)     /* both NaN, one sNaN: canonical, NV */
        S2N(fmin.s, 0xff800000, 0x3f800000)
        S2N(fmax.s, 0x00000001, 0x80000001)
        D2N(fmin.d, 0x0000000000000000, 0x8000000000000000)
        D2N(fmax.d, 0x0000000000000000, 0x8000000000000000)
        D2N(fmin.d, 0x7ff0000000000001, 0x3ff0000000000000)
        D2N(fmax.d, 0x7ff8000000000001, 0x7ff8000000000002)
        D2N(fmax.d, 0xfff8000000000000, 0xbff0000000000000)

        /* ---- FCLASS, every class ---- */
        SCLASS(0xff800000)
        SCLASS(0xbf800000)
        SCLASS(0x80000001)
        SCLASS(0x80000000)
        SCLASS(0x00000000)
        SCLASS(0x007fffff)
        SCLASS(0x3f800000)
        SCLASS(0x7f800000)
        SCLASS(0x7f800001)
        SCLASS(0xffbfffff)
        SCLASS(0x7fc00000)
        SCLASS(0x7fc00001)
        SCLASS(0xffc00000)
        DCLASS(0xfff0000000000000)
        DCLASS(0xbff0000000000000)
        DCLASS(0x8000000000000001)
        DCLASS(0x8000000000000000)
        DCLASS(0x0000000000000000)
        DCLASS(0x000fffffffffffff)
        DCLASS(0x3ff0000000000000)
        DCLASS(0x7ff0000000000000)
        DCLASS(0x7ff0000000000001)
        DCLASS(0x7ff8000000000000)
        DCLASS(0xfff8000000000001)
        /* unboxed single (a double in the register): canonical NaN, class 0x200 */
        LD(f1, 0x3ff0000000000000)
        fclass.s a0, f1
        SAVE(a0)
        FLAGS

        /* ---- compares ---- */
        SCMP(feq.s, 0x3f800000, 0x3f800000)
        SCMP(feq.s, 0x00000000, 0x80000000)
        SCMP(feq.s, 0x7fc00000, 0x3f800000)     /* quiet: no flag */
        SCMP(feq.s, 0x7f800001, 0x3f800000)     /* NV */
        SCMP(flt.s, 0x3f800000, 0x40000000)
        SCMP(flt.s, 0x7fc00000, 0x3f800000)     /* NV */
        SCMP(fle.s, 0x80000000, 0x00000000)
        SCMP(fle.s, 0x3f800000, 0x7fc00000)     /* NV */
        DCMP(feq.d, 0x7ff8000000000000, 0x7ff8000000000000)
        DCMP(feq.d, 0x7ff0000000000001, 0x0000000000000000)
        DCMP(flt.d, 0xbff0000000000000, 0x3ff0000000000000)
        DCMP(fle.d, 0x0000000000000000, 0x7ff8000000000000)

        j       pass

        TEST_END
        SIGNATURE(512)
