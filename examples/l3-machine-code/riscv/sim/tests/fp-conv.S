/* Floating-point ELF 2: every FCVT direction with saturating, boundary
   and tie inputs in all four (non-RMM) rounding modes, FCVT.S.D/D.S special
   values, NaN-boxing round trips through FLW/FSW/FLD/FSD/FMV/FSGNJ, and fcsr
   reads; fflags read and cleared after every case. */
#include "fpmacros.h"

        TEST_START
        ENABLE_FP

        /* ---- float -> int, single ---- */
        FS2I(fcvt.w.s,  rne, 0x3fc00000)    /* 1.5 -> 2 NX */
        FS2I(fcvt.w.s,  rtz, 0xbfc00000)    /* -1.5 -> -1 NX */
        FS2I(fcvt.w.s,  rdn, 0xbfc00000)    /* -2 */
        FS2I(fcvt.w.s,  rup, 0x3fc00000)    /* 2 */
        FS2I(fcvt.w.s,  rne, 0x40200000)    /* 2.5 tie -> 2 */
        FS2I(fcvt.w.s,  rne, 0x4f32d05e)    /* 3e9 NV -> 2^31-1 */
        FS2I(fcvt.w.s,  rne, 0xcf32d05e)    /* -3e9 NV -> -2^31 */
        FS2I(fcvt.w.s,  rne, 0xcf000000)    /* -2^31 exact */
        FS2I(fcvt.w.s,  rne, 0x4f000000)    /* 2^31 NV */
        FS2I(fcvt.w.s,  rne, 0x7fc00000)    /* NaN NV */
        FS2I(fcvt.w.s,  rne, 0xffc00000)    /* -NaN NV -> 2^31-1 */
        FS2I(fcvt.w.s,  rne, 0x7f800001)    /* sNaN NV */
        FS2I(fcvt.w.s,  rne, 0x7f800000)    /* +inf NV */
        FS2I(fcvt.w.s,  rne, 0xff800000)    /* -inf NV */
        FS2I(fcvt.w.s,  rup, 0x80000001)    /* -min sub -> 0 NX */
        FS2I(fcvt.w.s,  rdn, 0x80000001)    /* -> -1 NX */
        FS2I(fcvt.wu.s, rne, 0x4f32d05e)    /* 3e9 -> sign-extended */
        FS2I(fcvt.wu.s, rne, 0x4f800000)    /* 2^32 NV */
        FS2I(fcvt.wu.s, rne, 0xbf800000)    /* -1 NV -> 0 */
        FS2I(fcvt.wu.s, rtz, 0xbf000000)    /* -0.5 RTZ -> 0 NX */
        FS2I(fcvt.wu.s, rdn, 0xbf000000)    /* -0.5 RDN -> NV */
        FS2I(fcvt.wu.s, rne, 0x7fc00000)    /* NaN NV -> 2^32-1 */
        FS2I(fcvt.wu.s, rne, 0xff800000)    /* -inf NV -> 0 */
        FS2I(fcvt.wu.s, rup, 0x00000001)    /* min sub -> 1 NX */
        FS2I(fcvt.l.s,  rne, 0x5f000000)    /* 2^63 NV */
        FS2I(fcvt.l.s,  rne, 0xdf000000)    /* -2^63 exact */
        FS2I(fcvt.l.s,  rup, 0x3fa00000)    /* 1.25 -> 2 NX */
        FS2I(fcvt.l.s,  rne, 0x7f800000)    /* +inf NV */
        FS2I(fcvt.l.s,  rne, 0xff800000)    /* -inf NV */
        FS2I(fcvt.l.s,  rne, 0x7fc00000)    /* NaN NV */
        FS2I(fcvt.lu.s, rne, 0x5f800000)    /* 2^64 NV */
        FS2I(fcvt.lu.s, rne, 0x5f000000)    /* 2^63 exact */
        FS2I(fcvt.lu.s, rne, 0xbf800000)    /* -1 NV */
        FS2I(fcvt.lu.s, rne, 0x80000000)    /* -0 -> 0 exact */
        FS2I(fcvt.lu.s, rne, 0x7fc00000)    /* NaN NV */
        FS2I(fcvt.lu.s, rne, 0xff800000)    /* -inf NV */
        /* unboxed single input (a double in the register): canonical NaN */
        LD(f1, 0x3ff0000000000000)
        fcvt.w.s a0, f1, rne
        SAVE(a0)
        FLAGS

        /* ---- float -> int, double ---- */
        FD2I(fcvt.w.d,  rtz, 0xc1e0000000100000)   /* -2147483648.5 RTZ -> -2^31 NX */
        FD2I(fcvt.w.d,  rdn, 0xc1e0000000100000)   /* RDN -> NV */
        FD2I(fcvt.w.d,  rne, 0x41dfffffffe00000)   /* 2147483647.5 RNE -> NV */
        FD2I(fcvt.w.d,  rtz, 0x41dfffffffe00000)   /* RTZ -> 2^31-1 NX */
        FD2I(fcvt.w.d,  rne, 0x41e0000000000000)   /* 2^31 NV */
        FD2I(fcvt.w.d,  rne, 0x7ff8000000000000)   /* NaN NV */
        FD2I(fcvt.w.d,  rne, 0xfff0000000000000)   /* -inf NV */
        FD2I(fcvt.wu.d, rne, 0x41efffffffe00000)   /* 2^32-1 -> all ones */
        FD2I(fcvt.wu.d, rne, 0x41e0000000000000)   /* 2^31 -> sign-extended */
        FD2I(fcvt.wu.d, rne, 0x41effffffff00000)   /* 4294967295.5 RNE -> NV */
        FD2I(fcvt.wu.d, rtz, 0x41effffffff00000)   /* RTZ -> 2^32-1 NX */
        FD2I(fcvt.wu.d, rne, 0xfff0000000000000)   /* -inf NV -> 0 */
        FD2I(fcvt.wu.d, rne, 0x7ff0000000000001)   /* sNaN NV */
        FD2I(fcvt.l.d,  rne, 0x3fe0000000000000)   /* 0.5 -> 0 NX */
        FD2I(fcvt.l.d,  rne, 0x3ff8000000000000)   /* 1.5 -> 2 NX */
        FD2I(fcvt.l.d,  rne, 0xc3e0000000000000)   /* -2^63 exact */
        FD2I(fcvt.l.d,  rne, 0xc3e0000000000001)   /* below -2^63 NV */
        FD2I(fcvt.l.d,  rne, 0x43e0000000000000)   /* 2^63 NV */
        FD2I(fcvt.l.d,  rtz, 0xc036200000000000)   /* -22.125 RTZ -> -22 NX */
        FD2I(fcvt.l.d,  rne, 0x7ff0000000000001)   /* sNaN NV */
        FD2I(fcvt.l.d,  rne, 0x7ff0000000000000)   /* +inf NV */
        FD2I(fcvt.lu.d, rne, 0x43efffffffffffff)   /* just below 2^64 exact */
        FD2I(fcvt.lu.d, rne, 0x43f0000000000000)   /* 2^64 NV */
        FD2I(fcvt.lu.d, rne, 0x4415af1d78b58c40)   /* 1e20 NV */
        FD2I(fcvt.lu.d, rne, 0x8000000000000000)   /* -0 -> 0 exact */
        FD2I(fcvt.lu.d, rup, 0xbfe0000000000000)   /* -0.5 RUP -> 0 NX */
        FD2I(fcvt.lu.d, rne, 0xfff8000000000000)   /* -NaN NV -> all ones */

        /* ---- int -> single ---- */
        I2F(fcvt.s.w,  rne, 16777217)              /* NX */
        I2F(fcvt.s.w,  rup, 16777217)
        I2F(fcvt.s.w,  rne, 0x12345678ffffffff)    /* -1, upper bits ignored */
        I2F(fcvt.s.w,  rdn, 0)                     /* +0 in every mode */
        I2F(fcvt.s.w,  rne, -2147483648)
        I2F(fcvt.s.wu, rne, 0xffffffff)            /* NX */
        I2F(fcvt.s.wu, rtz, 0xffffffff)
        I2F(fcvt.s.l,  rne, -1)
        I2F(fcvt.s.l,  rne, 0x7fffffffffffffff)    /* NX */
        I2F(fcvt.s.l,  rup, -16777217)
        I2F(fcvt.s.l,  rne, 0x8000000000000000)    /* -2^63 exact */
        I2F(fcvt.s.lu, rne, 0xffffffffffffffff)    /* 2^64-1: NX */
        I2F(fcvt.s.lu, rtz, 0xffffffffffffffff)
        I2F(fcvt.s.lu, rne, 0x8000000000000000)    /* 2^63 exact */
        I2F(fcvt.s.lu, rne, 0x8000008000000000)    /* tie -> even */
        I2F(fcvt.s.lu, rne, 0x8000008000000001)    /* above tie (sticky) */
        I2F(fcvt.s.lu, rup, 0x8000000000000001)
        I2F(fcvt.s.lu, rdn, 0xffffff7fffffffff)
        I2F(fcvt.s.lu, rne, 0x8000018000000000)    /* tie, odd -> up */

        /* ---- int -> double ---- */
        I2FX(fcvt.d.w,  -5)
        I2FX(fcvt.d.w,  0x12345678ffffffff)
        I2FX(fcvt.d.wu, 0xffffffff)
        I2F(fcvt.d.l,  rne, 0x20000000000001)      /* 2^53+1 NX */
        I2F(fcvt.d.l,  rup, 0x20000000000001)
        I2F(fcvt.d.l,  rne, 0x8000000000000001)    /* -2^63+1 NX */
        I2F(fcvt.d.l,  rdn, 0x8000000000000001)
        I2F(fcvt.d.l,  rup, 0x8000000000000001)
        I2F(fcvt.d.l,  rdn, 0xa5aa5a5a5a5a5a5b)    /* below -2^62 */
        I2F(fcvt.d.l,  rup, 0xa5aa5a5a5a5a5a5b)
        I2F(fcvt.d.l,  rtz, 0xa5aa5a5a5a5a5a5b)
        I2F(fcvt.d.l,  rdn, 0xc000000000000000)    /* -2^62 exact */
        I2F(fcvt.d.lu, rne, 0xffffffffffffffff)    /* NX */
        I2F(fcvt.d.lu, rdn, 0xffffffffffffffff)
        I2F(fcvt.d.lu, rup, 0x8000000000000001)

        /* ---- double <-> single ---- */
        D2S(rne, 0x3fb999999999999a)               /* 0.1 NX */
        D2S(rtz, 0x3fb999999999999a)
        D2S(rne, 0x7e37e43c8800759c)               /* 1e300 OF NX -> inf */
        D2S(rtz, 0x7e37e43c8800759c)               /* -> max */
        D2S(rne, 0x01a56e1fc2f8f359)               /* 1e-300 UF NX -> 0 */
        D2S(rup, 0x01a56e1fc2f8f359)               /* -> min sub */
        D2S(rne, 0x81a56e1fc2f8f359)               /* -1e-300 -> -0 */
        D2S(rne, 0x380ffffff8000000)               /* tiny, rounds to min normal: NX only */
        D2S(rtz, 0x47effffff0000000)               /* max + ulp/2 RTZ: NX only */
        D2S(rne, 0x47effffff0000000)               /* RNE: OF NX */
        D2S(rne, 0x8000000000000000)               /* -0 */
        D2S(rne, 0x7ff8000020000000)               /* qNaN payload -> canonical */
        D2S(rne, 0x7ff0000000000001)               /* sNaN NV */
        D2S(rne, 0xfff0000000000000)               /* -inf */
        S2D(0x7fc00001)                       /* qNaN payload -> canonical */
        S2D(0x7f800001)                       /* sNaN NV */
        S2D(0xffc12345)
        S2D(0x80000000)                       /* -0 */
        S2D(0x00000001)                       /* min sub exact */
        S2D(0xff800000)                       /* -inf */

        /* ---- NaN-boxing round trips ---- */
        la      s0, data
        flw     f5, 0(s0)                          /* sNaN pattern, boxed, unchanged */
        fmv.x.d a0, f5
        SAVE(a0)
        fsw     f5, 16(s0)                         /* raw low 32 bits */
        ld      a0, 16(s0)
        SAVE(a0)
        flw     f6, 4(s0)                          /* qNaN payload pattern */
        fmv.x.w a0, f6                             /* sign-extended */
        SAVE(a0)
        fld     f7, 8(s0)                          /* a double: not a boxed single */
        fmv.x.w a0, f7                             /* raw low bits */
        SAVE(a0)
        fsw     f7, 24(s0)                         /* raw low bits */
        lw      a0, 24(s0)
        SAVE(a0)
        fadd.s  f8, f7, f7                         /* unboxed -> canonical NaN */
        fmv.x.d a0, f8
        SAVE(a0)
        FLAGS
        fsgnj.s f9, f7, f5                         /* canonical NaN with sNaN's sign */
        fmv.x.d a0, f9
        SAVE(a0)
        fsgnjn.s f9, f5, f5                        /* bit-exact, boxed */
        fmv.x.d a0, f9
        SAVE(a0)
        fsgnjx.s f9, f6, f6
        fmv.x.d a0, f9
        SAVE(a0)
        FLAGS
        li      t1, 0x12345678ffc00001
        fmv.w.x f10, t1                            /* boxed, payload kept */
        fmv.x.d a0, f10
        SAVE(a0)
        fsd     f10, 32(s0)                        /* all 64 bits */
        ld      a0, 32(s0)
        SAVE(a0)
        fmv.x.w a0, f10
        SAVE(a0)
        fsgnj.d f11, f10, f10                      /* D op on a boxed single */
        fmv.x.d a0, f11
        SAVE(a0)
        fcvt.s.w f12, zero                         /* +0, boxed, no flags */
        fmv.x.d a0, f12
        SAVE(a0)
        FLAGS
        /* compressed FP loads and stores */
        mv      s1, sp
        mv      sp, s0
        c.fldsp f13, 8(sp)
        c.fsdsp f13, 40(sp)
        mv      sp, s1
        c.fld   f14, 8(s0)
        c.fsd   f14, 48(s0)
        ld      a0, 40(s0)
        SAVE(a0)
        ld      a0, 48(s0)
        SAVE(a0)

        /* ---- fcsr: frm and accrued flags together.  Written through
           frm and fflags only: sail logs a write of fcsr under that name
           only, so compare.py would keep stale fflags/frm values. ---- */
        li      t0, 3
        fsrm    t0                                 /* frm = RUP */
        fsflags zero
        LS(f1, 0x3f800000)
        LS(f2, 0x33800000)
        fadd.s  f3, f1, f2, dyn                    /* RUP, NX */
        LS(f2, 0x00000000)
        fdiv.s  f3, f1, f2, dyn                    /* DZ */
        csrr    a0, fcsr                           /* 0x69 */
        SAVE(a0)
        csrr    a0, fflags
        SAVE(a0)
        csrr    a0, frm
        SAVE(a0)
        li      t0, 0x1f
        fsflags t0
        csrr    a0, fcsr                           /* 0x7f */
        SAVE(a0)
        fsrm    zero
        fsflags zero
        csrr    a0, fcsr                           /* 0 */
        SAVE(a0)

        j       pass

        TEST_END

        .data
        .align  3
data:   .word   0x7f800001
        .word   0xffc0dead
        .dword  0x400921fb54442d18
        .dword  0
        .dword  0
        .dword  0
        .dword  0
        .dword  0
        SIGNATURE(512)
