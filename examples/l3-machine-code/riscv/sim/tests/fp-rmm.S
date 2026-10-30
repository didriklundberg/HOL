/* Batch B: rounding mode RMM.  The exact conversions FCVT.D.S, FCVT.D.W and
   FCVT.D.WU accept RMM (static and dynamic) and must agree with sail; the
   last instruction, FADD.S with RMM, is the deferred part of F13: the model
   raises illegal instruction, sail rounds ties away from zero.  The model
   then traps to mtvec = 0 and ends in a trap loop (riscv-sim exit 4), so
   the expected result is a divergence at that instruction and no earlier. */
#include "fpmacros.h"

        TEST_START
        ENABLE_FP
        LS(f2, 0x3f800000)                 /* 1.0f */
        li      x2, 7
        .word   0x420140d3                 /* fcvt.d.s f1, f2, rmm */
        fmv.x.d a0, f1
        SAVE(a0)
        FLAGS
        .word   0xd20140d3                 /* fcvt.d.w f1, x2, rmm */
        fmv.x.d a0, f1
        SAVE(a0)
        FLAGS
        li      x2, -1
        .word   0xd21140d3                 /* fcvt.d.wu f1, x2, rmm */
        fmv.x.d a0, f1
        SAVE(a0)
        FLAGS
        LS(f2, 0x7f800001)                 /* sNaN */
        .word   0x420140d3                 /* fcvt.d.s f1, f2, rmm: canonical, NV */
        fmv.x.d a0, f1
        SAVE(a0)
        FLAGS
        li      t0, 4
        fsrm    t0                         /* frm = RMM */
        LS(f2, 0xc0490fdb)
        .word   0x420170d3                 /* fcvt.d.s f1, f2, dyn */
        fmv.x.d a0, f1
        SAVE(a0)
        li      x2, 0x80000000
        .word   0xd20170d3                 /* fcvt.d.w f1, x2, dyn */
        fmv.x.d a0, f1
        SAVE(a0)
        FLAGS
        fsrm    zero
        /* deferred: RMM in an instruction that rounds */
        LS(f2, 0x3f800000)
        LS(f3, 0x33800000)                 /* 2^-24: a tie */
rmm_fadd:                                  /* make test and make compare check this pc */
        .word   0x003140d3                 /* fadd.s f1, f2, f3, rmm */
        fmv.x.d a0, f1
        SAVE(a0)
        j       pass

        TEST_END
        SIGNATURE(16)
