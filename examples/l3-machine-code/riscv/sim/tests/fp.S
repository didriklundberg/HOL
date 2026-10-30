/* Smoke test (c): double-precision floating point (fld, fadd.d, fmul.d,
   fmadd.d, fcvt.l.d, fcvt.d.l, feq.d, fsd, fmv.x.d), checked against known
   IEEE 754 results.  Assembled without C.  The default rounding mode is
   used through the instructions' dyn rm field; with ENABLE_FS (always,
   since mstatus.FS resets to Off) the only CSR access enables FP. */
#include "test.h"

        TEST_START

#ifdef ENABLE_FS
        /* sail-riscv and the model reset mstatus.FS (bits 14:13) to Off,
           which makes FP instructions illegal; setting bit 13 makes it
           Initial. */
        li      t0, 0x2000
        csrs    mstatus, t0
#endif
        la      s0, data

        /* 1: 1.5 + 2.25 = 3.75 */
        fld     fa0, 0(s0)
        fld     fa1, 8(s0)
        fadd.d  fa2, fa0, fa1
        fmv.x.d a0, fa2
        RESULT(a0)
        CHECK(1, a0, 0x400e000000000000)

        /* 2: 1.5 * 2.25 = 3.375 */
        fmul.d  fa3, fa0, fa1
        fmv.x.d a0, fa3
        CHECK(2, a0, 0x400b000000000000)

        /* 3: fcvt.d.l -7 and fmadd.d 3.375 * -7 + 1.5 = -22.125 */
        li      a1, -7
        fcvt.d.l fa4, a1
        fmadd.d fa5, fa3, fa4, fa0
        fsd     fa5, 16(s0)
        ld      a0, 16(s0)
        RESULT(a0)
        CHECK(3, a0, 0xc036200000000000)

        /* 4: fcvt.l.d with round-towards-zero: -22.125 -> -22 */
        fcvt.l.d a0, fa5, rtz
        RESULT(a0)
        CHECK(4, a0, -22)

        /* 5: 0.1 + 0.2 rounds to 0x3fd3333333333334, not 0.3 */
        fld     fa0, 24(s0)
        fld     fa1, 32(s0)
        fadd.d  fa2, fa0, fa1
        fmv.x.d a0, fa2
        RESULT(a0)
        CHECK(5, a0, 0x3fd3333333333334)
        fld     fa3, 40(s0)
        feq.d   a0, fa2, fa3
        CHECK(6, a0, 0)

        j       pass

        TEST_END

        .data
        .align  3
data:   .double 1.5
        .double 2.25
        .dword  0
        .double 0.1
        .double 0.2
        .double 0.3

        SIGNATURE(5)
