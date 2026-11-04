/* Regression test for the unprivileged audit fixes of the RISC-V L3 model:
   F3 (failed SC clears the reservation), F4 (AMOMIN/MAX[U].W ignore rs2<63:32>),
   F15 (C.ADDIW with rd != x0),
   F20 (DIV/REM/REMU with rd aliasing a source, x/0, MIN/-1).
   Self-checking in the style of sim/tests (test.h); build with
   -march=rv64imac -mabi=lp64.  No CSR is touched. */
#include "test.h"

#define MIN64 0x8000000000000000
#define MIN32W 0xffffffff80000000

        TEST_START
        la      s0, data            /* A = s0, B = s0+8 (another 8-byte reservation set) */
        addi    s1, s0, 8

        /* ---- F3: LR/SC ---- */
        /* 1-3: LR.W A; SC.W B fails; SC.W A must then fail too and leave A */
        li      a1, 0x12345678
        lr.w    a0, (s0)
        RESULT(a0)
        sc.w    a2, a1, (s1)
        CHECK(1, a2, 1)
        sc.w    a3, a1, (s0)
        CHECK(2, a3, 1)
        ld      a4, 0(s0)
        RESULT(a4)
        CHECK(3, a4, 0x0aaaaaaa0aaaaaaa)
        /* 4-6: same with LR.D/SC.D */
        lr.d    a0, (s0)
        sc.d    a2, a1, (s1)
        CHECK(4, a2, 1)
        sc.d    a3, a1, (s0)
        CHECK(5, a3, 1)
        ld      a4, 0(s0)
        CHECK(6, a4, 0x0aaaaaaa0aaaaaaa)
        /* 7-8: a failed SC.W with rd = x0 also cancels */
        lr.w    a0, (s0)
        sc.w    zero, a1, (s1)
        sc.w    a3, a1, (s0)
        CHECK(7, a3, 1)
        ld      a4, 0(s0)
        CHECK(8, a4, 0x0aaaaaaa0aaaaaaa)
        /* 9-11 (control): LR.W A; SC.W A succeeds; a second SC.W A fails */
        lr.w    a0, (s0)
        sc.w    a2, a1, (s0)
        CHECK(9, a2, 0)
        sc.w    a3, a1, (s0)
        CHECK(10, a3, 1)
        ld      a4, 0(s0)
        RESULT(a4)
        CHECK(11, a4, 0x0aaaaaaa12345678)
        /* 12-13 (control): LR.D A; SC.D A with rd == rs2 succeeds */
        li      a1, 0x1122334455667788
        lr.d    a0, (s0)
        sc.d    a1, a1, (s0)
        CHECK(12, a1, 0)
        ld      a4, 0(s0)
        CHECK(13, a4, 0x1122334455667788)

        /* ---- F4: 32-bit AMO min/max with rs2<63:32> not the sign extension of rs2<31:0> ---- */
        addi    s2, s0, 16
        /* 14-15: AMOMIN.W mem=0, rs2=0x0000000080000000 -> mem 0x80000000, rd 0 */
        sw      zero, 0(s2)
        li      t0, 0x80000000
        amomin.w a0, t0, (s2)
        CHECK(14, a0, 0)
        lwu     a4, 0(s2)
        CHECK(15, a4, 0x80000000)
        /* 16-17: AMOMINU.W mem=0x80000000, rs2=0x0000000090000000 -> mem 0x80000000 */
        li      t0, 0x80000000
        sw      t0, 0(s2)
        li      t0, 0x90000000
        amominu.w a0, t0, (s2)
        CHECK(16, a0, MIN32W)
        lwu     a4, 0(s2)
        CHECK(17, a4, 0x80000000)
        /* 18-19: AMOMAX.W mem=5, rs2=0x0000000100000000 -> mem 5 */
        li      t0, 5
        sw      t0, 0(s2)
        li      t0, 0x100000000
        amomax.w a0, t0, (s2)
        CHECK(18, a0, 5)
        lwu     a4, 0(s2)
        CHECK(19, a4, 5)
        /* 20-21: AMOMAXU.W mem=0x7fffffff, rs2=0xffffffff00000001 -> mem 0x7fffffff */
        li      t0, 0x7fffffff
        sw      t0, 0(s2)
        li      t0, 0xffffffff00000001
        amomaxu.w a0, t0, (s2)
        CHECK(20, a0, 0x7fffffff)
        lwu     a4, 0(s2)
        CHECK(21, a4, 0x7fffffff)
        /* 22-23: the upper word of the doubleword is untouched; rd == rs2 */
        li      t0, 0x5a5a5a5a00000009
        sd      t0, 0(s2)
        li      t1, 0xffffffff00000007
        amominu.w t1, t1, (s2)
        CHECK(22, t1, 9)
        ld      a4, 0(s2)
        RESULT(a4)
        CHECK(23, a4, 0x5a5a5a5a00000007)
        /* 24 (control): AMOADD.W with a non-sign-extended rs2 */
        li      t0, 0x11111111ffffffff
        sd      t0, 0(s2)
        li      t1, 0x7777777700000001
        amoadd.w a0, t1, (s2)
        ld      a4, 0(s2)
        CHECK(24, a4, 0x1111111100000000)

        /* ---- F15: C.ADDIW (rd != x0) ---- */
        li      a0, 0x7fffffff
        c.addiw a0, 1
        CHECK(25, a0, MIN32W)
        li      a0, 0x1ffffffff
        c.addiw a0, 0               /* sext.w */
        CHECK(26, a0, -1)
        li      s1, 0x80000000
        c.addiw s1, -1
        CHECK(27, s1, 0x7fffffff)
        li      a5, 0x123456789
        c.addiw a5, 31
        RESULT(a5)
        CHECK(28, a5, 0x234567a8)

        /* ---- F20: M extension with rd aliasing a source, x/0 and MIN/-1 ---- */
        /* 29: DIV rd==rs2, result 0 (crashed the SML export) */
        li      a0, 4
        li      a1, 7
        div     a1, a0, a1
        CHECK(29, a1, 0)
        /* 30: DIV rd==rs2, 14/7 */
        li      a0, 14
        li      a1, 7
        div     a1, a0, a1
        CHECK(30, a1, 2)
        /* 31-33: REM and REMU rd==rs2 with result 0 */
        li      a0, 4
        li      a1, 2
        rem     a1, a0, a1
        CHECK(31, a1, 0)
        li      a1, 2
        remu    a1, a0, a1
        CHECK(32, a1, 0)
        li      t5, 5
        remu    t5, t5, t5
        CHECK(33, t5, 0)
        /* 34-35: REM rd==rs1==rs2 */
        li      t4, 1
        rem     t4, t4, t4
        CHECK(34, t4, 0)
        li      t4, -9
        rem     t4, t4, t4
        CHECK(35, t4, 0)
        /* 36-41: division by zero, rd == rs2 and rd == rs1 */
        li      a0, 1234
        li      a1, 0
        div     a1, a0, a1
        CHECK(36, a1, -1)
        li      a1, 0
        divu    a1, a0, a1
        CHECK(37, a1, -1)
        li      a1, 0
        rem     a1, a0, a1
        CHECK(38, a1, 1234)
        li      a1, 0
        remu    a1, a0, a1
        CHECK(39, a1, 1234)
        li      a1, 0
        rem     a0, a0, a1
        CHECK(40, a0, 1234)
        li      a2, 0
        remu    a2, a2, a2
        CHECK(41, a2, 0)
        /* 42-45: MIN/-1 */
        li      a0, MIN64
        li      a1, -1
        div     a2, a0, a1
        CHECK(42, a2, MIN64)
        rem     a2, a0, a1
        CHECK(43, a2, 0)
        div     a1, a0, a1
        CHECK(44, a1, MIN64)
        li      a1, -1
        rem     a0, a0, a1
        CHECK(45, a0, 0)
        /* 46-51: W forms: MIN32/-1, x/0, operands with junk upper halves */
        li      a0, 0x1234567880000000
        li      a1, 0xffffffffffffffff
        divw    a2, a0, a1
        CHECK(46, a2, MIN32W)
        remw    a2, a0, a1
        CHECK(47, a2, 0)
        li      a1, 0x100000000
        divw    a1, a0, a1
        CHECK(48, a1, -1)
        li      a1, 0x100000000
        remw    a1, a0, a1
        CHECK(49, a1, MIN32W)
        li      a1, 0x7700000000
        divuw   a1, a0, a1
        CHECK(50, a1, -1)
        li      a1, 0x7700000003
        remuw   a1, a0, a1
        CHECK(51, a1, 2)
        /* 52-53: MUL with rd aliasing (wrong Delta.data1 before F20; result was right) */
        li      a0, 3
        li      a1, 5
        mul     a0, a0, a1
        CHECK(52, a0, 15)
        li      a1, -7
        mulh    a1, a1, a1
        CHECK(53, a1, 0)
        RESULT(a0)

        j       pass

        TEST_END

        SIGNATURE(8)

        .data
        .align  4
data:   .dword  0x0aaaaaaa0aaaaaaa
        .dword  0x0bbbbbbb0bbbbbbb
        .dword  0
        .dword  0
