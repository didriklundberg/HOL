/* Smoke test (a): RV64IM integer arithmetic, loads and stores over a small
   array, a call and return.  Assembled without C. */
#include "test.h"

        TEST_START

        la      s0, data

        /* 1: sum of the 8 dwords (ld, add, blt loop) */
        li      t0, 0
        li      a0, 0
        li      t1, 8
1:      slli    t2, t0, 3
        add     t2, s0, t2
        ld      t3, 0(t2)
        add     a0, a0, t3
        addi    t0, t0, 1
        blt     t0, t1, 1b
        RESULT(a0)
        CHECK(1, a0, 0x123456799abce024)

        /* 2-7: sign- and zero-extending loads of data[2] */
        lb      a0, 16(s0)
        CHECK(2, a0, 0xfffffffffffffff0)
        lbu     a0, 16(s0)
        CHECK(3, a0, 0xf0)
        lh      a0, 16(s0)
        CHECK(4, a0, 0xffffffffffffdef0)
        lhu     a0, 16(s0)
        CHECK(5, a0, 0xdef0)
        lw      a0, 16(s0)
        CHECK(6, a0, 0xffffffff9abcdef0)
        lwu     a0, 16(s0)
        RESULT(a0)
        CHECK(7, a0, 0x9abcdef0)

        /* 8: sb/sh/sw/sd into scratch, read back as one dword */
        la      s1, scratch
        li      a1, -1
        sd      a1, 0(s1)
        li      a1, 0x11
        sb      a1, 0(s1)
        li      a1, 0x3322
        sh      a1, 2(s1)
        li      a1, 0x77665544
        sw      a1, 4(s1)
        ld      a0, 0(s1)
        RESULT(a0)
        CHECK(8, a0, 0x776655443322ff11)
        /* byte 1 was not written and keeps 0xff */
        li      TESTNUM, 9
        lbu     a0, 1(s1)
        li      t6, 0xff
        bne     a0, t6, fail

        /* 10-15: M extension */
        ld      a1, 16(s0)
        li      a2, 3
        mul     a0, a1, a2
        RESULT(a0)
        CHECK(10, a0, 0x369d0369d0369cd0)
        ld      a2, 24(s0)
        mulhu   a0, a1, a2
        CHECK(11, a0, 0x12345678)
        li      a1, -7
        li      a2, 2
        div     a0, a1, a2
        CHECK(12, a0, -3)
        rem     a0, a1, a2
        CHECK(13, a0, -1)
        divu    a0, a1, zero
        CHECK(14, a0, -1)
        rem     a0, a1, zero
        RESULT(a0)
        CHECK(15, a0, -7)

        /* 16-19: shifts and 32-bit operations */
        ld      a1, 32(s0)
        srai    a0, a1, 4
        CHECK(16, a0, 0xf800000000000000)
        srli    a0, a1, 4
        CHECK(17, a0, 0x0800000000000000)
        li      a1, 0x7fffffff
        addiw   a0, a1, 1
        CHECK(18, a0, 0xffffffff80000000)
        srliw   a0, a0, 4
        RESULT(a0)
        CHECK(19, a0, 0x08000000)

        /* 20-21: compares */
        li      a1, -1
        li      a2, 1
        slt     a0, a1, a2
        CHECK(20, a0, 1)
        sltu    a0, a1, a2
        CHECK(21, a0, 0)

        /* 22: call and return */
        li      a0, 40
        jal     ra, add2
        RESULT(a0)
        CHECK(22, a0, 42)

        j       pass

add2:   addi    a0, a0, 2
        ret

        TEST_END

        .data
        .align  3
data:   .dword  0x0000000000000001, 0xfffffffffffffffe
        .dword  0x123456789abcdef0, 0x00000000ffffffff
        .dword  0x8000000000000000, 0x7fffffffffffffff
        .dword  0x0000000000000100, 0x0000000000000037
scratch:
        .dword  0

        SIGNATURE(7)
