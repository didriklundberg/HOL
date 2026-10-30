/* Smoke test (b): compressed instructions (RV64C).  Written with explicit
   c.* mnemonics, assembled for rv64imac; the 32-bit instructions come from
   the macros (la, li of large constants, bne).  Fails under --no-c. */
#include "test.h"

        TEST_START

        la      sp, stack_top
        la      s0, data            /* s0 = x8, usable by c.ld/c.sd */

        /* 1: c.li, c.addi, c.add, c.mv, c.sub */
        c.li    a0, 5
        c.addi  a0, 7               /* 12 */
        c.li    a1, -3
        c.add   a0, a1              /* 9 */
        c.mv    a2, a0
        c.sub   a2, a1              /* 12 */
        RESULT(a2)
        CHECK(1, a2, 12)

        /* 2-3: c.ld/c.sd and c.lw/c.sw on x8..x15 */
        c.ld    a3, 0(s0)
        c.addi  a3, 1
        c.sd    a3, 8(s0)
        c.ld    a4, 8(s0)
        RESULT(a4)
        CHECK(2, a4, 0x123456789abcdef1)
        c.lw    a5, 4(s0)           /* sign-extended upper word of data[0] */
        RESULT(a5)
        CHECK(3, a5, 0x12345678)

        /* 4: stack-pointer forms c.addi16sp, c.addi4spn, c.sdsp/c.ldsp,
              c.swsp/c.lwsp */
        c.addi16sp sp, -32
        c.addi4spn a0, sp, 16
        c.sdsp  a4, 0(sp)
        c.swsp  a5, 8(sp)
        c.ldsp  a1, 0(sp)
        c.lwsp  a2, 8(sp)
        c.addi16sp sp, 32
        c.add   a1, a2              /* 0x123456789abcdef1 + 0x12345678 */
        RESULT(a1)
        CHECK(4, a1, 0x12345678acf13569)

        /* 5: c.slli, c.srli, c.srai, c.andi */
        c.li    a0, -1
        c.slli  a0, 60
        c.srai  a0, 4               /* 0xff00000000000000 */
        c.srli  a0, 56              /* 0xff */
        c.andi  a0, 0x1f            /* 0x1f */
        RESULT(a0)
        CHECK(5, a0, 0x1f)

        /* 6: c.and, c.or, c.xor, c.addw, c.subw, c.addiw */
        c.li    a0, 0x1c
        c.li    a1, 0x0a
        c.mv    a2, a0
        c.and   a2, a1              /* 0x08 */
        c.or    a2, a1              /* 0x0a */
        c.xor   a2, a0              /* 0x16 */
        lui     a3, 0x80000         /* 0xffffffff80000000 */
        c.addiw a3, -1              /* 0x7fffffff */
        c.addw  a3, a2              /* 0x80000015 sign-extended */
        c.subw  a3, a1              /* 0x8000000b sign-extended */
        RESULT(a3)
        CHECK(6, a3, 0xffffffff8000000b)

        /* 7: c.beqz, c.bnez, c.j */
        c.li    a0, 0
        c.li    a1, 0
        c.beqz  a0, 1f
        c.li    a1, 1               /* skipped */
1:      c.bnez  a1, fail_7
        c.j     2f
        c.li    a1, 2               /* skipped */
2:      CHECK(7, a1, 0)

        /* 8: c.jalr and c.jr */
        c.li    a0, 1
        la      t0, triple
        c.jalr  t0
        RESULT(a0)
        CHECK(8, a0, 3)

        /* 9: c.lui, c.nop */
        c.lui   a0, 0x1f            /* 0x1f000 */
        c.nop
        CHECK(9, a0, 0x1f000)

        j       pass

fail_7: li      TESTNUM, 7
        j       fail

triple: c.mv    a1, a0
        c.add   a0, a1
        c.add   a0, a1
        c.jr    ra

        TEST_END

        .data
        .align  3
data:   .dword  0x123456789abcdef0
        .dword  0
        .align  4
stack:  .fill   64, 1, 0
stack_top:

        SIGNATURE(7)
