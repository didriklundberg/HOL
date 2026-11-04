/* Sv57 address translation (P §12.6 p.138-139; doc/design-smode.md §3):
   leaves of 4 KiB, 2 MiB, 1 GiB, 512 GiB and 256 TiB, a VA
   that is canonical for Sv57 but not for Sv48, a sign-extended VA,
   non-canonical VAs, misaligned 256 TiB and 512 GiB superpages, invalid
   PTEs at levels 4 and 3, U-mode code, and MPRV.  Self-checking in the
   style of the other tests (test.h); build with -march=rv64ima_zicsr
   -mabi=lp64.  The cases and the macros are described in vm.h.

   The page table, with root pt4 (VPN[4], 256 TiB per entry), pt3 (VPN[3]
   for VA 0 to 256 TiB), pt2 (VPN[2] for VA 0 to 512 GiB), pt1 (VPN[1] for
   VA 0 to 1 GiB) and pt0 (VPN[0] for VA 0 to 2 MiB).  PA 0x80000000 is
   where the program is loaded.

     VA                  PTE                maps
     0xff00000000000000  pt4[256] RW        PA 0, 256 TiB
     0x0001000000000000  pt4[1]   RW        PA 0, 256 TiB
     0x0002000000000000  pt4[2]   RW        PA 0x8000000000: misaligned
     0x00ff000000000000  pt4[255] invalid
     0x0000008000000000  pt3[1]   RW        PA 0, 512 GiB
     0x0000010000000000  pt3[2]   RW        PA 0x40000000: misaligned
     0x00007f8000000000  pt3[255] invalid
     0x0000000080000000  pt2[2]   RWX       PA 0x80000000, 1 GiB (S-mode code)
     0x00000000c0000000  pt2[3]   RWXU      PA 0x80000000, 1 GiB (U-mode code)
     0x0000000000200000  pt1[1]   RW        PA 0x80000000, 2 MiB
     0x0000000000002000  pt0[2]   RW        data0

   Every leaf has A and D set. */
#include "test.h"
#include "vm.h"

#define VA_DATA     0x2000
#define VA_2M       0x200000
#define VA_512G     0x0000008000000000
#define VA_512G_MIS 0x0000010000000000
#define VA_L3_INV   0x00007f8000000000
#define VA_256T     0x0001000000000000
#define VA_256T_MIS 0x0002000000000000
#define VA_L4_INV   0x00ff000000000000
#define VA_HIGH     0xff00000000000000
/* bit 56 set, bits 63-57 clear; bits 63-57 set, bit 56 clear */
#define VA_NONCANON1 0x0100000000000000
#define VA_NONCANON2 0xfeffffffffffe000

#define DATA0       0x33445566778899aa

        TEST_START
        VM_INIT

        /* PMP entry 0: NAPOT 2^56, RWX */
        li      t0, (1 << 53) - 1
        csrw    pmpaddr0, t0
        li      t0, 0x1f
        csrw    pmpcfg0, t0

        la      t0, data0
        li      t1, DATA0
        sd      t1, 0(t0)

        PTE_L(pt4, 0, pt3, V)
        PTE_PA(pt4, 1, 0, V|R|W|A|D)
        PTE_PA(pt4, 2, 0x8000000000, V|R|W|A|D)
        PTE_PA(pt4, 256, 0, V|R|W|A|D)
        PTE_L(pt3, 0, pt2, V)
        PTE_PA(pt3, 1, 0, V|R|W|A|D)
        PTE_PA(pt3, 2, 0x40000000, V|R|W|A|D)
        PTE_L(pt2, 0, pt1, V)
        PTE_PA(pt2, 2, 0x80000000, V|R|W|X|A|D)
        PTE_PA(pt2, 3, 0x80000000, V|R|W|X|U|A|D)
        PTE_L(pt1, 0, pt0, V)
        PTE_PA(pt1, 1, 0x80000000, V|R|W|A|D)
        PTE_L(pt0, 2, data0, V|R|W|A|D)

        /* 1: satp holds Sv57 */
        SET_SATP(SATP_SV57, pt4)
        FENCE
        csrr    a0, satp
        RESULT(a0)
        la      t0, pt4
        srli    t0, t0, 12
        li      t1, SATP_SV57
        or      t0, t0, t1
        CHECK_REG(1, a0, t0)

        /* ---- leaves of each size ---- */

        /* 2-3: S-mode runs from the 1 GiB leaf and loads through a 4 KiB
           leaf */
        li      s0, VA_DATA
        li      a5, 0
        RUN_S(MPP_S, c2, ld a5, 0(s0))
        CHECK(2, a0, ECALL_S)
        RESULT(a5)
        CHECK(3, a5, DATA0)

        /* 4: through the 2 MiB leaf */
        la      s0, data0
        li      t0, 0x80000000 - VA_2M
        sub     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c4, ld a5, 0(s0))
        CHECK(4, a5, DATA0)

        /* 5: through the 1 GiB leaf */
        la      s0, data0
        li      a5, 0
        RUN_S(MPP_S, c5, ld a5, 0(s0))
        CHECK(5, a5, DATA0)

        /* 6: through the 512 GiB leaf */
        la      s0, data0
        li      t0, VA_512G
        add     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c6, ld a5, 0(s0))
        CHECK(6, a5, DATA0)

        /* 7-9: through the 256 TiB leaf, at a VA with bit 48 set, which is
           not canonical for Sv48 (P §12.6.1 p.138); a store too */
        la      s0, data0
        li      t0, VA_256T
        add     s0, s0, t0
        li      a5, 0
        li      a6, 0x1a1b1c1d1e1f1011
        RUN_S(MPP_S, c7, ld a5, 0(s0); sd a6, 8(s0))
        CHECK(7, a0, ECALL_S)
        CHECK(8, a5, DATA0)
        la      t0, data0
        ld      a5, 8(t0)
        CHECK_REG(9, a5, a6)

        /* 10: through the 256 TiB leaf of a sign-extended VA */
        la      s0, data0
        li      t0, VA_HIGH
        add     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c10, ld a5, 0(s0))
        CHECK(10, a5, DATA0)

        /* 11-12: U-mode runs from its 1 GiB leaf, five levels down */
        li      a5, 0
        RUN_U(MPP_U, c11, li a5, 0x57)
        CHECK(11, a0, ECALL_U)
        CHECK(12, a5, 0x57)

        /* 13-14: MPRV with MPP = S translates through the 256 TiB leaf */
        la      s0, data0
        li      t0, VA_256T
        add     s0, s0, t0
        li      a5, 0
        RUN_MPRV(MPRV | MPP_S, c13, ld a5, 0(s0))
        CHECK(13, a0, 0)
        CHECK(14, a5, DATA0)

        /* ---- non-canonical VAs (P §12.6.1 p.138) ---- */

        /* 15-19 */
        li      s0, VA_NONCANON1
        RUN_S(MPP_S, c15, ld a5, 0(s0))
        RESULT(a2)
        TRAP_M(15, LOAD_PAGE, VA_NONCANON1)
        RUN_S(MPP_S, c16, sd zero, 0(s0))
        TRAP_M(16, STORE_PAGE, VA_NONCANON1)
        JUMP(MPP_S, VA_NONCANON1, c17)
        TRAP_M(17, FETCH_PAGE, VA_NONCANON1)
        CHECK(18, a1, VA_NONCANON1)
        li      s0, VA_NONCANON2
        RUN_S(MPP_S, c19, ld a5, 0(s0))
        TRAP_M(19, LOAD_PAGE, VA_NONCANON2)

        /* ---- page faults at the upper levels ---- */

        /* 20-21: invalid PTEs at levels 4 and 3 */
        li      s0, VA_L4_INV
        RUN_S(MPP_S, c20, ld a5, 0(s0))
        TRAP_M(20, LOAD_PAGE, VA_L4_INV)
        li      s0, VA_L3_INV
        RUN_S(MPP_S, c21, ld a5, 0(s0))
        TRAP_M(21, LOAD_PAGE, VA_L3_INV)

        /* 22-23: misaligned 256 TiB and 512 GiB superpages (P §12.3.2
           step 5 p.134) */
        li      s0, VA_256T_MIS
        RUN_S(MPP_S, c22, ld a5, 0(s0))
        RESULT(a0)
        TRAP_M(22, LOAD_PAGE, VA_256T_MIS)
        li      s0, VA_512G_MIS
        RUN_S(MPP_S, c23, sd zero, 0(s0))
        TRAP_M(23, STORE_PAGE, VA_512G_MIS)

        csrwi   satp, 0
        TEST_END

        VM_HANDLERS

        .data
        .align  12
pt4:    .zero   4096
pt3:    .zero   4096
pt2:    .zero   4096
pt1:    .zero   4096
pt0:    .zero   4096
data0:  .zero   4096

        SIGNATURE(8)
