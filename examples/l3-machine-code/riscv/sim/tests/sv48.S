/* Sv48 address translation (P §12.5 p.137-138; doc/design-smode.md §3):
   leaves of 4 KiB, 2 MiB, 1 GiB and 512 GiB, a VA that is
   canonical for Sv48 but not for Sv39, a sign-extended VA, non-canonical
   VAs, misaligned 512 GiB, 1 GiB and 2 MiB superpages, invalid PTEs at
   levels 3 and 0, a pointer at level 0, U-mode code, and MPRV.
   Self-checking in the style of the other tests (test.h); build with
   -march=rv64ima_zicsr -mabi=lp64.  The cases and the macros are
   described in vm.h.

   The page table, with root pt3 (VPN[3], 512 GiB per entry), pt2 (VPN[2]
   for VA 0 to 512 GiB), pt1 (VPN[1] for VA 0 to 1 GiB) and pt0 (VPN[0]
   for VA 0 to 2 MiB).  PA 0x80000000 is where the program is loaded.

     VA                  PTE                maps
     0xffff800000000000  pt3[256] RW        PA 0, 512 GiB
     0x0000008000000000  pt3[1]   RW        PA 0, 512 GiB
     0x0000010000000000  pt3[2]   RW        PA 0x40000000: misaligned
     0x00007f8000000000  pt3[255] invalid
     0x0000000080000000  pt2[2]   RWX       PA 0x80000000, 1 GiB (S-mode code)
     0x00000000c0000000  pt2[3]   RWXU      PA 0x80000000, 1 GiB (U-mode code)
     0x0000000100000000  pt2[4]   RW        PA 0x80200000: misaligned
     0x0000000000200000  pt1[1]   RW        PA 0x80000000, 2 MiB
     0x0000000000400000  pt1[2]   RW        PA 0x80001000: misaligned
     0x0000000000001000  pt0[1]   invalid
     0x0000000000002000  pt0[2]   RW        data0
     0x0000000000003000  pt0[3]   pointer at level 0

   Every leaf has A and D set. */
#include "test.h"
#include "vm.h"

#define VA_INVALID  0x1000
#define VA_DATA     0x2000
#define VA_PTR0     0x3000
#define VA_2M       0x200000
#define VA_2M_MIS   0x400000
#define VA_1G_MIS   0x100000000
#define VA_512G     0x0000008000000000
#define VA_512G_MIS 0x0000010000000000
#define VA_L3_INV   0x00007f8000000000
#define VA_HIGH     0xffff800000000000
/* bit 47 set, bits 63-48 clear; bits 63-48 set, bit 47 clear */
#define VA_NONCANON1 0x0000800000000000
#define VA_NONCANON2 0xffff7ffffffff000

#define DATA0       0x2233445566778899

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

        PTE_L(pt3, 0, pt2, V)
        PTE_PA(pt3, 1, 0, V|R|W|A|D)
        PTE_PA(pt3, 2, 0x40000000, V|R|W|A|D)
        PTE_PA(pt3, 256, 0, V|R|W|A|D)
        PTE_L(pt2, 0, pt1, V)
        PTE_PA(pt2, 2, 0x80000000, V|R|W|X|A|D)
        PTE_PA(pt2, 3, 0x80000000, V|R|W|X|U|A|D)
        PTE_PA(pt2, 4, 0x80200000, V|R|W|A|D)
        PTE_L(pt1, 0, pt0, V)
        PTE_PA(pt1, 1, 0x80000000, V|R|W|A|D)
        PTE_PA(pt1, 2, 0x80001000, V|R|W|A|D)
        PTE_L(pt0, 2, data0, V|R|W|A|D)
        PTE_L(pt0, 3, pt0, V)

        /* 1: satp holds Sv48 */
        SET_SATP(SATP_SV48, pt3)
        FENCE
        csrr    a0, satp
        RESULT(a0)
        la      t0, pt3
        srli    t0, t0, 12
        li      t1, SATP_SV48
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

        /* 6-8: through the 512 GiB leaf, at a VA with bit 39 set, which is
           not canonical for Sv39 (P §12.5.1 p.137); a store too */
        la      s0, data0
        li      t0, VA_512G
        add     s0, s0, t0
        li      a5, 0
        li      a6, 0x0a0b0c0d0e0f0102
        RUN_S(MPP_S, c6, ld a5, 0(s0); sd a6, 8(s0))
        CHECK(6, a0, ECALL_S)
        CHECK(7, a5, DATA0)
        la      t0, data0
        ld      a5, 8(t0)
        CHECK_REG(8, a5, a6)

        /* 9: through the 512 GiB leaf of a sign-extended VA */
        la      s0, data0
        li      t0, VA_HIGH
        add     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c9, ld a5, 0(s0))
        CHECK(9, a5, DATA0)

        /* 10-11: U-mode runs from its 1 GiB leaf, four levels down */
        li      a5, 0
        RUN_U(MPP_U, c10, li a5, 0x55)
        CHECK(10, a0, ECALL_U)
        CHECK(11, a5, 0x55)

        /* 12-13: MPRV with MPP = S translates through the 512 GiB leaf */
        la      s0, data0
        li      t0, VA_512G
        add     s0, s0, t0
        li      a5, 0
        RUN_MPRV(MPRV | MPP_S, c12, ld a5, 0(s0))
        CHECK(12, a0, 0)
        CHECK(13, a5, DATA0)

        /* ---- non-canonical VAs (P §12.5.1 p.137) ---- */

        /* 14-18 */
        li      s0, VA_NONCANON1
        RUN_S(MPP_S, c14, ld a5, 0(s0))
        RESULT(a2)
        TRAP_M(14, LOAD_PAGE, VA_NONCANON1)
        RUN_S(MPP_S, c15, sd zero, 0(s0))
        TRAP_M(15, STORE_PAGE, VA_NONCANON1)
        JUMP(MPP_S, VA_NONCANON1, c16)
        TRAP_M(16, FETCH_PAGE, VA_NONCANON1)
        CHECK(17, a1, VA_NONCANON1)
        li      s0, VA_NONCANON2
        RUN_S(MPP_S, c18, ld a5, 0(s0))
        TRAP_M(18, LOAD_PAGE, VA_NONCANON2)

        /* ---- page faults at each level ---- */

        /* 19: an invalid PTE at level 3 */
        li      s0, VA_L3_INV
        RUN_S(MPP_S, c19, ld a5, 0(s0))
        TRAP_M(19, LOAD_PAGE, VA_L3_INV)

        /* 20-22: misaligned 512 GiB, 1 GiB and 2 MiB superpages
           (P §12.3.2 step 5 p.134) */
        li      s0, VA_512G_MIS
        RUN_S(MPP_S, c20, ld a5, 0(s0))
        RESULT(a0)
        TRAP_M(20, LOAD_PAGE, VA_512G_MIS)
        li      s0, VA_1G_MIS
        RUN_S(MPP_S, c21, sd zero, 0(s0))
        TRAP_M(21, STORE_PAGE, VA_1G_MIS)
        li      s0, VA_2M_MIS
        JUMP_REG(MPP_S, s0, c22)
        TRAP_M(22, FETCH_PAGE, VA_2M_MIS)

        /* 23-24: an invalid PTE and a pointer at level 0 */
        li      s0, VA_INVALID
        RUN_S(MPP_S, c23, ld a5, 0(s0))
        TRAP_M(23, LOAD_PAGE, VA_INVALID)
        li      s0, VA_PTR0
        RUN_S(MPP_S, c24, ld a5, 0(s0))
        TRAP_M(24, LOAD_PAGE, VA_PTR0)

        csrwi   satp, 0
        TEST_END

        VM_HANDLERS

        .data
        .align  12
pt3:    .zero   4096
pt2:    .zero   4096
pt1:    .zero   4096
pt0:    .zero   4096
data0:  .zero   4096

        SIGNATURE(8)
