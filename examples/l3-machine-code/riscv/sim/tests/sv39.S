/* Sv39 address translation (doc/design-smode.md §3): satp
   writes with reserved MODEs; mstatus.SUM; leaves of 4 KiB, 2 MiB and
   1 GiB; a sign-extended and two non-canonical virtual addresses; each
   page fault of the walk (invalid PTE, W without R, PTE bits 63-54, a
   pointer at level 0, a pointer with D, A or U, misaligned 2 MiB and
   1 GiB superpages, U and SUM, MXR, A and D under Svade); the PMP on a
   PTE read and on the final physical address; a 32-bit instruction whose
   upper half is on an unmapped page, and on a page mapped elsewhere;
   LR/SC through two virtual addresses of one physical address; MPRV with
   MPP = S and U; page faults delegated to S-mode, and under MPRV not;
   Bare in S-mode and satp written by S-mode.  Self-checking in the style
   of the other tests (test.h); build with -march=rv64ima_zicsr
   -mabi=lp64.

   The cases and the macros are described in vm.h.

   The page table, with root pt2 (VPN[2], 1 GiB per entry), pt1 (VPN[1]
   for VA 0 to 1 GiB, 2 MiB per entry) and pt0 (VPN[0] for VA 0 to 2 MiB,
   4 KiB per entry).  PA 0x80000000 is where the program is loaded.

     VA                  PTE                maps
     0xffffffffc0000000  pt2[511] RW        PA 0x80000000, 1 GiB
     0x0000000080000000  pt2[2]   RWX       PA 0x80000000, 1 GiB (S-mode code)
     0x00000000c0000000  pt2[3]   RWXU      PA 0x80000000, 1 GiB (U-mode code)
     0x0000000100000000  pt2[4]   RW        PA 0x80200000: misaligned
     0x0000000000200000  pt1[1]   RW        PA 0x80000000, 2 MiB
     0x0000000000400000  pt1[2]   RW        PA 0x80001000: misaligned
     0x0000000000600000  pt1[3]   pointer with A, to pt0
     0x0000000000800000  pt1[4]   pointer with U, to pt0
     0x0000000000a00000  pt1[5]   pointer with D, to pt0
     0x0000000000c00000  pt1[6]   pointer to pt0_deny, which the PMP denies
     0x0000000000001000  pt0[1]   invalid
     0x0000000000002000  pt0[2]   RW        data0
     0x0000000000003000  pt0[3]   R         data0
     0x0000000000004000  pt0[4]   X         data0
     0x0000000000005000  pt0[5]   RWU       data0
     0x0000000000006000  pt0[6]   RW, A = 0 data0
     0x0000000000007000  pt0[7]   RW, D = 0 data0
     0x0000000000008000  pt0[8]   W         data0 (reserved: W without R)
     0x0000000000009000  pt0[9]   RW        data0, with bit 54 set
     0x000000000000a000  pt0[10]  RW        data0, with bit 63 (N) set
     0x000000000000b000  pt0[11]  RW        data0, with bit 61 (PBMT) set
     0x000000000000c000  pt0[12]  X         strad_p
     0x000000000000d000  pt0[13]  X         set by the case
     0x000000000000e000  pt0[14]  RW        data0 (a second VA)
     0x000000000000f000  pt0[15]  RWX       deny_page, which the PMP denies
     0x0000000000010000  pt0[16]  pointer at level 0
     0x0000000000011000  pt0[17]  XU        data0

   Every leaf has A and D set unless the table says otherwise. */
#include "test.h"
#include "vm.h"

#define VA_INVALID  0x1000
#define VA_DATA     0x2000
#define VA_RO       0x3000
#define VA_XO       0x4000
#define VA_UDATA    0x5000
#define VA_NOA      0x6000
#define VA_NOD      0x7000
#define VA_WONLY    0x8000
#define VA_BIT54    0x9000
#define VA_N        0xa000
#define VA_PBMT     0xb000
#define VA_STRAD    0xc000
#define VA_STRAD2   0xd000
#define VA_ALIAS    0xe000
#define VA_DENY     0xf000
#define VA_PTR0     0x10000
#define VA_UXO      0x11000
#define VA_2M       0x200000
#define VA_2M_MIS   0x400000
#define VA_NL_A     0x600000
#define VA_NL_U     0x800000
#define VA_NL_D     0xa00000
#define VA_PTDENY   0xc00000
#define VA_1G_MIS   0x100000000
#define VA_HIGH     0xffffffffc0000000
/* bit 38 set, bits 63-39 clear; bits 63-39 set, bit 38 clear */
#define VA_NONCANON1 0x0000004000000000
#define VA_NONCANON2 0xffffff8000000000

#define DATA0       0x1122334455667788

        TEST_START
        VM_INIT

        /* PMP (P §3.7.1 p.70-73): entry 0 denies S-mode and U-mode the
           page pt0_deny, entry 1 the page deny_page (NAPOT 4 KiB, no
           permissions); entry 2 allows everything (NAPOT 2^56, RWX) */
        la      t0, pt0_deny
        srli    t0, t0, 2
        ori     t0, t0, 0x1ff
        csrw    pmpaddr0, t0
        la      t0, deny_page
        srli    t0, t0, 2
        ori     t0, t0, 0x1ff
        csrw    pmpaddr1, t0
        li      t0, (1 << 53) - 1
        csrw    pmpaddr2, t0
        li      t0, 0x1f1818
        csrw    pmpcfg0, t0

        la      t0, data0
        li      t1, DATA0
        sd      t1, 0(t0)

        /* ---- satp and SUM, translation off ---- */

        /* 1: satp resets to 0 */
        csrr    a0, satp
        CHECK(1, a0, 0)

        /* 2-4: a write with a reserved MODE (1, 11 = Sv64, 15) has no
           effect (P §12.1.11 p.125) */
        li      t0, 0x1000000000001234
        csrw    satp, t0
        csrr    a0, satp
        CHECK(2, a0, 0)
        li      t0, 0xb000000000001234
        csrw    satp, t0
        csrr    a0, satp
        CHECK(3, a0, 0)
        li      t0, 0xf000000000001234
        csrw    satp, t0
        csrr    a0, satp
        CHECK(4, a0, 0)

        /* 5: Bare with a nonzero ASID and PPN is stored as written
           ([S10]) */
        li      t0, 0x0ffff00000001234
        csrw    satp, t0
        csrr    a0, satp
        RESULT(a0)
        CHECK(5, a0, 0x0ffff00000001234)

        /* 6-8: Sv39, Sv48 and Sv57, with all 16 ASID bits and all 44 PPN
           bits writable ([S7], [S8], [S9]) */
        li      t0, 0x8fffffffffffffff
        csrw    satp, t0
        csrr    a0, satp
        RESULT(a0)
        CHECK(6, a0, 0x8fffffffffffffff)
        li      t0, 0x9000000000000001
        csrw    satp, t0
        csrr    a0, satp
        CHECK(7, a0, 0x9000000000000001)
        li      t0, 0xa000000000000002
        csrw    satp, t0
        csrr    a0, satp
        CHECK(8, a0, 0xa000000000000002)

        /* 9: a reserved MODE leaves that value */
        li      t0, 0xc000000000000003
        csrw    satp, t0
        csrr    a0, satp
        RESULT(a0)
        CHECK(9, a0, 0xa000000000000002)

        /* 10 */
        csrwi   satp, 0
        csrr    a0, satp
        CHECK(10, a0, 0)

        /* 11-12: mstatus.SUM is writable, also through sstatus (P §3.1.6.4
           p.35, §12.1.1.2 p.114, [S19]) */
        li      t0, SUM
        csrw    mstatus, t0
        csrr    a0, mstatus
        CHECK_BITS(11, a0, SUM, SUM)
        csrw    mstatus, zero
        csrs    sstatus, t0
        csrr    a0, mstatus
        RESULT(a0)
        CHECK_BITS(12, a0, SUM, SUM)
        csrw    mstatus, zero

        /* ---- the page table ---- */

        PTE_L(pt2, 0, pt1, V)
        PTE_PA(pt2, 2, 0x80000000, V|R|W|X|A|D)
        PTE_PA(pt2, 3, 0x80000000, V|R|W|X|U|A|D)
        PTE_PA(pt2, 4, 0x80200000, V|R|W|A|D)
        PTE_PA(pt2, 511, 0x80000000, V|R|W|A|D)

        PTE_L(pt1, 0, pt0, V)
        PTE_PA(pt1, 1, 0x80000000, V|R|W|A|D)
        PTE_PA(pt1, 2, 0x80001000, V|R|W|A|D)
        PTE_L(pt1, 3, pt0, V|A)
        PTE_L(pt1, 4, pt0, V|U)
        PTE_L(pt1, 5, pt0, V|D)
        PTE_L(pt1, 6, pt0_deny, V)

        PTE_L(pt0, 2, data0, V|R|W|A|D)
        PTE_L(pt0, 3, data0, V|R|A)
        PTE_L(pt0, 4, data0, V|X|A)
        PTE_L(pt0, 5, data0, V|R|W|U|A|D)
        PTE_L(pt0, 6, data0, V|R|W|D)
        PTE_L(pt0, 7, data0, V|R|W|A)
        PTE_L(pt0, 8, data0, V|W|A|D)
        la      t0, data0
        PTE_HI(pt0, 9, t0, V|R|W|A|D, 0x0040000000000000)
        PTE_HI(pt0, 10, t0, V|R|W|A|D, 0x8000000000000000)
        PTE_HI(pt0, 11, t0, V|R|W|A|D, 0x2000000000000000)
        PTE_L(pt0, 12, strad_p, V|X|A)
        PTE_L(pt0, 14, data0, V|R|W|A|D)
        PTE_L(pt0, 15, deny_page, V|R|W|X|A|D)
        PTE_L(pt0, 16, pt0, V)
        PTE_L(pt0, 17, data0, V|X|U|A)

        /* a valid leaf, in the page the PMP denies */
        PTE_L(pt0_deny, 0, data0, V|R|W|X|A|D)

        /* Sv39 with root pt2 */
        SET_SATP(SATP_SV39, pt2)
        FENCE

        /* ---- leaves of each size ---- */

        /* 13-14: S-mode runs from the 1 GiB leaf and loads through a
           4 KiB leaf */
        li      s0, VA_DATA
        li      a5, 0
        RUN_S(MPP_S, c13, ld a5, 0(s0))
        CHECK(13, a0, ECALL_S)
        RESULT(a5)
        CHECK(14, a5, DATA0)

        /* 15: through the 2 MiB leaf */
        la      s0, data0
        li      t0, 0x80000000 - VA_2M
        sub     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c15, ld a5, 0(s0))
        CHECK(15, a5, DATA0)

        /* 16-17: a store through the 2 MiB leaf */
        li      a6, 0x5555666677778888
        RUN_S(MPP_S, c16, sd a6, 16(s0))
        CHECK(16, a0, ECALL_S)
        la      t0, data0
        ld      a5, 16(t0)
        CHECK_REG(17, a5, a6)

        /* 18: through the 1 GiB leaf of a sign-extended VA (P §12.4.1
           p.136) */
        la      s0, data0
        li      t0, VA_HIGH - 0x80000000
        add     s0, s0, t0
        li      a5, 0
        RUN_S(MPP_S, c18, ld a5, 0(s0))
        CHECK(18, a5, DATA0)

        /* ---- non-canonical VAs: a page fault before any PTE read ---- */

        /* 19-24: load, store and fetch at a VA with bit 38 set and bits
           63-39 clear; the fetch also has mepc = the VA */
        li      s0, VA_NONCANON1
        RUN_S(MPP_S, c19, ld a5, 0(s0))
        RESULT(a0)
        RESULT(a2)
        TRAP_M(19, LOAD_PAGE, VA_NONCANON1)
        RUN_S(MPP_S, c20, sd zero, 0(s0))
        TRAP_M(20, STORE_PAGE, VA_NONCANON1)
        JUMP(MPP_S, VA_NONCANON1, c21)
        TRAP_M(21, FETCH_PAGE, VA_NONCANON1)
        CHECK(22, a1, VA_NONCANON1)
        li      s0, VA_NONCANON2
        RUN_S(MPP_S, c23, ld a5, 0(s0))
        TRAP_M(23, LOAD_PAGE, VA_NONCANON2)
        JUMP(MPP_U, VA_NONCANON2, c24)
        TRAP_M(24, FETCH_PAGE, VA_NONCANON2)

        /* ---- invalid PTE ---- */

        /* 25-27 */
        li      s0, VA_INVALID + 8
        RUN_S(MPP_S, c25, ld a5, 0(s0))
        TRAP_M(25, LOAD_PAGE, VA_INVALID + 8)
        RUN_S(MPP_S, c26, sw zero, 0(s0))
        TRAP_M(26, STORE_PAGE, VA_INVALID + 8)
        JUMP(MPP_S, VA_INVALID, c27)
        TRAP_M(27, FETCH_PAGE, VA_INVALID)

        /* ---- R, W, X and MXR (P §12.3.2 step 8 p.134) ---- */

        /* 28-33: a read-only page: loads and LR work; a store, an AMO and
           an SC fault with the store page fault, the SC also without a
           reservation and with one ([S18]) */
        li      s0, VA_RO
        li      a5, 0
        RUN_S(MPP_S, c28, ld a5, 0(s0))
        CHECK(28, a5, DATA0)
        RUN_S(MPP_S, c29, sd zero, 0(s0))
        TRAP_M(29, STORE_PAGE, VA_RO)
        RUN_S(MPP_S, c30, amoadd.d a5, zero, (s0))
        TRAP_M(30, STORE_PAGE, VA_RO)
        RUN_S(MPP_S, c31, sc.d a5, zero, (s0))
        TRAP_M(31, STORE_PAGE, VA_RO)
        li      a5, 0
        RUN_S(MPP_S, c32, lr.d a5, (s0); sc.d a4, zero, (s0))
        TRAP_M(32, STORE_PAGE, VA_RO)
        CHECK(33, a5, DATA0)

        /* 34-37: an execute-only page: a load faults unless MXR is set
           (P §3.1.6.4 p.35); an AMO is a store and faults as one ("AMOs
           never raise load page-fault exceptions", P §12.3.1 p.132) */
        li      s0, VA_XO
        RUN_S(MPP_S, c34, ld a5, 0(s0))
        TRAP_M(34, LOAD_PAGE, VA_XO)
        li      a5, 0
        RUN_S(MPP_S | MXR, c35, ld a5, 0(s0))
        CHECK(35, a5, DATA0)
        RUN_S(MPP_S | MXR, c36, amoor.d a5, zero, (s0))
        TRAP_M(36, STORE_PAGE, VA_XO)
        RUN_S(MPP_S, c37, sd zero, 0(s0))
        TRAP_M(37, STORE_PAGE, VA_XO)

        /* 38-39: W without R is reserved (P §12.3.2 step 3) */
        li      s0, VA_WONLY
        RUN_S(MPP_S, c38, ld a5, 0(s0))
        TRAP_M(38, LOAD_PAGE, VA_WONLY)
        RUN_S(MPP_S, c39, sd zero, 0(s0))
        TRAP_M(39, STORE_PAGE, VA_WONLY)

        /* ---- U and SUM (P §12.3.1 p.132, §3.1.6.4 p.35) ---- */

        /* 40-44: S-mode on a page with U = 1: loads and stores need SUM;
           a store with SUM writes the page */
        li      s0, VA_UDATA
        RUN_S(MPP_S, c40, ld a5, 0(s0))
        TRAP_M(40, LOAD_PAGE, VA_UDATA)
        RUN_S(MPP_S, c41, sd zero, 8(s0))
        TRAP_M(41, STORE_PAGE, VA_UDATA + 8)
        li      a5, 0
        RUN_S(MPP_S | SUM, c42, ld a5, 0(s0))
        CHECK(42, a5, DATA0)
        li      a6, 0x0123456789abcdef
        RUN_S(MPP_S | SUM, c43, sd a6, 8(s0))
        CHECK(43, a0, ECALL_S)
        la      t0, data0
        ld      a5, 8(t0)
        CHECK_REG(44, a5, a6)

        /* 45-46: S-mode never executes from a page with U = 1, whatever
           SUM is: MRET to the U-mode alias of c45_x */
        la      s1, c45_x
        li      t0, UALIAS
        add     s1, s1, t0
        JUMP_REG(MPP_S | SUM, s1, c45)
        CHECK(45, a0, FETCH_PAGE)
        CHECK_REG(46, a2, s1)

        /* 47: SUM set by S-mode through sstatus works at once (P §12.2.1
           p.129) */
        li      a6, SUM
        li      a5, 0
        RUN_S(MPP_S, c47, csrs sstatus, a6; ld a5, 0(s0))
        CHECK(47, a5, DATA0)

        /* 48-51: U-mode runs from the alias with U = 1, loads and stores on
           a page with U = 1, and faults on a page with U = 0 */
        li      a5, 0
        RUN_U(MPP_U, c48, ld a5, 0(s0); sd a5, 24(s0))
        CHECK(48, a0, ECALL_U)
        CHECK(49, a5, DATA0)
        li      s0, VA_DATA
        RUN_U(MPP_U | SUM, c50, ld a5, 0(s0))
        TRAP_M(50, LOAD_PAGE, VA_DATA)
        RUN_U(MPP_U, c51, sd zero, 0(s0))
        TRAP_M(51, STORE_PAGE, VA_DATA)

        /* 52-53: U-mode does not execute from a page with U = 0 */
        la      s1, c45_x
        JUMP_REG(MPP_U, s1, c52)
        CHECK(52, a0, FETCH_PAGE)
        CHECK_REG(53, a2, s1)

        /* 54-55: MXR in U-mode, on an execute-only page with U = 1 */
        li      s0, VA_UXO
        RUN_U(MPP_U, c54, ld a5, 0(s0))
        TRAP_M(54, LOAD_PAGE, VA_UXO)
        li      a5, 0
        RUN_U(MPP_U | MXR, c55, ld a5, 0(s0))
        CHECK(55, a5, DATA0)

        /* ---- A and D under Svade (P §12.3.2 step 9, [S3]) ---- */

        /* 56-57: A = 0 */
        li      s0, VA_NOA
        RUN_S(MPP_S, c56, ld a5, 0(s0))
        TRAP_M(56, LOAD_PAGE, VA_NOA)
        RUN_S(MPP_S, c57, sd zero, 0(s0))
        TRAP_M(57, STORE_PAGE, VA_NOA)

        /* 58-60: D = 0: loads work, stores and AMOs fault */
        li      s0, VA_NOD
        li      a5, 0
        RUN_S(MPP_S, c58, ld a5, 0(s0))
        CHECK(58, a5, DATA0)
        RUN_S(MPP_S, c59, sd zero, 0(s0))
        TRAP_M(59, STORE_PAGE, VA_NOD)
        RUN_S(MPP_S, c60, amoswap.d a5, zero, (s0))
        TRAP_M(60, STORE_PAGE, VA_NOD)

        /* ---- reserved PTE bits and encodings (P §12.3.2 steps 3-5,
           §12.3.1 p.133, §12.4.1 p.137, [S12]) ---- */

        /* 61-63: bit 54, N (bit 63) and PBMT (bit 61) */
        li      s0, VA_BIT54
        RUN_S(MPP_S, c61, ld a5, 0(s0))
        TRAP_M(61, LOAD_PAGE, VA_BIT54)
        li      s0, VA_N
        RUN_S(MPP_S, c62, ld a5, 0(s0))
        TRAP_M(62, LOAD_PAGE, VA_N)
        li      s0, VA_PBMT
        RUN_S(MPP_S, c63, sd zero, 0(s0))
        TRAP_M(63, STORE_PAGE, VA_PBMT)

        /* 64: a pointer at level 0 */
        li      s0, VA_PTR0
        RUN_S(MPP_S, c64, ld a5, 0(s0))
        TRAP_M(64, LOAD_PAGE, VA_PTR0)

        /* 65-66: misaligned 2 MiB and 1 GiB superpages */
        li      s0, VA_2M_MIS
        RUN_S(MPP_S, c65, ld a5, 0(s0))
        TRAP_M(65, LOAD_PAGE, VA_2M_MIS)
        li      s0, VA_1G_MIS
        RUN_S(MPP_S, c66, ld a5, 0(s0))
        TRAP_M(66, LOAD_PAGE, VA_1G_MIS)

        /* 67-69: pointers with A, U and D set */
        li      s0, VA_NL_A + VA_DATA
        RUN_S(MPP_S, c67, ld a5, 0(s0))
        TRAP_M(67, LOAD_PAGE, VA_NL_A + VA_DATA)
        li      s0, VA_NL_U + VA_DATA
        RUN_S(MPP_S, c68, ld a5, 0(s0))
        TRAP_M(68, LOAD_PAGE, VA_NL_U + VA_DATA)
        li      s0, VA_NL_D + VA_DATA
        JUMP_REG(MPP_S, s0, c69)
        TRAP_M(69, FETCH_PAGE, VA_NL_D + VA_DATA)

        /* ---- the PMP (P §3.7.2 p.74, [S14]) ---- */

        /* 70-73: the PMP denies S-mode the PTE: the access fault of the
           access, with the VA as trap value (P §3.1.16 p.52) */
        li      s0, VA_PTDENY + 0x10
        RUN_S(MPP_S, c70, ld a5, 0(s0))
        RESULT(a0)
        TRAP_M(70, LOAD_ACCESS, VA_PTDENY + 0x10)
        RUN_S(MPP_S, c71, sd zero, 0(s0))
        TRAP_M(71, STORE_ACCESS, VA_PTDENY + 0x10)
        JUMP(MPP_S, VA_PTDENY, c72)
        TRAP_M(72, FETCH_ACCESS, VA_PTDENY)
        CHECK(73, a1, VA_PTDENY)

        /* 74-76: the PMP denies the physical address of the page */
        li      s0, VA_DENY + 0x20
        RUN_S(MPP_S, c74, ld a5, 0(s0))
        RESULT(a0)
        TRAP_M(74, LOAD_ACCESS, VA_DENY + 0x20)
        RUN_S(MPP_S, c75, sd zero, 0(s0))
        TRAP_M(75, STORE_ACCESS, VA_DENY + 0x20)
        JUMP(MPP_S, VA_DENY, c76)
        TRAP_M(76, FETCH_ACCESS, VA_DENY)

        /* ---- an instruction across a page boundary ([D59], [S16]) ---- */

        /* 77-79: the lower half of a 32-bit instruction is the last parcel
           of page 0xc000, and 0xd000 is unmapped: a fetch page fault with
           the address of the upper half as trap value and mepc at the
           instruction (P §3.1.16 p.52) */
        JUMP(MPP_S, VA_STRAD + 0xffe, c77)
        RESULT(a2)
        TRAP_M(77, FETCH_PAGE, VA_STRAD2)
        CHECK(78, a1, VA_STRAD + 0xffe)

        /* 79-81: 0xd000 mapped to strad_q: the upper half comes from there,
           which makes it addi a5, a5, 7, then ECALL at 0xd002 */
        PTE_L(pt0, 13, strad_q, V|X|A)
        FENCE
        li      a5, 0
        JUMP(MPP_S, VA_STRAD + 0xffe, c79)
        CHECK(79, a0, ECALL_S)
        CHECK(80, a1, VA_STRAD2 + 2)
        RESULT(a5)
        CHECK(81, a5, 7)

        /* 82: 0xd000 mapped to the next physical page: addi a5, a5, 1 */
        PTE_L(pt0, 13, strad_p1, V|X|A)
        FENCE
        li      a5, 0
        JUMP(MPP_S, VA_STRAD + 0xffe, c82)
        CHECK(82, a5, 1)

        /* ---- LR/SC: the reservation is of the physical address
           (P §12.3.1 p.133, [S17]) ---- */

        /* 83-84: LR through 0x2000, SC through 0xe000, both data0 */
        li      s0, VA_DATA + 32
        li      s1, VA_ALIAS + 32
        li      a6, 0x7777777700000000
        li      a4, 5
        RUN_S(MPP_S, c83, lr.d a5, (s0); sc.d a4, a6, (s1))
        RESULT(a4)
        CHECK(83, a4, 0)
        la      t0, data0
        ld      a5, 32(t0)
        CHECK_REG(84, a5, a6)

        /* ---- MPRV (P §3.1.6.4 p.35, §3.3) ---- */

        /* 85-86: MPP = S: loads are translated as in S-mode */
        li      s0, VA_DATA
        li      a5, 0
        RUN_MPRV(MPRV | MPP_S, c85, ld a5, 0(s0))
        CHECK(85, a0, 0)
        CHECK(86, a5, DATA0)

        /* 87-89: SUM applies with MPP = S */
        li      s0, VA_UDATA
        RUN_MPRV(MPRV | MPP_S, c87, ld a5, 0(s0))
        RESULT(a0)
        TRAP_M(87, LOAD_PAGE, VA_UDATA)
        li      a5, 0
        RUN_MPRV(MPRV | MPP_S | SUM, c88, ld a5, 0(s0))
        CHECK(88, a0, 0)
        CHECK(89, a5, DATA0)

        /* 90-92: MPP = U */
        li      a5, 0
        RUN_MPRV(MPRV | MPP_U, c90, ld a5, 0(s0))
        CHECK(90, a5, DATA0)
        li      s0, VA_DATA
        RUN_MPRV(MPRV | MPP_U, c91, ld a5, 0(s0))
        TRAP_M(91, LOAD_PAGE, VA_DATA)
        li      s0, VA_RO
        RUN_MPRV(MPRV | MPP_S, c92, sd zero, 0(s0))
        TRAP_M(92, STORE_PAGE, VA_RO)

        /* 93-94: MXR with MPP = S */
        li      s0, VA_XO
        li      a5, 0
        RUN_MPRV(MPRV | MPP_S | MXR, c93, ld a5, 0(s0))
        CHECK(93, a0, 0)
        CHECK(94, a5, DATA0)

        /* ---- delegation (P §3.1.8 p.42-43) ---- */

        li      t0, (1 << 12) | (1 << 13) | (1 << 15)
        csrw    medeleg, t0

        /* 95-98: a page fault in U-mode, delegated, is taken in S-mode
           with stval = the VA and sepc = the U-mode VA of the load */
        li      s0, VA_DATA + 8
        RUN_U(MPP_U, c95, ld a5, 0(s0))
        CHECK(95, a0, 3)
        RESULT(s2)
        CHECK(96, s2, LOAD_PAGE)
        CHECK(97, s4, VA_DATA + 8)
        la      t0, c95_u
        li      t1, UALIAS
        add     t0, t0, t1
        CHECK_REG(98, s3, t0)

        /* 99-100: and in S-mode, delegated, too */
        li      s0, VA_INVALID
        RUN_S(MPP_S, c99, sd zero, 0(s0))
        CHECK(99, a0, 3)
        CHECK(100, s2, STORE_PAGE)

        /* 101-103: a fetch page fault of U-mode */
        JUMP(MPP_U, VA_INVALID, c101)
        CHECK(101, a0, 3)
        CHECK(102, s2, FETCH_PAGE)
        CHECK(103, s3, VA_INVALID)

        /* 104: under MPRV the fault is M-mode's, never delegated
           (P §3.1.8 p.42) */
        RUN_MPRV(MPRV | MPP_S, c104, ld a5, 0(s0))
        TRAP_M(104, LOAD_PAGE, VA_INVALID)

        csrw    medeleg, zero

        /* ---- Bare in S-mode, and satp written by S-mode ---- */

        /* 105: Bare: S-mode addresses are physical */
        csrw    satp, zero
        FENCE
        la      s0, data0
        li      a5, 0
        RUN_S(MPP_S, c105, ld a5, 0(s0))
        CHECK(105, a5, DATA0)

        /* 106-107: S-mode writes satp (TVM = 0, P §3.1.6.6 p.37) and the
           next access is translated (P §12.2.1 p.129) */
        la      s1, pt2
        srli    s1, s1, 12
        li      t0, SATP_SV39
        or      s1, s1, t0
        li      s0, VA_DATA
        li      a5, 0
        RUN_S(MPP_S, c106, csrw satp, s1; sfence.vma zero, zero; ld a5, 0(s0))
        CHECK(106, a0, ECALL_S)
        CHECK(107, a5, DATA0)

        csrwi   satp, 0
        TEST_END

        VM_HANDLERS

/* only fetched in cases 45 and 52, which fault */
c45_x:  ecall

        .data
        .align  12
pt2:    .zero   4096
pt1:    .zero   4096
pt0:    .zero   4096
pt0_deny:
        .zero   4096
data0:  .zero   4096
deny_page:
        .zero   4096
/* the lower half of addi a5, a5, 1 at page offset 0xffe, its upper half
   and an ECALL in the next page */
strad_p:
        .zero   4094
        .half   0x8793
strad_p1:
        .half   0x0017
        .half   0x0073, 0x0000
        .zero   4090
/* the upper half of addi a5, a5, 7 and an ECALL */
strad_q:
        .half   0x0077
        .half   0x0073, 0x0000
        .zero   4090

        SIGNATURE(16)
