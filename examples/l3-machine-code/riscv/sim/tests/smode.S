/* S-mode execution (doc/design-smode.md §2): MRET and SRET
   into S-mode and U-mode, ECALL from S-mode taken in M-mode and, delegated,
   in S-mode, medeleg and mideleg, sie and sip through mideleg, SSIP set by
   M-mode and taken in S-mode with stvec Direct and Vectored, SRET under
   TSR, WFI under TW, counter enables from S-mode and U-mode, scause WLRL,
   stval of an illegal instruction in S-mode, and satp and SFENCE.VMA under
   TVM.  Self-checking in the style of the other tests (test.h); build with
   -march=rv64im_zicsr -mabi=lp64.

   Each case runs in M-mode, enters S-mode or U-mode with MRET or SRET and
   comes back through a trap.  mtvec is m_trap, which saves mcause, mepc,
   mtval and mstatus in a0-a3 and goes on in M-mode at the address in s10.
   stvec is s_trap (Direct) or s_vec (Vectored); s_trap saves scause, sepc,
   stval and sstatus in s2-s5 and returns to M-mode with an EBREAK, which
   no case delegates, so a0 is 3 after a trap into S-mode.  PMP entry 0
   gives S-mode and U-mode access to all memory.  MTIP is pending from the
   start (mtimecmp is 0), so mie.MTIE stays clear. */
#include "test.h"

/* mstatus fields (P §3.1.6 Figure 8 p.32) */
#define SIE     0x2
#define SPIE    0x20
#define SPP     0x100
#define MPP_U   0x0
#define MPP_S   0x800
#define MPP     0x1800
#define MPRV    0x20000
#define TVM     0x100000
#define TW      0x200000
#define TSR     0x400000

/* mcause/scause of a supervisor software interrupt */
#define INTR_SSI 0x8000000000000001

/* write ms to mstatus and MRET to label to; the trap that ends the case
   continues in M-mode at label cont */
#define MRET_TO(ms, to, cont)            \
        li t0, ms; csrw mstatus, t0;     \
        la t0, to; csrw mepc, t0;        \
        la s10, cont;                    \
        mret

/* the same with SRET, from M-mode */
#define SRET_TO(ms, to, cont)            \
        li t0, ms; csrw mstatus, t0;     \
        la t0, to; csrw sepc, t0;        \
        la s10, cont;                    \
        sret

/* check number n: reg must equal the address of label l */
#define CHECK_ADDR(n, reg, l)  li TESTNUM, n; la t6, l; bne reg, t6, fail

/* check number n: reg && mask must equal val */
#define CHECK_BITS(n, reg, mask, val)    \
        li TESTNUM, n; li t6, mask; and t6, reg, t6; li t5, val; bne t6, t5, fail

        TEST_START
        la      t0, m_trap
        csrw    mtvec, t0
        la      t0, s_trap
        csrw    stvec, t0
        /* PMP entry 0: NAPOT over 2^56 bytes, RWX, as riscv-tests do */
        li      t0, (1 << 53) - 1
        csrw    pmpaddr0, t0
        li      t0, 0x1f
        csrw    pmpcfg0, t0

        /* ---- MRET into S-mode, ECALL from S-mode ---- */

        /* 1-4: MRET with MPP = S enters S-mode and clears MPRV (P §3.1.6.4
           p.35); with medeleg clear, the ECALL of S-mode goes to M-mode with
           cause 9, mepc at the ECALL, mtval 0 and MPP = S */
        MRET_TO(MPP_S | MPRV, a1_s, a1_m)
a1_s:   ecall
a1_m:   RESULT(a0)
        CHECK(1, a0, 9)
        CHECK_ADDR(2, a1, a1_s)
        CHECK(3, a2, 0)
        RESULT(a3)
        CHECK_BITS(4, a3, MPP | MPRV, MPP_S)

        /* 5-9: with medeleg[9] set it is taken in S-mode: scause 9, sepc at
           the ECALL, stval 0, SPP = S, SPIE = SIE, SIE = 0 (P §3.1.8 p.42,
           §12.1.1 p.113) */
        li      t0, 1 << 9
        csrw    medeleg, t0
        MRET_TO(MPP_S | SIE, a2_s, a2_m)
a2_s:   ecall
a2_m:   CHECK(5, a0, 3)
        RESULT(s2)
        CHECK(6, s2, 9)
        CHECK_ADDR(7, s3, a2_s)
        CHECK(8, s4, 0)
        RESULT(s5)
        CHECK_BITS(9, s5, SIE | SPIE | SPP, SPIE | SPP)
        csrw    medeleg, zero

        /* ---- medeleg, mideleg, sie, sip ---- */

        /* 10-11: the writable bits of medeleg (exceptions 0-9, 12, 13, 15)
           and of mideleg (SSI, STI, SEI) ([D40], [D41]) */
        li      t0, -1
        csrw    medeleg, t0
        csrr    a0, medeleg
        RESULT(a0)
        CHECK(10, a0, 0xb3ff)
        csrw    mideleg, t0
        csrr    a0, mideleg
        RESULT(a0)
        CHECK(11, a0, 0x222)
        csrw    medeleg, zero
        csrw    mideleg, zero

        /* 12-16: sie is mie restricted to mideleg (P §12.1.3 p.117) */
        li      t0, 2
        csrw    mie, t0
        csrr    a0, sie
        CHECK(12, a0, 0)
        li      t0, -1
        csrw    sie, t0
        csrr    a0, mie
        CHECK(13, a0, 2)
        li      t0, 0x222
        csrw    mideleg, t0
        csrr    a0, sie
        CHECK(14, a0, 2)
        li      t0, -1
        csrw    sie, t0
        csrr    a0, mie
        RESULT(a0)
        CHECK(15, a0, 0x222)
        csrw    sie, zero
        csrr    a0, mie
        CHECK(16, a0, 0)

        /* 17-21: sip is mip restricted to mideleg, and only its SSIP is
           writable (P §12.1.3 p.117-118) */
        csrw    mideleg, zero
        csrsi   mip, 2
        csrr    a0, sip
        CHECK(17, a0, 0)
        csrw    sip, zero
        csrr    a0, mip
        CHECK_BITS(18, a0, 0x222, 2)
        li      t0, 0x222
        csrw    mideleg, t0
        csrr    a0, sip
        RESULT(a0)
        CHECK(19, a0, 2)
        li      t0, 0x220
        csrs    sip, t0
        csrr    a0, sip
        CHECK(20, a0, 2)
        csrci   sip, 2
        csrr    a0, mip
        CHECK_BITS(21, a0, 0x222, 0)

        /* ---- Supervisor software interrupt ---- */

        /* 22-27: SSIP set by M-mode, delegated and enabled in sie, is taken
           in S-mode before its first instruction when SIE is set, at stvec
           in Direct mode (P §12.1.3 p.117, §12.1.2 p.116) */
        li      t0, 2
        csrw    mideleg, t0
        csrw    mie, t0
        csrsi   mip, 2
        li      s6, 0
        MRET_TO(MPP_S | SIE, b1_s, b1_m)
b1_s:   ecall
b1_m:   CHECK(22, a0, 3)
        RESULT(s2)
        CHECK(23, s2, INTR_SSI)
        CHECK_ADDR(24, s3, b1_s)
        CHECK(25, s4, 0)
        CHECK_BITS(26, s5, SIE | SPIE | SPP, SPIE | SPP)
        CHECK(27, s6, 0)

        /* 28-31: the same with stvec Vectored, where the interrupt goes to
           BASE + 4 * 1 (P §12.1.2 p.116-117) */
        la      t0, s_vec
        ori     t0, t0, 1
        csrw    stvec, t0
        li      s6, 0
        MRET_TO(MPP_S | SIE, b2_s, b2_m)
b2_s:   ecall
b2_m:   CHECK(28, a0, 3)
        CHECK(29, s2, INTR_SSI)
        CHECK_ADDR(30, s3, b2_s)
        RESULT(s6)
        CHECK(31, s6, 0x51)
        csrci   mip, 2

        /* 32-33: with stvec Vectored an exception still goes to BASE */
        li      t0, 1 << 9
        csrw    medeleg, t0
        li      s6, 0
        MRET_TO(MPP_S, b3_s, b3_m)
b3_s:   ecall
b3_m:   CHECK(32, s2, 9)
        CHECK(33, s6, 0x50)
        csrw    medeleg, zero
        la      t0, s_trap
        csrw    stvec, t0

        /* 34-36: an SSI that is not delegated goes to M-mode, and in S-mode
           it is taken although MIE is clear (P §3.1.6.1 p.32, §3.1.8 p.43) */
        csrw    mideleg, zero
        csrsi   mip, 2
        MRET_TO(MPP_S, b4_s, b4_m)
b4_s:   ecall
b4_m:   RESULT(a0)
        CHECK(34, a0, INTR_SSI)
        CHECK_ADDR(35, a1, b4_s)
        CHECK_BITS(36, a3, MPP, MPP_S)
        csrci   mip, 2

        /* 37-39: a delegated SSI is taken in U-mode although SIE is clear,
           into S-mode with SPP = U (P §3.1.6.1 p.32) */
        li      t0, 2
        csrw    mideleg, t0
        csrsi   mip, 2
        MRET_TO(MPP_U, b5_u, b5_m)
b5_u:   ecall
b5_m:   CHECK(37, a0, 3)
        CHECK(38, s2, INTR_SSI)
        CHECK_BITS(39, s5, SIE | SPIE | SPP, 0)
        csrci   mip, 2
        csrw    mie, zero
        csrw    mideleg, zero

        /* ---- SRET ---- */

        /* 40-42: SRET in M-mode is legal whatever TSR is (P §3.1.6.6 p.37).
           With SPP = U it enters U-mode and sets SIE = SPIE, SPIE = 1,
           SPP = U and MPRV = 0 (P §3.3.2 p.61, §3.1.6.1 p.32, §3.1.6.4
           p.35); the ECALL of U-mode (cause 8) goes to M-mode */
        SRET_TO(TSR | MPRV | SPIE, c1_u, c1_m)
c1_u:   ecall
c1_m:   RESULT(a0)
        CHECK(40, a0, 8)
        CHECK_ADDR(41, a1, c1_u)
        RESULT(a3)
        CHECK_BITS(42, a3, MPRV | SPP | SPIE | SIE | MPP, SIE | SPIE)

        /* 43-44: SRET in M-mode with SPP = S enters S-mode */
        SRET_TO(SPP, c2_s, c2_m)
c2_s:   ecall
c2_m:   CHECK(43, a0, 9)
        CHECK_ADDR(44, a1, c2_s)

        /* 45-47: SRET in S-mode with TSR set is an illegal instruction,
           with the instruction as mtval (P §3.1.6.6 p.37, [D43]) */
        MRET_TO(MPP_S | TSR, c3_s, c3_m)
c3_s:   sret
c3_m:   RESULT(a0)
        CHECK(45, a0, 2)
        CHECK_ADDR(46, a1, c3_s)
        CHECK(47, a2, 0x10200073)

        /* 48-50: SRET in S-mode with TSR clear and SPP = U enters U-mode,
           where SRET is an illegal instruction (P §3.3.2 p.61) */
        la      t0, c4_u
        csrw    sepc, t0
        MRET_TO(MPP_S, c4_s, c4_m)
c4_s:   sret
c4_u:   sret
c4_m:   CHECK(48, a0, 2)
        CHECK_ADDR(49, a1, c4_u)
        CHECK_BITS(50, a3, MPP, MPP_U)

        /* 51-52: SRET in S-mode with SPP = S stays in S-mode and goes to
           sepc */
        la      t0, c5_t
        csrw    sepc, t0
        MRET_TO(MPP_S | SPP, c5_s, c5_m)
c5_s:   sret
        ecall
c5_t:   ecall
c5_m:   CHECK(51, a0, 9)
        CHECK_ADDR(52, a1, c5_t)

        /* ---- WFI ---- */

        /* 53: WFI in M-mode is a no-op, TW or not (P §3.1.6.6 p.37, §3.3.3
           p.62) */
        li      t0, TW
        csrw    mstatus, t0
        li      s7, 0
        wfi
        li      s7, 1
        CHECK(53, s7, 1)
        csrw    mstatus, zero

        /* 54-56: WFI in S-mode with TW set, when no interrupt is pending and
           enabled in mie, is an illegal instruction: the time limit is zero
           (P §3.1.6.6 p.37, [S20]) */
        li      t0, 2
        csrw    mideleg, t0
        csrw    mie, t0
        MRET_TO(MPP_S | TW, d1_s, d1_m)
d1_s:   wfi
d1_m:   RESULT(a0)
        CHECK(54, a0, 2)
        CHECK_ADDR(55, a1, d1_s)
        CHECK(56, a2, 0x10500073)

        /* 57-58: with SSIP pending and enabled in sie, and SIE clear, the
           same WFI completes at once and retires: WFI ignores SIE and
           mideleg (P §3.3.3 p.62, [S20]) */
        csrsi   mip, 2
        MRET_TO(MPP_S | TW, d2_s, d2_m)
d2_s:   wfi
d2_e:   ecall
d2_m:   RESULT(a0)
        CHECK(57, a0, 9)
        CHECK_ADDR(58, a1, d2_e)

        /* 59-61: setting SIE after such a WFI takes the interrupt in S-mode
           before the next instruction (P §12.1.3 p.117) */
        MRET_TO(MPP_S | TW, d3_s, d3_m)
d3_s:   wfi
        csrsi   sstatus, SIE
d3_i:   ecall
d3_m:   CHECK(59, a0, 3)
        CHECK(60, s2, INTR_SSI)
        CHECK_ADDR(61, s3, d3_i)
        csrci   mip, 2
        csrw    mie, zero
        csrw    mideleg, zero

        /* 62-63: WFI in U-mode is an illegal instruction, TW clear (P
           §3.1.6.6 p.37, [D23]) */
        MRET_TO(MPP_U, d4_u, d4_m)
d4_u:   wfi
d4_m:   CHECK(62, a0, 2)
        CHECK(63, a2, 0x10500073)

        /* 64: WFI in S-mode with TW clear is a no-op */
        MRET_TO(MPP_S, d5_s, d5_m)
d5_s:   wfi
d5_e:   ecall
d5_m:   CHECK_ADDR(64, a1, d5_e)

        /* ---- Counter enables ---- */

        /* 65-66: the writable bits of mcounteren and scounteren: CY, TM, IR
           ([D27]) */
        li      t0, -1
        csrw    mcounteren, t0
        csrr    a0, mcounteren
        CHECK(65, a0, 7)
        csrw    scounteren, t0
        csrr    a0, scounteren
        CHECK(66, a0, 7)

        /* 67-68: S-mode reads cycle only with mcounteren.CY set, whatever
           scounteren is (P §3.1.11 p.47); mtval is the instruction */
        csrw    mcounteren, zero
        MRET_TO(MPP_S, e1_s, e1_m)
e1_s:   csrr    a4, cycle
e1_m:   RESULT(a0)
        CHECK(67, a0, 2)
        CHECK(68, a2, 0xc0002773)

        /* 69-71: with mcounteren = CY, S-mode reads cycle but not time */
        li      t0, 1
        csrw    mcounteren, t0
        li      s7, 0
        MRET_TO(MPP_S, e2_s, e2_m)
e2_s:   csrr    a4, cycle
        li      s7, 1
e2_t:   csrr    a4, time
e2_m:   CHECK(69, a0, 2)
        CHECK_ADDR(70, a1, e2_t)
        CHECK(71, s7, 1)

        /* 72-75: U-mode also needs the scounteren bit (P §12.1.5 p.119):
           with mcounteren = CY TM IR and scounteren = TM it reads time,
           but not cycle or instret */
        li      t0, 7
        csrw    mcounteren, t0
        li      t0, 2
        csrw    scounteren, t0
        li      s7, 0
        MRET_TO(MPP_U, e3_u, e3_m)
e3_u:   csrr    a4, time
        li      s7, 1
e3_c:   csrr    a4, cycle
e3_m:   CHECK(72, a0, 2)
        CHECK_ADDR(73, a1, e3_c)
        CHECK(74, s7, 1)
        MRET_TO(MPP_U, e4_u, e4_m)
e4_u:   csrr    a4, instret
e4_m:   CHECK(75, a0, 2)

        /* 76-78: and scounteren alone is not enough: with mcounteren =
           CY IR and scounteren = CY TM IR, U-mode reads cycle, not time */
        li      t0, 5
        csrw    mcounteren, t0
        li      t0, 7
        csrw    scounteren, t0
        li      s7, 0
        MRET_TO(MPP_U, e5_u, e5_m)
e5_u:   csrr    a4, cycle
        li      s7, 1
e5_t:   csrr    a4, time
e5_m:   CHECK(76, a0, 2)
        CHECK_ADDR(77, a1, e5_t)
        CHECK(78, s7, 1)
        csrw    mcounteren, zero
        csrw    scounteren, zero

        /* ---- scause, stval ---- */

        /* 79-84: scause holds any code from 0 to 31, interrupt or not, and
           above 31 what mcause can hold; a write of anything else leaves
           it unchanged (P §12.1.8 p.120, [D33]) */
        li      t0, 31
        csrw    scause, t0
        csrr    a0, scause
        CHECK(79, a0, 31)
        li      t0, 32
        csrw    scause, t0
        csrr    a0, scause
        CHECK(80, a0, 31)
        li      t0, 0x8000000000000005
        csrw    scause, t0
        csrr    a0, scause
        CHECK(81, a0, 0x8000000000000005)
        li      t0, 0x800000000000001f
        csrw    scause, t0
        csrr    a0, scause
        CHECK(82, a0, 0x800000000000001f)
        li      t0, 0x8000000000000040
        csrw    scause, t0
        csrr    a0, scause
        RESULT(a0)
        CHECK(83, a0, 0x800000000000001f)
        li      t0, 0x7fffffffffffffff
        csrw    scause, t0
        csrr    a0, scause
        CHECK(84, a0, 0x800000000000001f)

        /* 85: S-mode writes scause too */
        MRET_TO(MPP_S, f1_s, f1_m)
f1_s:   li      t0, 19
        csrw    scause, t0
        csrr    a5, scause
        ecall
f1_m:   CHECK(85, a5, 19)

        /* 86-89: an illegal instruction in S-mode, delegated, leaves the
           instruction in stval (P §12.1.9 p.121, [D43]) */
        li      t0, 1 << 2
        csrw    medeleg, t0
        csrw    stval, zero
        MRET_TO(MPP_S, f2_s, f2_m)
f2_s:   csrr    a4, mstatus
f2_m:   CHECK(86, a0, 3)
        RESULT(s2)
        CHECK(87, s2, 2)
        CHECK_ADDR(88, s3, f2_s)
        RESULT(s4)
        CHECK(89, s4, 0x30002773)
        csrw    medeleg, zero

        /* ---- TVM ---- */

        /* 90: TVM has no effect in M-mode (P §3.1.6.6 p.37) */
        li      t0, TVM
        csrw    mstatus, t0
        csrw    satp, zero
        csrr    a0, satp
        sfence.vma
        CHECK(90, a0, 0)
        csrw    mstatus, zero

        /* 91-93: in S-mode with TVM set, a satp read is an illegal
           instruction */
        MRET_TO(MPP_S | TVM, g1_s, g1_m)
g1_s:   csrr    a4, satp
g1_m:   RESULT(a0)
        CHECK(91, a0, 2)
        CHECK_ADDR(92, a1, g1_s)
        CHECK(93, a2, 0x18002773)

        /* 94: so is a satp write */
        MRET_TO(MPP_S | TVM, g2_s, g2_m)
g2_s:   csrw    satp, zero
g2_m:   CHECK(94, a0, 2)

        /* 95-96: and SFENCE.VMA (P §12.2.1 p.127) */
        MRET_TO(MPP_S | TVM, g3_s, g3_m)
g3_s:   sfence.vma
g3_m:   CHECK(95, a0, 2)
        CHECK(96, a2, 0x12000073)

        /* 97-99: with TVM clear, S-mode reads and writes satp (Bare) and
           runs SFENCE.VMA, which does nothing, also for an address that is
           not a valid virtual address (P §12.2.1 p.128, [S4]) */
        li      s7, 0
        MRET_TO(MPP_S, g4_s, g4_m)
g4_s:   csrw    satp, zero
        csrr    a5, satp
        sfence.vma
        li      t0, -1
        sfence.vma t0, t0
        li      s7, 1
        ecall
g4_m:   CHECK(97, a0, 9)
        CHECK(98, a5, 0)
        CHECK(99, s7, 1)

        /* 100: SFENCE.VMA in U-mode is an illegal instruction */
        MRET_TO(MPP_U, g5_u, g5_m)
g5_u:   sfence.vma
g5_m:   CHECK(100, a0, 2)

        TEST_END

        .text
/* M-mode trap handler: save the trap and go on in M-mode at s10 */
        .align  2
m_trap: csrr    a0, mcause
        csrr    a1, mepc
        csrr    a2, mtval
        csrr    a3, mstatus
        jr      s10

/* S-mode trap handler (stvec Direct): save the trap, return to M-mode */
        .align  2
s_trap: csrr    s2, scause
        csrr    s3, sepc
        csrr    s4, stval
        csrr    s5, sstatus
        ebreak

/* stvec Vectored: exceptions at BASE, interrupt i at BASE + 4i; each entry
   leaves a mark in s6 and goes on in s_trap */
        .align  6
s_vec:  j       s_vec_exc
        j       s_vec_ssi       /* 1 SSI */
        j       s_vec_bad
        j       s_vec_bad
        j       s_vec_bad
        j       s_vec_bad       /* 5 STI */
        j       s_vec_bad
        j       s_vec_bad
        j       s_vec_bad
        j       s_vec_bad       /* 9 SEI */
s_vec_exc:
        li      s6, 0x50
        j       s_trap
s_vec_ssi:
        li      s6, 0x51
        j       s_trap
s_vec_bad:
        li      s6, 0xbad
        j       s_trap

        SIGNATURE(24)
