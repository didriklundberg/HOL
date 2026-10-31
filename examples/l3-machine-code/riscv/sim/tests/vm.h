/* Shared definitions of the address-translation tests sv39.S, sv48.S and
   sv57.S (doc/design-smode.md §3), after test.h.

   Each case runs in M-mode, enters S-mode or U-mode with MRET and comes
   back through a trap, as in smode.S.  mtvec is m_trap, which saves
   mcause, mepc, mtval and mstatus in a0-a3 and goes on in M-mode at the
   address in s10.  A case that does not fault ends with an ECALL (a0 = 9
   from S-mode, 8 from U-mode).  stvec is s_trap, which saves scause,
   sepc, stval and sstatus in s2-s5 and returns to M-mode with an EBREAK
   (a0 = 3).  M-mode writes every PTE, and runs SFENCE.VMA after each
   change, which the model does not need but sail's TLB does.

   Every test maps VA 0x80000000 to PA 0x80000000, where the program is
   loaded, with a 1 GiB leaf (RWX) for S-mode, and VA 0xc0000000 to the same
   PA with U = 1 for U-mode (UALIAS).  The macros use t0-t3 and s10. */

/* PTE bits (P §12.4.1 Figure 70 p.136) */
#define V       0x01
#define R       0x02
#define W       0x04
#define X       0x08
#define U       0x10
#define A       0x40
#define D       0x80

/* mstatus fields (P §3.1.6 Figure 8 p.32) */
#define MPP_U   0x0
#define MPP_S   0x800
#define MPRV    0x20000
#define SUM     0x40000
#define MXR     0x80000

/* satp.MODE (P §12.1.11 Table 40 p.126) */
#define SATP_SV39   0x8000000000000000
#define SATP_SV48   0x9000000000000000
#define SATP_SV57   0xa000000000000000

/* exception codes (P §3.1.15 Table 16 p.50) */
#define FETCH_ACCESS    1
#define LOAD_ACCESS     5
#define STORE_ACCESS    7
#define ECALL_U         8
#define ECALL_S         9
#define FETCH_PAGE      12
#define LOAD_PAGE       13
#define STORE_PAGE      15

/* VA 0xc0000000 + x maps PA 0x80000000 + x with U = 1 */
#define UALIAS      0x40000000

/* table[i] := the PTE with the PPN of the address in register a and flags
   f, or'ed with hi */
#define PTE_HI(table, i, a, f, hi)       \
        srli    t1, a, 12;               \
        slli    t1, t1, 10;              \
        ori     t1, t1, f;               \
        li      t3, hi;                  \
        or      t1, t1, t3;              \
        la      t2, table;               \
        li      t3, (i) * 8;             \
        add     t2, t2, t3;              \
        sd      t1, 0(t2)
#define PTE(table, i, a, f)     PTE_HI(table, i, a, f, 0)
/* the same, to the address of label l or to a physical address */
#define PTE_L(table, i, l, f)   la t0, l; PTE(table, i, t0, f)
#define PTE_PA(table, i, pa, f) li t0, pa; PTE(table, i, t0, f)

/* satp := mode with root table at label root */
#define SET_SATP(mode, root)             \
        la      t0, root;                \
        srli    t0, t0, 12;              \
        li      t1, mode;                \
        or      t0, t0, t1;              \
        csrw    satp, t0

/* SFENCE.VMA after a change of satp, a PTE or the PMP */
#define FENCE   sfence.vma zero, zero

/* write ms to mstatus, MRET to the instructions in S-mode (from their
   VA = PA), end with an ECALL; a trap continues at label l_m */
#define RUN_S(ms, l, ...)                \
        li      t0, ms;                  \
        csrw    mstatus, t0;             \
        la      t0, l##_s;               \
        csrw    mepc, t0;                \
        la      s10, l##_m;              \
        mret;                            \
l##_s:  __VA_ARGS__;                     \
        ecall;                           \
l##_m:

/* the same in U-mode, from the alias with U = 1 */
#define RUN_U(ms, l, ...)                \
        li      t0, ms;                  \
        csrw    mstatus, t0;             \
        la      t0, l##_u;               \
        li      t1, UALIAS;              \
        add     t0, t0, t1;              \
        csrw    mepc, t0;                \
        la      s10, l##_m;              \
        mret;                            \
l##_u:  __VA_ARGS__;                     \
        ecall;                           \
l##_m:

/* MRET with mstatus ms to the VA in register r; a trap continues at l */
#define JUMP_REG(ms, r, l)               \
        li      t0, ms;                  \
        csrw    mstatus, t0;             \
        csrw    mepc, r;                 \
        la      s10, l;                  \
        mret;                            \
l:
/* the same to a constant VA, which is left in s1 */
#define JUMP(ms, va, l)         li s1, va; JUMP_REG(ms, s1, l)

/* in M-mode with mstatus ms (MPRV set): a0 := 0 after the instructions,
   or the cause of their trap; then mstatus := 0 */
#define RUN_MPRV(ms, l, ...)             \
        la      s10, l;                  \
        li      t0, ms;                  \
        csrw    mstatus, t0;             \
        __VA_ARGS__;                     \
        li      a0, 0;                   \
l:      csrw    mstatus, zero

/* check number n: a trap into M-mode with cause c and mtval v */
#define TRAP_M(n, c, v)                  \
        CHECK(n, a0, c);                 \
        li      t6, v;                   \
        bne     a2, t6, fail

/* check number n: reg && mask must equal val */
#define CHECK_BITS(n, reg, mask, val)    \
        li TESTNUM, n; li t6, mask; and t6, reg, t6; li t5, val; bne t6, t5, fail

/* check number n: reg1 must equal reg2 */
#define CHECK_REG(n, reg1, reg2)  li TESTNUM, n; bne reg1, reg2, fail

/* mtvec and stvec */
#define VM_INIT                          \
        la      t0, m_trap;              \
        csrw    mtvec, t0;               \
        la      t0, s_trap;              \
        csrw    stvec, t0

/* the trap handlers, in .text */
#define VM_HANDLERS                      \
        .text;                           \
        .align  2;                       \
m_trap: csrr    a0, mcause;              \
        csrr    a1, mepc;                \
        csrr    a2, mtval;               \
        csrr    a3, mstatus;             \
        jr      s10;                     \
        .align  2;                       \
s_trap: csrr    s2, scause;              \
        csrr    s3, sepc;                \
        csrr    s4, stval;               \
        csrr    s5, sstatus;             \
        ebreak
