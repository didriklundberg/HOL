/* Shared macros for the riscv-sim smoke tests.

   Each test is self-checking, in the style of riscv-tests: TESTNUM (gp)
   holds the number of the current check; on failure the test writes
   (TESTNUM << 1) | 1 to tohost, on success 1, both as one 64-bit store.
   Results are also stored in the signature region, which `make test`
   compares with tests/<name>.sig.expected.

   Of the smoke tests only fp.S touches a CSR (mstatus.FS); the regression
   programs fsoff-all.S and fp-*.S (with fpmacros.h) use mstatus, mtvec,
   mcause, mepc, mtval and fflags/frm. */

#define TESTNUM gp

/* store a 64-bit result in the next signature slot (s11 is the pointer) */
#define RESULT(reg)  sd reg, 0(s11); addi s11, s11, 8

/* check number n: reg must equal val */
#define CHECK(n, reg, val)  li TESTNUM, n; li t6, val; bne reg, t6, fail

#define TEST_START                       \
        .section .text.init;             \
        .globl _start;                   \
_start: la s11, begin_signature;         \
        li TESTNUM, 0

#define TEST_END                         \
pass:   li t6, 1;                        \
        la t5, tohost;                   \
        sd t6, 0(t5);                    \
1:      j 1b;                            \
fail:   slli t6, TESTNUM, 1;             \
        ori t6, t6, 1;                   \
        la t5, tohost;                   \
        sd t6, 0(t5);                    \
2:      j 2b;                            \
        .section .tohost, "aw", @progbits; \
        .align 6;                        \
        .globl tohost;                   \
tohost: .dword 0;                        \
        .align 6;                        \
        .globl fromhost;                 \
fromhost: .dword 0

#define SIGNATURE(nslots)                \
        .data;                           \
        .align 4;                        \
        .globl begin_signature;          \
begin_signature: .rept nslots; .dword 0xdeadbeefdeadbeef; .endr; \
        .globl end_signature;            \
end_signature:
