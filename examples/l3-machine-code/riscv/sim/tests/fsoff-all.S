/* With mstatus.FS Off (its reset value) every F and D instruction, the RV64C
   FP loads and stores and every access to fflags, frm and fcsr must raise
   illegal instruction with mtval = the instruction bits, and change nothing.
   The handler checks mcause and mtval, counts the trap and skips the
   instruction; at the end, the count, the integer destination sentinel,
   mstatus.FS and the stored-to dword are checked. */
#include "test.h"

        .set    ntraps, 0
        .macro  T args:vararg
        \args
        .set    ntraps, ntraps + 1
        .endm

        TEST_START
        la      t0, handler
        csrw    mtvec, t0
        la      s0, data
        mv      sp, s0
        li      s1, 0                   # traps taken
        li      a1, 0x5a5a              # integer destination sentinel
        li      a2, 0x1234              # integer source

        .option push
        .option norvc
        T flw       f1, 0(s0)
        T fld       f1, 0(s0)
        T fsw       f1, 0(s0)
        T fsd       f1, 0(s0)
        T fld       f1, 1(s0)           # misaligned: illegal comes first
        T fsd       f1, 3(s0)           # misaligned: illegal comes first

        T fmadd.s   f1, f2, f3, f4
        T fmsub.s   f1, f2, f3, f4
        T fnmsub.s  f1, f2, f3, f4
        T fnmadd.s  f1, f2, f3, f4
        T fadd.s    f1, f2, f3
        T fsub.s    f1, f2, f3
        T fmul.s    f1, f2, f3
        T fdiv.s    f1, f2, f3
        T fsqrt.s   f1, f2
        T fsgnj.s   f1, f2, f3
        T fsgnjn.s  f1, f2, f3
        T fsgnjx.s  f1, f2, f3
        T fmin.s    f1, f2, f3
        T fmax.s    f1, f2, f3
        T feq.s     a1, f2, f3
        T flt.s     a1, f2, f3
        T fle.s     a1, f2, f3
        T fcvt.w.s  a1, f2
        T fcvt.wu.s a1, f2
        T fmv.x.w   a1, f2
        T fclass.s  a1, f2
        T fcvt.s.w  f1, a2
        T fcvt.s.wu f1, a2
        T fmv.w.x   f1, a2
        T fcvt.l.s  a1, f2
        T fcvt.lu.s a1, f2
        T fcvt.s.l  f1, a2
        T fcvt.s.lu f1, a2

        T fmadd.d   f1, f2, f3, f4
        T fmsub.d   f1, f2, f3, f4
        T fnmsub.d  f1, f2, f3, f4
        T fnmadd.d  f1, f2, f3, f4
        T fadd.d    f1, f2, f3
        T fsub.d    f1, f2, f3
        T fmul.d    f1, f2, f3
        T fdiv.d    f1, f2, f3
        T fsqrt.d   f1, f2
        T fsgnj.d   f1, f2, f3
        T fsgnjn.d  f1, f2, f3
        T fsgnjx.d  f1, f2, f3
        T fmin.d    f1, f2, f3
        T fmax.d    f1, f2, f3
        T feq.d     a1, f2, f3
        T flt.d     a1, f2, f3
        T fle.d     a1, f2, f3
        T fcvt.w.d  a1, f2
        T fcvt.wu.d a1, f2
        T fclass.d  a1, f2
        T fcvt.d.w  f1, a2
        T fcvt.d.wu f1, a2
        T fcvt.l.d  a1, f2
        T fcvt.lu.d a1, f2
        T fcvt.d.l  f1, a2
        T fcvt.d.lu f1, a2
        T fmv.x.d   a1, f2
        T fmv.d.x   f1, a2
        T fcvt.s.d  f1, f2
        T fcvt.d.s  f1, f2

        T csrr      a1, fflags
        T csrr      a1, frm
        T csrr      a1, fcsr
        T csrw      fflags, a2
        T csrw      frm, a2
        T csrw      fcsr, a2
        T csrsi     fflags, 1
        T csrci     fcsr, 1
        T csrrwi    a1, frm, 1
        T csrc      fflags, a2
        T csrs      frm, a2
        .option pop

        .option push
        .option rvc
        T c.fld     f8, 0(s0)
        T c.fsd     f8, 0(s0)
        T c.fldsp   f1, 0(sp)
        T c.fsdsp   f1, 0(sp)
        .option pop

        CHECK(1, s1, ntraps)            # every instruction trapped
        CHECK(2, a1, 0x5a5a)            # no integer destination written
        csrr    t0, mstatus
        srli    t0, t0, 13
        andi    t0, t0, 3
        CHECK(3, t0, 0)                 # mstatus.FS still Off
        ld      t0, 0(s0)
        CHECK(4, t0, 0x0123456789abcdef) # no store wrote memory
        RESULT(s1)
        j       pass

        .align  2
handler:
        csrr    t0, mcause
        li      t1, 2
        addi    gp, s1, 100             # check 100 + index of the instruction
        bne     t0, t1, fail            # illegal instruction
        csrr    t0, mepc
        lhu     t1, 0(t0)
        andi    t2, t1, 3
        li      t3, 3
        bne     t2, t3, 1f              # 16-bit instruction
        lhu     t2, 2(t0)
        slli    t2, t2, 16
        or      t1, t1, t2
        addi    t0, t0, 2
1:      addi    t0, t0, 2
        csrr    t2, mtval
        addi    gp, s1, 200
        bne     t1, t2, fail            # mtval holds the instruction bits
        csrw    mepc, t0
        addi    s1, s1, 1
        mret

        TEST_END

        .data
        .align  3
data:   .dword  0x0123456789abcdef
        .dword  0
        SIGNATURE(1)
