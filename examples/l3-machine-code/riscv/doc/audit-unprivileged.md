# Audit of the unprivileged RV64GC semantics in HOL's L3 RISC-V spec

Date: 2026-10-30. Subject: `examples/l3-machine-code/riscv/src/riscv.spec` on HOL-fixes branch
`riscv-l3` (last spec commit 116d411e1, 2026-10-27), and its exports `model/riscv.sml`,
`model/riscv.sig` and `model/riscvScript.sml`, regenerated 16 s after the spec. All line numbers
refer to that `riscv.spec` unless a file is named. This is the WP1 output of
`RISCV_MODEL_PLAN.md` (WP1.4).

Summary: 13 bugs, 0 missing encodings, 4 deviations, 14 notes (F1-F31). Five candidate findings
were refuted (Appendix).

## 1. Scope and method

**Scope.** User-level RV64GC: RV64I, M, A, F, D, C (Zca + Zcd), Zicsr, Zifencei and the Zicntr
counter reads, plus how reserved, illegal and HINT encodings decode and execute. Out of scope:

- the priv-1.7 privileged architecture (mret, CSR numbering, mstatus layout, PMP, trap
  vectoring, delegation, interrupts), which WP2 rewrites;
- RV32 paths;
- the items already decided: the JAL/JALR/branch target check `addr<1> and not haveRVC()`,
  `DecodeRVC` gated on `haveRVC()`, RV64 only, and `#UNDEFINED` in privileged paths.

Privileged behaviour appears below only where a user-level instruction or encoding triggers it.

**Severity scale.**

- **bug**: a legal user-level program observes wrong results or flags.
- **missing**: an RV64GC encoding that `Decode`/`DecodeRVC` rejects.
- **deviation**: behaviour differs from the manual only for reserved, illegal or HINT encodings,
  or in which exception is raised.
- **note**: correct but fragile, or relevant to the HOL/SML exports (partial functions,
  `#UNDEFINED`, tooling).

**References.**

- sail-riscv, tag 2026-10-26-6f886e6: `model/extensions/{I,M,A,FD,C,Zicsr,Zicntr}`,
  `model/sys`, `model/core`. `build/c_emulator/sail_riscv_sim` was run on small bare-metal ELFs
  for F9, F10, F13 and F14.
- RISC-V ISA manual, combined release 8fb3965 (2026-10-30). Section numbers are from that
  release: 2.1/2.2 RV32I/RV64I, 4.2 Zicsr, 4.3 Zicntr, 4.5 M, 5.2 Zalrsc, 5.6 Zaamo, 6.1 F,
  6.2 D, 7.1 Zca, 7.3 Zcd.
- riscv-opcodes `extensions/rv_*` and `rv64_*` files, for the encoding inventory.
- GNU objdump (riscv64-unknown-elf), as an independent check of the RVC reference decoder.

**Method.** There were nine area audits: encoding inventory, RV64I computational, RV64I
control/memory, M, A, F/D arithmetic, F/D conversion/move/compare, C, and Zicsr/Zicntr/Zifencei.
Two refuters then attacked each candidate finding independently. Each re-read the L3 code and the
references and, in almost every case, re-ran the test with a script of their own. A finding
appears in §2 only if neither refuter could refute it. The text below already includes the
refuters' corrections: wrong hex encodings in the original test cases, off-by-one line numbers,
overstated claims, and one misdescribed effect (F17).

**What was executed.** The SML export was loaded under Poly/ML 5.9.2 with the L3-2018-02-09
runtime library (`~/Documents/riscv-tools/l3/L3-2018-02-09/lib`). Instructions were run through
`Decode`/`DecodeRVC` + `Run`, or through full `Next`. Each finding names its script directories
under `~/Documents/riscv-tools/work/`. The bulk runs were:

- **Decode inventory.** 1,323,707 words, compared constructor and operand by operand against an
  independent Python decoder built from riscv-opcodes and the sail encdec clauses. The words
  cover every 32-bit major opcode × funct3 × funct7 × rs2 combination, all 4096 SYSTEM imm12
  values, 66 samples per RV64GC riscv-opcodes entry, 200k random words and all 49,152 16-bit
  words.
- **RVC.** All 49,152 halfwords against a reference expansion that agrees with objdump on all
  46,743 legal encodings.
- **RV64I computational.** A decode sweep of 131,072 encodings with an Encode round trip, plus
  6,000 random cases against a transcription of sail `base_insts.sail`.
- **RV64I control/memory.** 2,688 branch cases, plus 224 load and 128 store cases at all 16
  alignments.
- **M.** 95,836 cases against a transcription of sail `mext_insts.sail`.
- **A, F/D and Zicsr.** Directed tests: 45 for A and several hundred for F/D.

Every finding was executed on the SML export. The exception is the HOL side of F10, F13 and F27:
that rests on reading `binary_ieee`/`machine_ieee` and `common/Import.sml`, plus one `EVAL` in a
plain `hol` session. Holmake was never run.

**Harness caveats** (needed to reproduce the results):

- **FP64 runtime.** Under Poly/ML 5.9.2 the stock L3 `PolySSE` FP64 binding returns garbage
  (F30). All double-precision results above were produced with
  `~/Documents/riscv-tools/work/fparith/{shim.c,PolySSE_fixed.sml}`, loaded through
  `fparith/load.sml`. The WP0 harness in `examples/l3-machine-code/riscv/sim` has its own fix
  (`lib/sse_fp64_shim.c`, `lib/SSEFix.sml`).
- **`riscv.write'gpr` argument order.** It takes `(value, index)`. The A-area auditor suspected
  that the rv64i-arith harness passed them reversed. It does not: `harness.sml` line 17 passes
  `(b64 v, B(r,5))`. Only the scratch file `dbg.sml` had them reversed, so the RV64I results
  stand.
- **`work/sim/riscv-sim`.** `~/Documents/riscv-tools/work/sim/riscv-sim` is a compiled L3
  emulator, not Sail. Do not use it as the oracle.
- **Stale mcause.** Some harnesses print an mcause left over from an earlier run, so traps were
  detected by PC or `NextFetch` instead.

**Not covered.**

- No ELF-level differential trace runs of rv64u\*-p or riscv-arch-test against Sail. That is
  WP1.2 proper and needs the WP0 harness.
- No systematic sweep of subnormal or fsqrt edge cases, only spot checks.
- No HOL step theorems were built.

## 2. Confirmed findings

Ids follow fix order: bugs first, then each severity group from the smallest fix to the largest.
The L3 code in the proposed fixes is a sketch: run it through the L3 parser before committing.
After every spec change, regenerate `riscv.sml`, `riscv.sig` and `riscvScript.sml`.
`riscv_stepLib` currently has no step theorems for CSR, AMO or FP instructions. It only
enumerates `DecodeRVC`, so F15 is the only fix that touches it.

| Id | Severity | Title | L3 lines | Executed |
|----|----------|-------|----------|----------|
| F1 | bug | CSRRWI with zimm=0 does not write the CSR | 4171-4178 | yes |
| F2 | bug | FCLASS sets bit 9 only for the canonical NaN | 3612, 4085 | yes |
| F3 | bug | A failed SC leaves the reservation in place | 2772-2773, 2794-2795 | yes |
| F4 | bug | AMOMIN/MAX/MINU/MAXU.W compare all 64 bits of rs2 | 3008-3144 | yes |
| F5 | bug | FLW/FLD (and C.FLD/C.FLDSP) do not set mstatus.FS to Dirty | 3180, 3630 | yes |
| F6 | bug | FCVT.WU.S/FCVT.WU.D zero-extend the 32-bit result | 3394-3412, 3845-3863 | yes |
| F7 | bug | Single-precision values are not NaN-boxed on write or unboxed on read | 1628-1633 | yes |
| F8 | bug | FMIN/FMAX: signed zeros, sNaN, qNaN handling, no NV | 3264-3298, 3714-3750 | yes |
| F9 | bug | FMA family not fused; FNMADD/FNMSUB negate the rounded result | 3303-3345, 3754-3796 | yes + sail |
| F10 | bug | NaN results are not the canonical NaN (arithmetic, FCVT.S.D, FCVT.D.S) | 3210-3345, 3660-3796, 3936-3953 | yes + sail |
| F11 | bug | No F/D instruction except FEQ/FLT/FLE sets fflags | 3210-3953 | yes |
| F12 | bug | FMA raises no NV for ∞×0 + qNaN | 3303-3345, 3754-3796 | yes |
| F13 | bug | Rounding mode RMM raises illegal instruction | 823-843 | yes + sail |
| F14 | deviation | CSRRWI zimm=0 on a read-only CSR does not trap | 4172 | yes + sail |
| F15 | deviation | C.ADDIW with rd=x0 (reserved) executes as a nop | 4996 | yes |
| F16 | deviation | Misaligned LR.W/LR.D raise cause 6 instead of 4 (or 5) | 2738-2739, 2755-2756 | yes |
| F17 | deviation | Obsolete priv-1.7 SYSTEM words execute from U-mode | 4473-4477, 4107-4126, 4209 | yes |
| F18 | note | setFP_Underflow/setFP_Inexact set OF | 871-875 | yes |
| F19 | note | fcsr write stores reserved bits 31:8 | 1046 | yes |
| F20 | note | `inline writeRD`: SML DIV/REM/REMU crash; wrong Delta.data1 | 1623-1626 | yes |
| F21 | note | rawReadHalf returns halfwords in reversed order (dead code) | 1738-1748 | yes |
| F22 | note | EncodeRVC/CBtype produce wrong encodings (dead code) | 5045-5053 | yes |
| F23 | note | CSRRW/CSRRWI with rd=x0 still read the CSR | 4136-4142, 4171-4178 | yes |
| F24 | note | SC translates with Read access, and not at all when it fails | 2768-2805 | yes |
| F25 | note | SML: FCVT.int.fmt raises Option on NaN/±inf (eager ValOf) | 3374 … 3916 | yes |
| F26 | note | time CSR goes backwards with more than one hart | 5266-5270 | yes |
| F27 | note | HOL export: NaN results unspecified, no RMM | 823-831, FArith | read + EVAL |
| F28 | note | Misaligned loads/stores complete; plan WP2.5 says trap | 2559-2717 | yes |
| F29 | note | SML runtime: FCVT.S.LU with rs1 ≥ 2^63 raises Fail | 3428-3433 | yes |
| F30 | note | Stock PolySSE FP64 FFI returns garbage under Poly/ML 5.9.2 | (runtime) | yes |
| F31 | note | Poly/ML 5.9.2 `IntInf.~>>` wrong for negative bignums | (tooling) | yes |

### 2.1 Bugs

#### F1. CSRRWI with zimm=0 does not write the CSR

- **L3:** `define System > CSRRWI`, 4171-4178. Line 4172 passes the access type
  `if zimm == 0 then Read else Write`, and lines 4174-4175 write only `when zimm != 0`. The
  export `riscv.sml` `dfn'CSRRWI` (≈8155) has the same guard.
- **Problem:** The "zero operand means no write" rule was copied from CSRRSI/CSRRCI (4183-4203),
  where it is correct. For CSRRWI it is wrong. As a result `fsrmi 0` (`csrwi frm,0`),
  `fsflagsi 0` (`csrwi fflags,0`) and `csrwi fcsr,0` do nothing. The old rounding mode and
  accrued flags stay in place, so later FP results and flags are wrong, and mstatus.FS is not set
  to Dirty. The same root cause produces F14.
- **Expected:**
  - Manual §4.2.1, Table 21: CSRRWI writes the CSR whether or not rd=x0. Only CSRRSI/CSRRCI with
    uimm=0 skip the write.
  - sail `model/extensions/Zicsr/zicsr_insts.sail` `csr_access_type` (lines 35-36):
    `(CSRRW, true, _) => CSRWrite` and `(CSRRW, false, _) => CSRReadWrite`, whatever the
    immediate. `execute CSRImm` passes `zero_extend(imm)` to `doCSR`, which calls `write_CSR`.
- **Test** (executed; `work/zicsr/tests.sml` T1/T2/T8, `csrrwi-refute1`, `zicsr-ref2`):
  - `csrrwi x0,frm,3` (0x0021D073), then `csrrwi x1,frm,0` (0x002050F3), then
    `csrrs x2,frm,x0` (0x00202173). Expected x1=3, x2=0. L3 gives x1=3, x2=3.
  - `csrrwi x0,fflags,0x1f` (0x001FD073), then `csrrwi x0,fflags,0` (0x00105073), then
    `csrrs x2,fflags,x0` (0x00102173). Expected x2=0. L3 gives x2=0x1F.
  - From reset (FS=1, Initial), `csrrwi x0,frm,0`. Expected FS=3. L3 leaves FS=1.
  - Control: the register form `csrrw x0,frm,x0` does clear frm.
- **Fix:**
  ```
  define System > CSRRWI(rd::reg, zimm::reg, csr::imm12) =
      if checkCSROp(csr, zimm, Write)
      then { val = CSR(csr)
           ; writeCSR(csr, ZeroExtend(zimm))
           ; writeRD(rd, val)
           }
      else signalException(Illegal_Instr)
  ```
  This also fixes F14. F23 suggests an optional `rd == 0` refinement of the read.

#### F2. FCLASS.S/FCLASS.D set bit 9 only for the canonical NaN

- **L3:** 3612 (`ret<9> <- val == RV32_CanonicalNan` in FCLASS_S, 3600-3614) and 4085 (FCLASS_D,
  4073-4087).
- **Problem:** Bit 8 uses `FP32_IsSignalingNan` (851-855), which correctly requires the quiet
  bit to be 0. So every quiet NaN other than 0x7FC00000/0x7FF8000000000000 sets no bit at all,
  and rd=0. Such NaNs are ordinary: fneg (FSGNJN) of the canonical NaN gives 0xFFC00000, FLW and
  FMV.W.X carry any payload, and the SML export's arithmetic produces x86 NaNs (F10).
- **Expected:**
  - Manual §6.1.9: bit 9 means "rs1 is a quiet NaN", and "exactly one bit in rd will be set".
    FCLASS.D is defined the same way (§6.2).
  - sail `fext_insts.sail:898` and `dext_insts.sail:848` compute
    `float_class_onehot_bits(float_classify(rs1_val))`.
- **Test** (executed; `fclass-qnan-refute1`, `fclass-refute2`). FCLASS.S x3,f1 is 0xE00091D3
  and FCLASS.D x3,f1 is 0xE20091D3. S inputs are NaN-boxed.

  | Input | Expected | L3 |
  |---|---|---|
  | S 0x7FC00000 | 0x200 | 0x200 |
  | S 0x7FC00001 | 0x200 | 0 |
  | S 0xFFC00000 | 0x200 | 0 |
  | S 0x7FFFFFFF | 0x200 | 0 |
  | D 0x7FF8000000000001 | 0x200 | 0 |
  | D 0xFFF8000000000000 | 0x200 | 0 |

  The other nine classes are correct for S and D, including the sNaN cases.
- **Fix:** `ret<9> <- FP32_IsNan(val) and not FP32_IsSignalingNan(val)`, and the same with
  FP64 in FCLASS_D.
- **Resolution:** 8d0bc60b4 (the proposed fix).

#### F3. A failed SC.W/SC.D leaves the reservation in place

- **L3:** In SC_W (2768-2785), lines 2772-2773 are
  `else if not matchLoadReservation(vAddr) then writeRD(rd, 1)`. SC_D (2788-2805) does the same
  at 2794-2795. `ReserveLoad <- None` runs only on the success paths (2779, 2801) and in
  `takeTrap` (1562).
- **Problem:** After LR A, a failing SC to B leaves the reservation on A, so a following SC to A
  succeeds and writes memory. A legal program sees a successful SC and a store that the manual
  forbids. This also breaks the manual's recommended context-switch idiom, an SC to a scratch
  word to kill the reservation.
- **Expected:**
  - Manual §5.2: "Regardless of success or failure, executing an SC.W instruction invalidates any
    reservation held by this hart". Also: "An SC must fail if there is another SC (to any
    address) between the LR and the SC in program order."
  - sail `zalrsc_insts.sail` `execute STORECON` (from line 66) calls `cancel_reservation()`
    (line 76) on every `Ok(b)`, success or failure.
- **Test** (executed; `amo-audit/tests.sml` T5, `sc-cancel-refute1/2`). The program is LR.W
  x1,(x2) (0x100120AF), then SC.W x4,x3,(x5) (0x1832A22F), then SC.W x6,x3,(x2) (0x1831232F).
  Inputs: x2=0x10000, x5=0x10008, x3=0x12345678, mem[0x10000]=0x0AAAAAAA.
  - Expected: x4=1, x6=1, memory unchanged.
  - L3: x4=1, x6=0, and mem[0x10000]=0x12345678.
  - The doubleword form (LR.D 0x100130AF, SC.D 0x1832B22F, SC.D 0x1831332F) fails the same way.
  - Control: LR followed by SC to the same address succeeds.
- **Fix:** In both defines, write
  `else if not matchLoadReservation(vAddr) then { writeRD(rd, 1); ReserveLoad <- None }`.
  If F24 is done at the same time, its restructured SC already includes this.
- **Resolution:** a46b360f4 (the proposed fix; F24's restructuring is left to WP2).

#### F4. AMOMIN.W/AMOMAX.W/AMOMINU.W/AMOMAXU.W compare all 64 bits of rs2

- **L3:** AMOMIN_W 3008-3024, AMOMAX_W 3048-3064, AMOMINU_W 3088-3104, AMOMAXU_W 3128-3144.
  Each computes `memv = SignExtend(rawReadData(pAddr)<31:0>)` and `data = GPR(rs2)` at full
  width, then takes a 64-bit SignedMin/SignedMax/Min/Max and stores `val<31:0>`. Decode cases are
  at 4449-4452.
- **Problem:** The result depends on rs2[63:32]. Whenever rs2 is not a sign-extended 32-bit
  value, the wrong operand is chosen and the wrong word is stored. rd is still correct. The
  ADD/XOR/AND/OR/SWAP .W forms are unaffected, because their low 32 bits depend only on the low
  operand bits.
- **Expected:**
  - Manual §5.6: "For RV64, 32-bit AMOs always sign-extend the value placed in rd, and ignore the
    upper 32 bits of the original value of rs2."
  - sail `zaamo_insts.sail` `execute AMO` line 136 has `rs2_val = trunc(X(rs2))`, and lines
    144-147 compare at 32 bits.
- **Test** (executed; `amo-audit/tests.sml` T1-T4, `amo-refute1/2`). rd=x1, rs1=x2=0x10000,
  rs2=x3.

  | Instruction | mem32 | x3 | Expected mem | L3 mem |
  |---|---|---|---|---|
  | AMOMIN.W 0x803120AF | 0 | 0x0000000080000000 | 0x80000000 | 0x0 |
  | AMOMINU.W 0xC03120AF | 0x80000000 | 0x0000000090000000 | 0x80000000 | 0x90000000 |
  | AMOMAX.W 0xA03120AF | 5 | 0x0000000100000000 | 5 | 0 |
  | AMOMAXU.W 0xE03120AF | 0x7FFFFFFF | 0xFFFFFFFF00000001 | 0x7FFFFFFF | 0x1 |

  A sweep of 784 cases found 204 that differ. Every one has rs2[63:32] ≠ sext(rs2[31]).
- **Fix:** `data = SignExtend(GPR(rs2)<31:0>)` in the four min/max .W defines. It is harmless in
  the other five. Sign extension preserves both signed and unsigned 32-bit order, so the 64-bit
  compare then matches the 32-bit one.
- **Resolution:** fbc4e337c; riscv-tests `rv64ua-p-amo{min,max}{,u}_w` now pass (they failed test 7).

#### F5. FLW and FLD bypass writeFPRS/writeFPRD, so mstatus.FS is not set to Dirty

- **L3:** FLW (3176-3186) does `FPRS(rd) <- val` at 3180, and FLD (3626-3636) does
  `FPRD(rd) <- val` at 3630. Only writeFPRS/writeFPRD (1642-1654) set MFS to Dirty and MSD to
  true. Every other FP register write goes through them, and the fcsr component (697-702) and
  the CSR 0x001-0x003 writes (1037-1048) set Dirty too. C.FLD and C.FLDSP decode to FLD, so they
  have the same defect.
- **Problem:** A load changes FP state, but FS stays Initial or Clean. An OS that saves FP
  context lazily when FS == Dirty (Linux does) loses the registers a user program just loaded
  across a context switch. The trigger is a user instruction, and the defect is in FLW/FLD, so
  the WP2 mstatus rework does not fix it. FLW also leaves bits 63:32 stale; that half belongs to
  F7.
- **Expected:**
  - Privileged manual, "Extension Context Status in mstatus Register", state-transition table:
    an instruction that possibly modifies state moves Initial or Clean to Dirty.
  - sail `fdext_regs.sail` `wF` calls `dirty_fd_context()`, which sets FS=Dirty and SD=1.
    `LOAD_FP` (`fext_insts.sail:286`) writes through `wF`.
- **Test** (executed; `fparith/t3.sml`, `flw-fsdirty-refute1/2`). Setup: MFS=1,
  mem[0x1000]=0x3F800000, x5=0x1000.
  - FLW f3,0(x5) (0x0002A187): expected FS=3. L3 leaves FS=1.
  - FLD f3,0(x5) (0x0002B187): expected FS=3. L3 leaves FS=1.
  - Starting from FS=2 (Clean), FS stays 2 after either load.
  - C.FLD f9,8(x8) (0x2404) leaves FS=1.
  - Contrast: FMV.W.X and FADD.S starting from FS=1 give FS=3.
- **Fix:** Change line 3180 to `writeFPRS(rd, val)` and line 3630 to `writeFPRD(rd, val)`. Keep
  the `recordLoad` calls; they overwrite Delta.data1 with the same value. FLW is NaN-boxed only
  once F7 makes writeFPRS box, so land F5 and F7 together.
- **Resolution:** 5af52ddeb (the proposed fix; C.FLD/C.FLDSP decode to FLD and are covered).

#### F6. FCVT.WU.S and FCVT.WU.D zero-extend the 32-bit result

- **L3:** FCVT_WU_S 3394-3412 and FCVT_WU_D 3845-3863. `res` is 64-bit (regType). The
  saturation value `[0n2 ** 32 - 1]` becomes 0x00000000FFFFFFFF, and `[val]` zero-extends any
  result in [2^31, 2^32-1]. The export has `BitsN.fromNat(2^32-1, 64)` and
  `BitsN.fromInt(val', 64)` (riscv.sml ≈7284, 7291).
- **Problem:** Ordinary `(uint32_t)f` code followed by a 64-bit compare or store sees the wrong
  upper half.
- **Expected:**
  - Manual §6.1.7: "For XLEN>32, FCVT.W.S and FCVT.WU.S sign-extend the 32-bit result to the
    destination register width". §6.2 says the same for the D forms.
  - sail `fext_insts.sail:558` and `dext_insts.sail:470`: `X(rd) = sign_extend(rd_val_WU)`.
- **Test** (executed; `fconv/t.sml`, `refuter-fcvtwu`, `fcvtwu-refute2`). FCVT.WU.S x3,f1,rne
  is 0xC01081D3 and FCVT.WU.D x3,f1,rne is 0xC21081D3.

  | Instruction and input | Expected x3 | L3 x3 |
  |---|---|---|
  | .S, boxed 0x4F32D05E (3.0e9) | 0xFFFFFFFFB2D05E00 | 0x00000000B2D05E00 |
  | .S, 5e9 (0x4F9502F9) | 0xFFFFFFFFFFFFFFFF | 0x00000000FFFFFFFF |
  | .S, 2^31 | 0xFFFFFFFF80000000 | 0x0000000080000000 |
  | .D, 0x41EFFFFFFFE00000 (4294967295.0) | 0xFFFFFFFFFFFFFFFF | 0x00000000FFFFFFFF |
  | .D, 2^31 (0x41E0000000000000) | 0xFFFFFFFF80000000 | 0x0000000080000000 |

  Control: FCVT.W.S of -1.0 gives all ones, which is correct. NaN and ±inf inputs crash the SML
  export instead (F25).
- **Fix:** Build a 32-bit result and sign-extend it:
  ```
  ; res32 = if FP32_IsNan(inp) or inp == FP32_PosInf then 0xFFFFFFFF
            else if inp == FP32_NegInf then 0x0
            else if val > 2 ** 32 - 1 then 0xFFFFFFFF
            else if val < 0 then 0x0 else [val] :: word
  ; writeRD(rd, SignExtend(res32))
  ```
  Make the same change in FCVT_WU_D, and combine it with the F25 restructuring.
- **Resolution:** c960e321b (`res` is now 32 bits and sign-extended at `writeRD`).

#### F7. Single-precision values are neither NaN-boxed on write nor unboxed on read

- **L3:** `component FPRS` (1628-1633) reads `fpr(n)<31:0>` and writes `fpr(n)<31:0> <- value`.
  - Writers that go through it: writeFPRS (1642-1647), and therefore every \*_S arithmetic op,
    FSGNJ\*.S (3487-3511), FMV.W.X (3526-3527), FCVT.S.\* (3349-3433) and FCVT.S.D (3936-3941).
    FLW also uses it directly (3180).
  - Readers: every S-format consumer, including FCVT.D.S (3947-3953), FEQ/FLT/FLE.S (3535-3594)
    and FCLASS.S (3600-3614).
- **Problem:** There are two halves to this.
  - **Writes keep bits 63:32 unchanged.** A program sees this through FSD, FMV.X.D, any D
    operation, or a callee-saved spill and restore.
  - **Reads ignore bits 63:32.** An improperly boxed value (left by FLD, FMV.D.X or a D result)
    is used as its low 32 bits instead of as the canonical NaN.
- **Expected:**
  - Manual §6.2.2 (NaN Boxing of Narrower Values): "Any operation that writes a narrower result
    to an f register must write all 1s to the uppermost FLEN-n bits". FLW and FMV.W.X create a
    valid boxed value. FSW and FMV.X.W use the low bits and ignore the rest. For all other
    operations, an input that is not correctly boxed "is treated as an n-bit canonical NaN".
  - sail `fdext_regs.sail`: `nan_box` (line 41), `nan_unbox` (48-51), and `rF_S`/`wF_S` built
    on them.
  - sail `fext_insts.sail`: `LOAD_FP` writes `F(rd) = nan_box(result)` (286), `FMV_W_X` boxes
    (908), and `FMV_X_W` (903) and the FP store (321) read the raw low bits.
- **Test** (executed; `fparith/t1.sml`, `t3.sml`, `nanbox-refute1`, `nanbox-write-refute1/2`,
  `fpconv-nanbox-refute1`, `refuter2-fpconv-nanbox`).

  Writes:

  | Instruction | Inputs | Expected f3 | L3 f3 |
  |---|---|---|---|
  | FADD.S f3,f1,f2 rne (0x002081D3) | f1=0xFFFFFFFF3F800000, f2=0xFFFFFFFF40000000, f3=0 | 0xFFFFFFFF40400000 | 0x0000000040400000 |
  | same | f3=0x123456789ABCDEF0 before | 0xFFFFFFFF40400000 | 0x1234567840400000 |
  | FMV.W.X f3,x1 (0xF00081D3) | x1=0x3F800000, f3=0x1234567800000000 | 0xFFFFFFFF3F800000 | 0x123456783F800000 |
  | FLW f3,0(x1) (0x0000A187) | mem=0x1122334455667788 | 0xFFFFFFFF55667788 | 0x0000000055667788 |
  | FCVT.S.W, FCVT.S.D, FSGNJ.S | 16777217; 1.0; 1.0 with -2.0 | 0xFFFFFFFF4B800000; …3F800000; …BF800000 | upper half 0 |

  User-visible case: FLW into f3=0xAAAAAAAA00000000, then FMV.X.D x6,f3 (0xE2018353). L3 gives
  x6=0xAAAAAAAA55667788; expected 0xFFFFFFFF55667788.

  Reads, with f1=0x000000003F800000 (an unboxed 1.0):

  | Instruction | Expected | L3 |
  |---|---|---|
  | FADD.S f3,f1,f2 (f2 boxed 2.0) | 0xFFFFFFFF7FC00000 | 0x40400000 |
  | FCVT.W.S x3,f1 | 0x7FFFFFFF, NV | 1, no flag |
  | FCVT.D.S f3,f1 | 0x7FF8000000000000 | 0x3FF0000000000000 |
  | FSGNJ.S f3,f1,f2 (f2 boxed -2.0) | 0xFFFFFFFFFFC00000 | 0xBF800000 |
  | FCLASS.S x3,f1 | 0x200 | 0x40 |
  | FEQ.S x3,f1,f1 | 0 | 1 |
  | FLT.S x3,f1,f2 (f2 boxed 2.0) | 0, NV | 1, no flag |
  | FMV.X.W of 0x123456783F800000 | 0x3F800000 | 0x3F800000 (correct) |
- **Fix:** Box on write, unbox on read, and keep a raw read for the two transfer instructions:
  ```
  component FPRS(n::reg) :: word
  { value        = if fpr(n)<63:32> == 0xFFFFFFFF then fpr(n)<31:0> else RV32_CanonicalNan
    assign value = { fpr(n) <- 0xFFFFFFFF`32 : value
                   ; mark_log(LOG_REG, log_w_fprs(n, value))
                   }
  }
  word FPRS_raw(n::reg) = fpr(n)<31:0>
  ```
  Use `FPRS_raw` in FSW (`data = FPRS(rs2)`, 3194) and FMV_X_S (3520). FLW must go through
  writeFPRS (F5). Apply both halves together: the read-side change alone would turn every
  register written today without boxing into the canonical NaN.
- **Resolution:** ab004ecb2 (the proposed fix, plus `Delta.data1` records the boxed value); FLW is boxed through the FPRS component.

#### F8. FMIN/FMAX: wrong signed-zero order, sNaN and qNaN handling, and no NV flag

- **L3:** FMIN_S 3264-3279, FMAX_S 3283-3298, FMIN_D 3714-3730, FMAX_D 3734-3750.
- **Problem:** Four defects, all present in both S and D.
  1. `FP32_Compare(+0,-0)` is `FP_EQ`, and the EQ case returns f1 for FMIN and f2 for FMAX. So
     FMIN(+0,-0)=+0 and FMAX(+0,-0)=-0. The result is right only when the operands come in the
     other order.
  2. If either operand is an sNaN, the result is the canonical NaN even when the other operand
     is a number. That is the old v2.0 minNum behaviour.
  3. The UN case returns `if f1 == canonical then f2 else f1`. A non-canonical qNaN in rs1 with
     a number in rs2 therefore returns the NaN, which is wrong under both the 2.0 and the 2.2
     rules. Two non-canonical qNaNs return rs1's payload.
  4. NV is never set.
- **Expected:**
  - Manual §6.1.6: "-0.0 is considered to be less than the value +0.0. If both inputs are NaNs,
    the result is the canonical NaN. If only one operand is a NaN, the result is the non-NaN
    operand. Signaling NaN inputs set the invalid operation exception flag, even when the result
    is not NaN". Since F v2.2 these are IEEE 754-2019 minimumNumber/maximumNumber.
  - sail `fext_insts.sail:769-808` (`execute F_BIN_TYPE_F_S`) and `dext_insts.sail:718-756`.
    Flags come from `fle_S(..., is_quiet=true)`, which sets NV only for sNaN inputs.
- **Test** (executed; `fparith/t1.sml`, `t2.sml`, `fminmax-refute1`, `fmin-refute2`). FMIN.S
  f3,f1,f2 is 0x282081D3 and FMAX.S is 0x282091D3; the D forms are 0x2A2081D3 and 0x2A2091D3.

  | Case | Expected | L3 |
  |---|---|---|
  | FMIN.S(+0,-0) | 0x80000000 | 0x00000000 |
  | FMAX.S(+0,-0) | 0x00000000 | 0x80000000 |
  | FMIN.S(sNaN 0x7F800001, 1.0); also with operands swapped | 0x3F800000, NV | 0x7FC00000, no flag |
  | FMIN.S(qNaN 0x7FC00001, 1.0) | 0x3F800000 | 0x7FC00001 |
  | FMIN.S(0x7FC00002, 0x7FC00001) | 0x7FC00000 | 0x7FC00002 |
  | FMIN.D(+0,-0) / FMAX.D(+0,-0) | 0x8000000000000000 / 0x0 | 0x0 / 0x8000000000000000 |
  | FMIN.D(sNaN 0x7FF0000000000001, 1.0) | 0x3FF0000000000000, NV | 0x7FF8000000000000, no flag |
  | FMIN.D(0x7FF8000000000001, 1.0) | 0x3FF0000000000000 | 0x7FF8000000000001 |
  | FMAX.D(0x7FF8000000000001, 0x7FF8000000000002) | 0x7FF8000000000000 | 0x7FF8000000000001 |

  These cases are correct in L3: FMIN(1,2)=1, FMAX(1,2)=2, FMIN(-0,+0)=-0, FMAX(canonNaN,1)=1.
- **Fix** (FMAX swaps the two choices; the D forms are analogous):
  ```
  define FArith > FMIN_S(rd::reg, rs1::reg, rs2::reg) =
  { f1 = FPRS(rs1)
  ; f2 = FPRS(rs2)
  ; when FP32_IsSignalingNan(f1) or FP32_IsSignalingNan(f2) do setFP_Invalid()
  ; res = if FP32_IsNan(f1) and FP32_IsNan(f2) then RV32_CanonicalNan
          else if FP32_IsNan(f1) then f2
          else if FP32_IsNan(f2) then f1
          else if FP32_IsZero(f1) and FP32_IsZero(f2) then (if FP32_Sign(f1) then f1 else f2)
          else if FP32_LessThan(f1, f2) then f1 else f2
  ; writeFPRS(rd, res)
  }
  ```
- **Resolution:** cef25b0fa (the proposed fix).

#### F9. The FMA family is not fused, and FNMADD/FNMSUB negate the rounded result

- **L3:** FMADD_S, FMSUB_S, FNMADD_S and FNMSUB_S at 3303-3345, and the D forms at 3754-3796.
  FMADD is `FP32_Add(r, FP32_Mul(r, a, b), c)`, FMSUB uses `FP32_Sub`, FNMADD is
  `FP32_Neg(FP32_Add(…))` and FNMSUB is `FP32_Neg(FP32_Sub(…))`. The D forms use the FP64_\*
  equivalents.
- **Problem:** There are two defects, and one fix covers both.
  - **(a) Not fused.** The product is rounded before the addend is applied, so results are
    wrong, including in sign, when cancellation occurs. L3 already has fused primitives,
    `FP32_MulAdd`/`FP32_MulAdd_` and the FP64 versions (L3 `Base.sml` 3910-3960). HolExport
    maps them to the HOL mul_add, and the SML runtime has `FP32.mul_add`. The spec does not use
    them.
  - **(b) Negation applied after rounding.** The manual defines FNMSUB = −(a·b)+c and
    FNMADD = −(a·b)−c with a single rounding. L3 computes −round(a·b ± c). That gives the wrong
    sign of zero, and it mirrors the directed rounding modes, because round_up(−x) ≠ −round_up(x).
- **Expected:**
  - Manual §6.1.6 calls these fused multiply-add instructions: "FNMSUB.S computes −(rs1×rs2)+rs3"
    and "FNMADD.S computes −(rs1×rs2)−rs3". The commentary notes that MIPS negates the sum, and
    "The two definitions differ with respect to signed-zero results".
  - sail `fext_insts.sail:375-378` and `dext_insts.sail:279-282` make one
    `riscv_f32MulAdd`/`riscv_f64MulAdd` call with negated inputs.
- **Test** (executed in L3: `fparith/t4.sml`, `fma-refute1/2`, `refute-fnma1/2`; executed in
  `sail_riscv_sim`: `refute-fnma1/fn.S`, `refute-fnma2/t.S`). All cases use rm=RNE unless
  stated.
  - **(a)** f1=0x3F800001 (1+2^-23), f2=0x3F7FFFFE (1−2^-23). The exact product is 1−2^-46.

    | Instruction | Addend | Expected | L3 |
    |---|---|---|---|
    | FMADD.S f3,f1,f2,f4 (0x202081C3) | −1.0 | 0xA8800000 | 0x00000000 |
    | FMSUB.S | +1.0 | 0xA8800000 | 0x00000000 |
    | FNMSUB.S | +1.0 | 0x28800000 | 0x80000000 |
    | FNMADD.S | −1.0 | 0x28800000 | 0x80000000 |
    | FMADD.S, rm=RTZ | −1.0 | 0xA8800000 | 0xB3800000 |
    | FMADD.D (0x222081C3) with 1±2^-52 | −1.0 | 0xB970000000000000 | 0x0 |

    For the FMADD.S row, the host `FP32.mul_add` returns 0xA8800000.
  - **(b)** The products here are exact, so these cases are independent of (a). Expected values
    come from sail.

    | Instruction | Inputs | Expected | L3 |
    |---|---|---|---|
    | FNMSUB.S (0x202081CB) | 1, 1, 1 | +0 (sail 0xFFFFFFFF00000000) | 0x80000000 |
    | FNMSUB.D (0x222081CB) | 1, 1, 1 | 0x0 | 0x8000000000000000 |
    | FNMADD.S, RUP (0x2020B1CF) | 1, 1, 2^-24 | 0xBF800000 | 0xBF800001 |
    | FNMADD.D, RUP (0x2220B1CF) | 1, 1, 2^-60 | 0xBFF0000000000000 | 0xBFF0000000000001 |
- **Fix** (a=FPRS(rs1), b=FPRS(rs2), c=FPRS(rs3); the D forms use FP64):
  ```
  FMADD_S  : FP32_MulAdd_(r, a, b, c)
  FMSUB_S  : FP32_MulAdd_(r, a, b, FP32_Neg(c))
  FNMSUB_S : FP32_MulAdd_(r, FP32_Neg(a), b, c)
  FNMADD_S : FP32_MulAdd_(r, FP32_Neg(a), b, FP32_Neg(c))
  ```
  Then accrue the returned flags (F11), add the explicit ∞×0 check (F12), and canonicalise the
  value (F10). Negating the operands rather than the result also stops a NaN result from having
  its sign flipped.
- **Resolution:** e40dd7ee2 (the proposed `MulAdd_` calls, flags accrued: F11's part for the FMA family).

#### F10. NaN results are not the canonical NaN

- **L3:**
  - Arithmetic writes the primitive's result unchanged: 3210-3258 and 3303-3345 (S), 3660-3710
    and 3754-3796 (D).
  - FCVT.S.D (3936-3941) and FCVT.D.S (3947-3953) write the conversion's result unchanged.
  - `RV32_CanonicalNan`/`RV64_CanonicalNan` (846-847) are used only by FMIN/FMAX/FCLASS.
- **Problem:** The NaN that ends up in the register depends on the export.
  - **SML export:** Arithmetic produces the x86 default NaN 0xFFC00000 / 0xFFF8000000000000,
    which is negative. NaN operands pass through with their payload, and x86 cvtss2sd/cvtsd2ss
    keep both payload and sign.
  - **HOL export:** Arithmetic gives `float_some_qnan`, a Hilbert choice of some quiet NaN
    (`binary_ieeeScript.sml:495-498`). Conversions give `from_float (@fp. float_is_nan fp)`
    (`machine_ieeeScript.sml`, `convert_def`). Either way the register value is unspecified
    (F27).
  - The FNM\* forms then negate the result, flipping a NaN's sign.
  - A program sees all of this through FMV.X.W/FMV.X.D, FSGNJ or a store.
- **Expected:**
  - Manual §6.1.3: "Except when otherwise stated, if the result of a floating-point operation is
    NaN, it is the canonical NaN": 0x7FC00000 for single, 0x7FF8000000000000 for double (§6.2).
    FCVT.S.D and FCVT.D.S are not exempt.
  - sail uses softfloat's RISCV specialisation (`specialize.h`: `defaultNaNF32UI` 0x7FC00000,
    `defaultNaNF64UI` 0x7FF8000000000000). `canonical_NaN` is at `fdext_regs.sail:21`.
- **Test** (executed in L3: `fparith/t1.sml`, `t2.sml`, `fparith-refute1`, `refuter2-fpnan`,
  `fcvt-sd-nan-refute1`, `refuter2-fpconv-nan`). Rows marked (S) were also run on
  `sail_riscv_sim` (`fparith-refute1/t.S`, `fcvt-sd-nan-refute1/t.S`).

  | Case | Expected | L3 |
  |---|---|---|
  | FDIV.S f3,f1,f2 (0x182081D3) 0/0 (S) | 0x7FC00000 | 0xFFC00000 |
  | FSUB.S inf−inf; FSQRT.S −1 | 0x7FC00000 | 0xFFC00000 |
  | FADD.S 0x7FC00001 + 1.0 (S) | 0x7FC00000 | 0x7FC00001 |
  | FADD.S sNaN 0x7F800001 + 1.0 (S) | 0x7FC00000, NV | 0x7FC00001, no NV |
  | FDIV.D 0/0; FMUL.D inf·0; FSQRT.D −1 (S for fsqrt) | 0x7FF8000000000000 | 0xFFF8000000000000 |
  | FADD.D 0x7FF8000000000001 + 1.0 (S) | 0x7FF8000000000000 | 0x7FF8000000000001 |
  | FNMADD.S 1·1 + 0x7FC00000 | 0x7FC00000 | 0xFFC00000 |
  | FCVT.D.S f3,f1 (0x420081D3), boxed 0x7FC00001 (S) | 0x7FF8000000000000 | 0x7FF8000020000000 |
  | FCVT.D.S, sNaN 0x7F800001 (S) | 0x7FF8000000000000, NV | 0x7FF8000020000000, no NV |
  | FCVT.D.S, 0xFFC12345 | 0x7FF8000000000000 | 0xFFF82468A0000000 |
  | FCVT.S.D f3,f1 (0x401081D3), 0x7FF8000020000000 (S) | 0xFFFFFFFF7FC00000 | 0x7FC00001 |
- **Fix:** Add
  `bits(32) canonS(x::bits(32)) = if FP32_IsNan(x) then RV32_CanonicalNan else x` and a matching
  `canonD`. Wrap the results of:
  - FADD, FSUB, FMUL, FDIV and FSQRT;
  - the FMA family, after F9;
  - FCVT.S.D;
  - FCVT.D.S, which must also call `setFP_Invalid()` on an sNaN input.

  Do not wrap FSGNJ\*, FMV\*, FLW/FLD/FSW/FSD: those are defined to be bit-exact. Doing this in
  the spec also makes the HOL next-state value concrete (F27).
- **Resolution:** a88125e3d (`canonS`/`canonD`); FCVT.D.S raises NV on an sNaN since d40724833 (F11).

#### F11. No F/D instruction other than FEQ/FLT/FLE ever sets fflags

- **L3:**
  - Arithmetic (3210-3345, 3660-3796) uses the value-only primitives `FP32_Add`, `FP32_Sub`,
    `FP32_Mul`, `FP32_Div` and `FP32_Sqrt`, and their FP64 versions. In the export these are
    `(L3.snd o FP32.add)` and so on (riscv.sml 7128-7229, 7618-7720), so the flags the host
    computes are thrown away.
  - Conversions (3349-3480, 3800-3953) never touch fcsr. FCVT.S.D uses the flag-less
    `FP64_ToFP32`.
  - The only flag writes in the whole spec are the `setFP_Invalid()` calls at 3540, 3561, 3582,
    4013, 4034 and 4055 (FEQ/FLT/FLE).
- **Problem:** fflags, as read by fetestexcept, or by lrint followed by an FE_INEXACT check, is
  always 0 after arithmetic and conversions. The flags that are never raised are:
  - from arithmetic: NV, DZ, OF, UF and NX;
  - from float→int: NV (NaN, ±inf, out of range) and NX;
  - from int→float: NX;
  - from FCVT.S.D: NV, OF, UF and NX;
  - from FCVT.D.S: NV for an sNaN input.
- **Expected:**
  - Manual §6.1.2 (accrued exception flags). Manual §6.1.7: "If the rounded result is not
    representable in the destination format, it is clipped to the nearest value and the invalid
    flag is set" and "All floating-point conversion instructions set the Inexact exception flag
    if the rounded result differs from the operand value and the Invalid exception flag is not
    set."
  - sail: every execute clause in `fext_insts.sail` and `dext_insts.sail` does
    `let (fflags, rd_val) = riscv_f32…(…)` followed by `accrue_fflags(fflags)`
    (`fdext_regs.sail:447`).
- **Test** (executed; fcsr cleared before each case; `fparith/t1.sml`, `t2.sml`,
  `fparith-nofflags-refute1`, `fparith-ref2`, `fconv/t.sml`, `fconv-fflags-refute1`,
  `fconv-nofflags-refute2`). Control: FEQ.S sNaN,1.0 gives fcsr=0x10, so flags are observable.
  In every case below L3 leaves fcsr=0. Numeric results are correct unless another finding says
  otherwise.

  | Case | Expected fflags |
  |---|---|
  | FDIV.S f3,f1,f2 (0x182081D3) 1.0/+0 | DZ 0x08 |
  | FDIV.S 0/0; FSUB.S inf−inf; FSQRT.S −1; FMADD.S inf·0+1 | NV 0x10 |
  | FMUL.S 0x7F7FFFFF · 2.0 | OF\|NX 0x05 |
  | FADD.S 1.0 + 2^-30 | NX 0x01 |
  | FMUL.S 2^-126 · 2^-126 | UF\|NX 0x03 |
  | FADD.D sNaN+1, FDIV.D 1/0, FMUL.D inf·0, FADD.D 1+2^-60, FSQRT.D −1 | NV, DZ, NV, NX, NV |
  | FCVT.W.S x3,f1 (0xC00081D3), 1.5 | NX (x3=2) |
  | FCVT.W.S 3e9 | NV (x3=0x7FFFFFFF) |
  | FCVT.L.S (0xC02081D3), 2^63 | NV |
  | FCVT.WU.S −1.0 | NV (x3=0) |
  | FCVT.W.D rdn (0xC200A1D3), −2147483648.5 | NV |
  | FCVT.S.W 16777217; FCVT.D.L 2^53+1; FCVT.S.D 0.1 | NX |
  | FCVT.S.D 1e300 | OF\|NX (f3=0x7F800000) |
  | FCVT.S.D 1e-300 | UF\|NX (f3=0) |
  | FCVT.D.S sNaN 0x7F800001 | NV |

  Called directly, the host primitives return the right flags (e.g. `FP32.div` 1/0 gives DZ), so
  the information exists and is dropped.
- **Fix:**
  - Add a helper. The field names are those of L3's `ieee_flags` record (`Base.sml` 1036-1042):
    ```
    unit accrueFlags(f::ieee_flags) =
    { when f.InvalidOp    do fcsr.NV <- true
    ; when f.DivideByZero do fcsr.DZ <- true
    ; when f.Overflow     do fcsr.OF <- true
    ; when f.Underflow    do fcsr.UF <- true
    ; when f.Precision    do fcsr.NX <- true
    }
    ```
  - **Arithmetic and FCVT.S.D:** use the flag-returning primitives
    `FP32_{Add,Sub,Mul,Div,Sqrt,MulAdd}_`, the FP64 versions and `FP64_ToFP32_` (all listed in
    `Base.sml` 3885-3960; they return `ieee_flags * value`). For example:
    `match FP32_Add_(r, a, b) { case (f, v) => { accrueFlags(f); writeFPRS(rd, canonS(v)) } }`.
    For the FMA family use the fused `MulAdd_` (F9). Calling `Mul_` and then `Add_` would accrue
    intermediate flags that fused hardware does not raise.
  - **Float→int:** set NV when the input is NaN or ±inf, or out of range after rounding.
    Otherwise set NX when `not FP32_IsIntegral(inp)` (or the FP64 version).
  - **Int→float:** there is no flag-returning FromInt. Set NX when the result does not convert
    back exactly, e.g. `ValOf(FP32_ToInt(roundTowardZero, res)) != i`. This never fires for
    FCVT.D.W[U].
  - **FCVT.D.S:** set NV on an sNaN input (F10).
  - **Tininess:** manual §6.1.4 detects tininess after rounding. The HOL import already uses
    `Underflow_AfterRounding` for RISC-V (`common/Import.sml:395`; `ieee_underflow_before`
    defaults to false and only arm/arm8 set it), and x86 SSE also detects tininess after
    rounding (SoftFloat's 8086-SSE specialisation uses `afterRounding`). So UF agrees between
    the two exports.
  - Do not use `setFP_Underflow`/`setFP_Inexact` until F18 is fixed.
- **Resolution:** d40724833 (`accrueFlags`; FMA family in e40dd7ee2). FSQRT accrues no flag for a quiet NaN input, because HOL's `float_sqrt` raises NV for a negative one. Float-to-int NV/NX and int-to-float NX are computed in the spec, as L3's SML `toInt`/`fromInt` return no flags.

#### F12. The FMA family raises no NV for ∞×0 + qNaN

- **L3:** 3303-3345 and 3754-3796.
- **Problem:** The manual requires NV here, and switching to the fused, flag-returning primitive
  (F9, F11) does not supply it.
  - HOL `float_mul_add` (`binary_ieeeScript.sml:692-704`) checks for NaN operands first and
    returns `check_for_signalling [x;y;z]`, which raises NV only for an sNaN.
  - The x86 FMA behaves the same: `FP32.mul_add(RNE, inf, 0, 0x7FC00000)` and its FP64 version
    return InvalidOp=false. With addend 1.0 they do return InvalidOp=true.
  - The FMADD/FMSUB result is also the non-canonical 0xFFC00000 (F10).
- **Expected:**
  - Manual §6.1.6: "The fused multiply-add instructions must set the invalid operation exception
    flag when the multiplicands are ∞ and zero, even when the addend is a quiet NaN."
  - sail calls softfloat `f32_mulAdd`; in `s_mulAddF32.c` the `infProdArg` path raises invalid
    and returns the default NaN.
- **Test** (executed; `fparith/t4.sml`, `refute-fma-nv/t.sml`, `t2.sml`, `fma-nv-refute2`).
  - FMADD.S f3,f1,f2,f4 rne (0x202081C3) with f1=boxed +inf, f2=+0, f4=boxed 0x7FC00000.
    Expected f3=0xFFFFFFFF7FC00000 and fcsr=0x10. L3 gives f3=0x00000000FFC00000 and fcsr=0.
    FMSUB.S behaves the same.
  - FNMADD.S and FNMSUB.S give 0x7FC00000, canonical only because the negation flips the x86
    NaN's sign, and fcsr=0.
  - FMADD.D (0x222081C3) with +inf, 0, 0x7FF8000000000000. Expected 0x7FF8000000000000 with NV.
    L3 gives 0xFFF8000000000000 with fcsr=0.
  - 0 × (−inf) behaves the same way.
- **Fix:** Before the `MulAdd_` call, add
  `when ((a == FP32_PosInf or a == FP32_NegInf) and FP32_IsZero(b)) or (FP32_IsZero(a) and (b == FP32_PosInf or b == FP32_NegInf)) do setFP_Invalid()`.
  Use FP64 for the D forms, with a and b being the multiplicands after the F9 negation. Then
  apply F9, F10 and F11.
- **Resolution:** 73fd68ae8 (the proposed check, as `FP32_InfTimesZero`/`FP64_InfTimesZero`).

#### F13. Rounding mode RMM raises illegal instruction

- **L3:**
  - `rnd_mode_static` (800-809) and `rnd_mode_dynamic` (812-820) map 4 to RMM correctly.
  - `l3round` (823-831) then has `case RMM => None -- roundTiesToMaxMagnitude not in L3`, and
    `round` (834-843) passes the None through.
  - Every define with an fprnd field turns None into `signalException(Illegal_Instr)`, e.g.
    FADD_S 3210, FMADD_S 3303, FCVT_W_S 3371, FCVT_D_W 3800, FCVT_D_S 3947.
  - Decode accepts rm=100.
  - Root cause: L3's `ieee_rounding` (`Base.sml:1043-1045`) and HOL's binary_ieee `rounding`
    (`binary_ieeeScript.sml:246-250`) each have only four modes.
- **Problem:** Every F/D instruction with an rm field traps when rm=100, or when rm=111 and
  frm=100. That includes the always-exact FCVT.D.S, FCVT.D.W and FCVT.D.WU. Compiled code does
  this: `riscv64-unknown-elf-gcc -O2 -fno-math-errno` turns `__builtin_lround(double)` into
  `fcvt.l.d a0,fa0,rmm`.
- **Expected:**
  - Manual §6.1.2, rounding-mode table: 100 = RMM, "Round to Nearest, ties to Max Magnitude".
    Only 101 and 110 are reserved, plus 111 when it appears in frm. Instructions unaffected by
    rounding "must treat the rm field as usual".
  - sail `fext_insts.sail`: `encdec_rounding_mode` maps RM_RMM to 0b100 (line 36),
    `valid_rounding_mode` rejects only 101/110 (49), and `select_instr_or_fcsr_rm` (51) accepts
    RMM.
- **Test** (executed in L3: `inventory/exec.sml`, `inventory-rmm-refute1/2`, `rmm-refute1`,
  `fpconv-rmm-refute1`; executed in `sail_riscv_sim`: `inventory-rmm-refute2/t.elf`). Inputs:
  f2=boxed 1.0f, f3=2^-24 (0x33800000), f4=1.0d, f5=2^-53, x2=7. "Trap" means Illegal_Instr
  with the destination unchanged.

  | Instruction | Expected ((S) = sail run) | L3 |
  |---|---|---|
  | fadd.s f1,f2,f3,rmm (0x003140D3) | 0xFFFFFFFF3F800001, NX (S) | trap |
  | fadd.d f1,f4,f5,rmm (0x025240D3) | 0x3FF0000000000001 (S) | trap |
  | fcvt.d.s f1,f2,rmm (0x420140D3) | 0x3FF0000000000000 (S) | trap |
  | fcvt.d.w f1,x2,rmm (0xD20140D3) | 0x401C000000000000 (S) | trap |
  | fadd.s rm=dyn (0x003170D3), frm=100 | 0xFFFFFFFF3F800001 (S) | trap (runs with frm=000) |
  | fcvt.w.s x3,f1,rmm (0xC000C1D3), f1=2.5 | 3, NX | trap |
  | fcvt.l.d x3,f1,rmm (0xC220C1D3), f1=−2.5 | −3 | trap |

  Control: rm=101 traps in both models, which is correct.
- **Fix:**
  - **Preferred:** add roundTiesToAway (IEEE 754-2008) to HOL `binary_ieee` (`rounding`,
    `float_round`, and so to `machine_ieee`) and to L3's `ieee_rounding`, then map
    `case RMM => Some(roundTiesToAway)`. The binary_ieee part is a HOL-fixes change to
    upstream. The SML runtime cannot do it with SSE/IEEEReal, so it needs a software path, such
    as a softfloat binding (see F30).
  - **Interim, in the spec:**
    - Exact conversions (FCVT.D.S, FCVT.D.W, FCVT.D.WU) should accept RMM and ignore the mode.
    - Float→int can emulate RMM: `if FP32_IsIntegral(x) then RTZ(x) else if FP32_IsIntegral(FP32_Add(RNE, x, x)) then (if sign then RDN else RUP)(x) else RNE(x)`.
      A tie is exactly the case where 2x is an integer, and doubling a non-integral finite x is
      exact.
    - Arithmetic and int→float have no cheap exact emulation. Until HOL/L3 support RMM, document
      it as an explicit limitation in the spec.
- **Resolution:** exact conversions only: 6c8774b88 (FCVT.D.S/D.W/D.WU accept RMM via `validRounding`). Deferred: RMM elsewhere still raises illegal instruction, since neither HOL's binary_ieee nor L3's FP library has roundTiesToAway.

### 2.2 Missing

None. Every RV64GC encoding in riscv-opcodes (`rv_i`, `rv64_i`, `rv_m`, `rv64_m`, `rv_a`,
`rv64_a`, `rv_f`, `rv64_f`, `rv_d`, `rv64_d`, `rv_zicsr`, `rv_zifencei`, `rv_c`, `rv64_c`,
`rv_c_d`) decodes to the correct constructor with the correct operands (§3).

### 2.3 Deviations

#### F14. CSRRWI with zimm=0 on a read-only CSR does not trap

- **L3:** 4172 uses access type Read when zimm=0. That reaches `checkCSROp` (4130-4131) and
  `check_CSR_access` (891-892), `(a == Read or rw != 0b11) and …`, so the read-only test on
  csr<11:10> is skipped.
- **Problem:** `csrrwi rd,cycle,0`, and the same for `time`, `instret` and the other
  csr<11:10>=11 CSRs, retires and returns the counter value. It should raise an
  illegal-instruction trap. This is reachable from U-mode.
- **Expected:**
  - Manual §4.2.1: only CSRRS/CSRRC with rs1=x0 and CSRRSI/CSRRCI with uimm=0 are exempt from
    the read-only trap. CSRRWI always writes, and writing a read-only CSR raises an
    illegal-instruction exception.
  - sail `csr_access_type` (`zicsr_insts.sail:35-36`) gives CSRWrite or CSRReadWrite, and
    `sys/sys_control.sail` `check_CSR_access` rejects writes when csr[11..10]==0b11.
- **Test** (executed in L3: `zicsr/tests.sml` T3, `zicsr-csrrwi-ro-refute1/t.sml`; executed in
  `sail_riscv_sim`: `zicsr-csrrwi-ro-refute1/t.elf`). `csrrwi x1,cycle,0` (0xC00050F3) with
  x1=0x55, run in U-mode and in M-mode:
  - L3 retires it: PC+4, and x1 = the cycle value (0).
  - Sail traps with mcause=2, mtval=0xC00050F3, and x1=0x55 unchanged.
  - The same happens for time (0xC01) and instret (0xC02).
  - Controls that do trap in L3: `csrrwi x1,cycle,1` and `csrrw x1,cycle,x0`.
- **Fix:** The F1 change, with no extra work.

#### F15. C.ADDIW with rd=x0 (reserved) is accepted and runs as a nop

- **L3:** DecodeRVC 4996:
  ```
  case '001 i5`1 r imi`5 01' => ArithI(ADDIW( r, r, i5 ^ 7 : imi))
  ```
  No earlier case catches rd=0. The other reserved RVC points do have `UnknownInstruction`
  cases: c.addi4spn with zero immediate (4982), c.addi16sp with zero immediate (4998), c.lui with
  zero immediate (5001), c.lwsp and c.ldsp with rd=0 (5024, 5026), and c.jr with rs1=0 (5029).
- **Problem:** The 64 halfwords with bits[15:13]=001, bits[11:7]=0 and bits[1:0]=01 (0x2001,
  0x2005, …, 0x307D) decode as `ADDIW x0,x0,imm` and retire as nops.
- **Expected:**
  - Manual §7.1.4.2: "C.ADDIW is valid only when rd≠x0; the code points with rd=x0 are
    reserved."
  - sail `zca_insts.sail:155-157` (`when rsd != zreg & xlen == 64 & …`). These words fall
    through to `C_ILLEGAL` (`postlude/insts_end.sail`, `Illegal_Instruction()`).
  - riscv-opcodes `rv64_c` lists `c.addiw rd_rs1_n0`, and objdump prints these words as `.insn`.
  - The manual leaves the behaviour of reserved encodings UNSPECIFIED, so the trap is Sail's
    choice. It is also how L3 treats every other reserved RVC point, and the WP5 comparison
    diffs against Sail.
- **Test** (executed; `rvc-decode/diff.txt`, `exec.sml`, `caddiw-refute1/2`,
  `refute-c-addiw{,-1}`).
  - 0x2005 (c.addiw x0,1) at PC 0x1000 with C enabled: L3 decodes `ADDIW $0,$0,0x1`, retires,
    and gives PC=0x1002 with mcause 0. Expected: an illegal-instruction trap (mcause 2).
  - 0x2001 and 0x307D behave the same.
  - In the exhaustive check, these 64 are the only halfwords that differ.
  - Controls: 0x0000 and 0x4002 trap.
- **Fix:** Insert this before line 4996, in the style of 5024:
  ```
  case '001 i5`1 00000 imi`5 01' => UnknownInstruction
  ```
  `riscv_stepLib` enumerates `DecodeRVC_def` with `find_all_rvc` (`step/riscv_stepLib.sml:111`),
  so rebuild it and check that the RVC theorem names it produces still suit downstream users.
- **Resolution:** 74c59d9b4; `riscv_dict` gains five unused RVC patterns, step theorems unchanged.

#### F16. Misaligned LR.W/LR.D raise cause 6 instead of a load exception

- **L3:** LR_W 2738-2739 and LR_D 2755-2756 both call `signalAddressException(AMO_Misaligned, vAddr)`.
  `ExceptionType` (271-283) has no load-address-misaligned constructor, and `excCode` (285-299)
  skips 0x4. A translation failure in LR does correctly raise Load_Fault (cause 5).
- **Problem:** A misaligned LR traps with cause 6 (store/AMO address misaligned). The spec
  cannot raise cause 4 at all.
- **Expected:**
  - Manual §5.2: a misaligned LR/SC raises "an address-misaligned exception or an access-fault
    exception".
  - Privileged manual, mcause section: "load and load-reserved instructions generate load
    exceptions, whereas store, store-conditional, and AMO instructions generate store/AMO
    exceptions."
  - sail `sys/vmem_utils.sail` `vmem_read_addr` (≈201-206) returns E_Load_Addr_Align or
    E_Load_Access_Fault, with the comment "LR faults like a normal load". The cause 6 that L3
    raises for SC and AMO is correct.
- **Test** (executed; `amo-audit` T7/T7b, `lr-misalign-refute1`, `refuter2-a-lr`).
  - LR.W x1,(x2) (0x100120AF) with x2=0x10002 or 0x10001: L3 traps with mcause 6, mbadaddr =
    vAddr, x1 unchanged.
  - LR.D x1,(x2) (0x100130AF) with x2=0x10004: same.
  - Expected for both: cause 4 (or 5).
  - Aligned controls load correctly, and a misaligned SC.W gives cause 6, which is correct.
- **Fix:** Add `Load_Misaligned` to `ExceptionType` with `excCode` 0x4, add it to the reverse map
  `excType` (302) and to `excName` (321), and use it in LR_W/LR_D. WP2 rewrites `ExceptionType`
  anyway, and WP2.5 needs cause 4 for ordinary loads too (F28). Raising Load_Fault (cause 5) is
  an interim alternative that the manual allows.

#### F17. Obsolete priv-1.7 SYSTEM words decode and execute from U-mode

- **L3:**
  - Decode lines:

    | Line | Pattern | Decodes to |
    |---|---|---|
    | 4473 | 0x10000073 | ERET |
    | 4474 | 0x30500073 | MRTS |
    | 4475 | 0x10200073 | WFI |
    | 4477 | 0x10100073 \| rs1<<15 | SFENCE_VM |

  - Semantics:
    - ERET (4107-4108) sets `NextFetch <- Some(Ereturn)`.
    - MRTS (4113-4121) copies mcause, mbadaddr and mepc into the S CSRs, sets `mstatus.MPRV`
      (the priv-1.7 current-privilege field read by `curPrivilege`, 772-773) to Supervisor, and
      sets `NextFetch <- Some(Mrts)`.
    - WFI (4126) is `nothing`.
    - SFENCE_VM (4209-4212) flushes the TLB.
  - None of these checks the privilege level.
  - In `Next`, `Some(Ereturn)` (5331-5341) evaluates `PC <- curEPC()`, and `curEPC` (775-781) is
    `#INTERNAL_ERROR("No EPC in U-mode")` for User. `Some(Mrts)` (5348-5352) jumps to
    `SCSR.stvec`.
- **Problem:** Each of these words executes without a privilege check from U-mode, in the
  current manual a reserved word or SRET:
  - **0x30500073:** the hart moves to Supervisor and jumps to stvec, with no trap. A reserved
    word escalates privilege.
  - **0x10000073:** `Next` aborts with L3 `INTERNAL_ERROR "No EPC in U-mode"`, so the HOL step
    has no defined next state. This is `#INTERNAL_ERROR` reachable from user code. It does not
    pop the privilege stack, as the original audit text claimed; that audit ran only `Run`, not
    `Next`.
  - **0x10200073** (SRET today) and **0x101xx073:** retire as nops.
- **Expected:**
  - The current encodings are MRET 0x30200073, SRET 0x10200073, WFI 0x10500073 and SFENCE.VMA
    `0001001 rs2 rs1 000 00000 1110011` (riscv-opcodes `rv_system`, `rv_s`; sail
    `base_insts.sail`).
  - No encdec clause anywhere under sail `model/` matches funct12 0x100, 0x305 or 0x101/rs1, so
    those words are ILLEGAL (`postlude/insts_end.sail`). SRET from U-mode sets `sret_illegal`
    and raises Illegal_Instruction.
- **Test** (executed with full `Next`; `inventory/exec_priv.sml`,
  `inventory-legacysys-refute1/t.sml`, `inventory-priv17-refute2/next_priv.sml`). The word is at
  0x80000000, with priv=User, stvec=0x4000 and mepc=0x5000.
  - 0x30500073: `Next` returns with privilege Supervisor and PC=0x4000.
  - 0x10000073: `Next` raises INTERNAL_ERROR and PC is unchanged.
  - 0x10200073, 0x10128073 and 0x10100073: nops, PC+4, still User.
  - Expected for all of them: Illegal_Instr (mcause 2).
  - Controls: 0x30200073 and 0x10500073 trap with mcause 2, and 0x00000073 traps with mcause 8.
- **Fix:** In WP2, delete Decode lines 4473-4477 and add MRET, SRET, WFI and SFENCE.VMA with
  their modern encodings and privilege checks. Until then, the minimum is a guard in both ERET
  and MRTS: `if curPrivilege() == User then signalException(Illegal_Instr) else …`. The ERET
  guard matters most, since that path aborts the model.

### 2.4 Notes

#### F18. setFP_Underflow and setFP_Inexact set OF

- **L3:** 871-875. Both helpers do `fcsr.OF <- true`. The FPCSR layout (502-510) is NV=bit 4,
  DZ=3, OF=2, UF=1, NX=0. They are exported as `setFP_Underflow_def` and `setFP_Inexact_def`
  (riscvScript.sml 1644, 1656). Nothing calls them; only `setFP_Invalid` is used.
- **Expected:** sail `fext_insts.sail:68-72` has `ufFlag()=0b00010` and `nxFlag()=0b00001`;
  `accrue_fflags` ORs these into FFLAGS.
- **Test** (executed; each helper called directly from fflags=0; `fparith-setfp-refute1`,
  `setfp-uf-nx-refute1`, `zicsr/tests5.sml`). Underflow gives 0x4 (expected 0x2), Inexact gives
  0x4 (expected 0x1). Invalid 0x10, DivZero 0x8 and Overflow 0x4 are correct.
- **Fix:** Line 872 `fcsr.UF <- true` and line 875 `fcsr.NX <- true`, or replace all the helpers
  with `accrueFlags` (F11).
- **Resolution:** 08bf3ba96 (the proposed fix).

#### F19. Writing fcsr stores the reserved bits 31:8

- **L3:** 1046, `case 0x003 => { c_UCSR(procID).&fpcsr <- value<31:0> …`. Reads mask the value
  (931-933), so no program can see the extra bits. They do land in the hidden 24-bit field
  `fpcsr'rst` (riscv.sig line 86; riscvScript.sml:97, `("fpcsr'rst", FTy 24)`), so two HOL
  states can differ only in that field. An instruction with no architectural effect, such as
  `csrrs` on fcsr with x2=0xFFFFFF00, still changes the model state. Today stepLib and prog never
  mention fpcsr; the cost falls on future WP3/WP4 frame reasoning.
- **Expected:**
  - Manual §6.1.2: "Bits 31–8 of the fcsr are reserved for other standard extensions. If these
    extensions are not present, implementations shall ignore writes to these bits and supply a
    zero value when read."
  - sail `fdext_control.sail:44`: `write_fcsr(value[7..5], value[4..0])`.
- **Test** (executed; `zicsr/tests.sml` T6, `fcsr-rst-refute1/2`). With x2 = all ones,
  `csrrw x1,fcsr,x2` (0x003110F3) then `csrrs x3,fcsr,x0` (0x003021F3) gives x3=0xFF, which is
  correct. The stored word is 0xFFFFFFFF; expected 0xFF.
- **Fix:** `c_UCSR(procID).&fpcsr <- ZeroExtend(value<7:0>)`.

#### F20. `inline writeRD` re-evaluates its argument: SML DIV/REM/REMU crash, and Delta.data1 is wrong

- **L3:** `inline unit writeRD` at 1623-1626 uses `val` twice. The SML export evaluates the
  second copy, for `Delta.data1`, after the GPR write:
  - DIV (2343-2347), REM (2351-2355) and REMU (2370-2374) pass an unbound
    `GPR(rs1) quot/rem/mod GPR(rs2)`. See riscv.sml dfn'DIV 5150-5169, dfn'REM 5171-5188 and
    dfn'REMU 5221-5238.
  - `BitsN.quot/rem/mod` (`BitsN.sml` 225-232) call `IntInf.quot/rem/mod` with no zero check, so
    a zero divisor raises SML `Div`. `Next` has no handler for it.
- **Problem:**
  - **Crash:** with rd==rs2 and a result of 0, or with rd==rs1==rs2 for REM/REMU, the SML
    emulator stops with a `Div` exception. Register results are always correct.
  - **Wrong trace data:** every unbound writeRD use with rd aliasing a source gets a wrong
    Delta.data1, for example MUL and ADD.
  - **Not affected:** DIVU, the W forms and MULH/MULHU/MULHSU, which let-bind their operands or
    result. The HOL export is unaffected too, because PROVER_EXPORT removes the Delta write and
    `dfn'DIV_def` has a single `write'GPR`.
  - **Why it matters:** per-step comparison against Sail (WP0/WP5) would crash on ordinary
    compiler output such as `div a1,a0,a1`.
- **Expected:** Manual §4.5 says no exception is raised on divide by zero. sail
  `mext_insts.sail` DIV/REM read `X(rs1)` and `X(rs2)` once, before writing `X(rd)`.
- **Test** (executed; `mext/t7.sml`, `run.sml`, `m-divdelta-refute1`, `mext-wrd-refute2`).
  - DIV x2,x1,x2 (0x0220C133) with x1=4, x2=7: x2 becomes 0, then SML `Div` escapes from `Run`.
  - REMU x2,x1,x2 (0x0220F133) and REM x2,x1,x2 (0x0220E133) with x1=4, x2=2: same.
  - REM x31,x31,x31 (0x03FFEFB3) with x31=1, and REMU x31,x31,x31 (0x03FFFFB3) with x31=5: same.
  - DIV x2,x1,x2 with x1=14, x2=7: no exception, x2=2, but Delta.data1=7.
  - MUL x1,x1,x2 (0x022080B3) with 3 and 5: x1=0xF, but Delta.data1=0x4B.
  - The 95,836-case M run hit 1,367 such exceptions, and every destination value was correct.
- **Fix:** There are two ways, and they change the HOL export differently:
  - Drop `inline` from writeRD. writeRD then becomes a HOL constant used by every `dfn'*`, so
    add `writeRD_def` to riscv_stepLib's rewrites.
  - Let-bind the value in each caller, e.g. DIV: `{ q = GPR(rs1) quot GPR(rs2); writeRD(rd, q) }`.
    This keeps the HOL export's shape.

  Either way, check that the regenerated riscvScript.sml is unchanged or alpha-equivalent.
- **Resolution:** f4bf99282, by a third way: writeRD binds `v = val`; riscvScript.sml is unchanged.

#### F21. rawReadHalf returns halfwords in reversed order (dead code, exported to HOL)

- **L3:** 1738-1748. For pAddr<2:1>='00' it returns `data<63:48>`, but MEM is little-endian
  (1661-1687), so bytes 0-1 are `data<15:0>`. Nothing calls it, in the spec or in step/, prog/,
  decompiler/ or HolBA src/ outside the generated models. Fetch uses rawReadInst (1750-1757),
  which is correct. The function is still exported as `rawReadHalf_def` (HOL-fixes
  riscvScript.sml:4541; HolBA `src/shared/l3-machine-code/riscv/model/riscvScript.sml:4516`).
- **Expected:** Manual §1.4-1.5 (little-endian memory); sail `sys_control.sail:554-557` (only
  little-endian is supported).
- **Test** (executed; `rv64i-ctrl-mem/t5.sml`, `rawreadhalf-refute1`). Bytes 0x10..0x17 are at
  0x8000..0x8007. `rawReadData(0x8000)` = 0x1716151413121110, which is correct. `rawReadHalf`
  at 0x8000/2/4/6 gives 0x1716, 0x1514, 0x1312, 0x1110; expected 0x1110, 0x1312, 0x1514, 0x1716.
- **Fix:** Delete it, or reverse the cases: '00' gives `<15:0>`, '01' gives `<31:16>`, '10'
  gives `<47:32>` and '11' gives `<63:48>`.
- **Resolution:** db2396f08 (deleted).

#### F22. EncodeRVC and CBtype produce wrong encodings (dead code, exported to HOL)

- **L3:**
  - `CBtype` (5045-5046) puts `imm<5>` (offset[6]) in bit 2, where the CB format needs `imm<4>`
    (offset[5]). offset[5] is lost and offset[6] appears twice.
  - `EncodeRVC` (5050-5053) calls `CBtype(1, 0, …)` for `beq rs1',x0,…`, giving funct3=000 (the
    C.NOP/C.ADDI space). C.BEQZ has funct3=110.
  - Every other instruction goes through `Full(Encode i)`.
  - No callers exist in HOL-fixes, HOL, HolBA or CakeML, but `EncodeRVC_def` and `CBtype_def`
    are exported.
- **Expected:** Manual §7.1.1 (CB format) and §7.1.3 (C.BEQZ). sail `zca_insts.sail` C_BEQZ is
  `0b110 @ imm[7] @ imm[3..2] @ creg @ imm[6..5] @ imm[1..0] @ imm[4] @ 0b01`. riscv-opcodes
  `rv_c` has `c.beqz … 15..13=6`.
- **Test** (executed; `rvc-decode/enc.sml`, `encrvc-refute1/2`):

  | Instruction | L3 EncodeRVC | Correct |
  |---|---|---|
  | beq x8,x0,8 | Comp 0x401, decodes as ADDI fp,fp,0 | 0xC401, decodes as BEQ fp,$0,8 |
  | beq x8,x0,32 | 0x1 (c.nop) | 0xC005 |
  | beq x8,x0,64 | 0x25 | 0xC021 |
  | beq x9,x0,−2 | 0x1CFD | 0xDCFD |
  | beq x15,x0,254 | 0xFFD | 0xCFFD |
  | beq x8,x0,−256 | 0x1001 | 0xD001 |
- **Fix:** Delete EncodeRVC, CBtype and the `rvc` type. Alternatively, put `imm<4>` in bit 2 and
  call `CBtype(1, 6, …)` for BEQ (and 7 for BNE).
- **Resolution:** 7f2c56787 (deleted EncodeRVC, CBtype, `rvc` and `rvcreg`).

#### F23. CSRRW/CSRRWI with rd=x0 still read the CSR

- **L3:** CSRRW (4136-4142) and CSRRWI (4171-4178) bind `val = CSR(csr)` unconditionally.
- **Problem:** No program can observe this. CSRMap reads are pure, and all 45 defined CSRs have a
  read case, so `#UNDEFINED` is unreachable. The manual also says standard CSRs have no read side
  effects, so the extra read could only matter for custom CSRs.
- **HOL export:** `CSR` has type `state -> (F64 # state)` because of its `#UNDEFINED` default, so
  the read does appear in `dfn'CSRRW`. For a concrete defined csr with rd=0 it should simplify
  away.
- **Expected:** Manual §4.2.1: "If rd=x0, then the instruction shall not read the CSR and shall
  not cause any of the side effects that might occur on a CSR read". sail `doCSR`:
  `read_val = if access_type != CSRWrite then read_CSR(csr) else zeros()`.
- **Test** (executed; `zicsr/tests3.sml`, `csrrw-x0-refute1/2`). `csrrw x0,c,x5` and
  `csrrwi x0,c,3` were run on all 45 defined CSRs. None raised an exception, and the read-only
  ones trapped Illegal_Instr. Writes behave as the manual says.
- **Fix** (optional): `val = if rd == 0 then 0 else CSR(csr)`, which mirrors Sail's structure.

#### F24. SC translates with Read access, and not at all when it fails

- **L3:**
  - SC_W (2768-2785) and SC_D (2788-2805) check the reservation first (2772, 2794). Only when it
    matches do they call `translateAddr(vAddr, Data, Read)` (2774, 2796).
  - Stores and AMOs pass `Write` (SW 2664, SD 2708, AMOSWAP_W 2814).
  - `checkMemPermission` (1774) depends on the access type, and the PTE D bit is set only
    `when ac == Write` (walk64 1846; translate64 TLB hit 1985).
- **Problem:** Under Sv39 two things go wrong:
  - **(a)** A successful SC to a readable but non-writable page writes memory and never sets D.
  - **(b)** A failing SC never translates, so it never faults, even when the address is
    unmapped.

  In Bare or M-mode translation is the identity, so nothing is visible. The rating is note
  rather than deviation because the effect needs priv-1.7 paging (mstatus.VM/sptbr), which the
  plan replaces with WARL-Bare satp until WP7. It becomes observable again as soon as
  `translateAddr` checks Read vs Write. That happens with the WP2 PMP hook: a U-mode SC into a
  PMP region with R=1, W=0 would succeed.
  *WP7 note:* with Sv39, Sv48 and Sv57 (WP7 stage 2) an SC is translated as a write whether or not
  its reservation matches (`design-smode.md` [S18]); `sim/tests/sv39.S` checks that an SC to a
  read-only page raises a store page fault with and without a reservation.
- **Expected:**
  - Manual §5.2: "No SC.W instruction shall retire unless it passes memory permission checks, but
    it is UNSPECIFIED whether any side effects (such as setting a page-table entry D bit) occur
    on a failed SC.W. For the purposes of memory protection, a failed SC.W may be treated like a
    store."
  - sail `vmem_utils.sail` `vmem_write_addr` translates with StoreConditional before
    `match_reservation`, and still runs `phys_access_check` on the failure path.
    `vmem_pte.sail` maps StoreConditional to `pte_W`.
- **Test** (executed by both refuters on a hand-built priv-1.7 Sv39 setup; `sc-vm-refute1/t.sml`,
  `t2.sml`, `refuter2-a-sc-vm/t.sml`). Setup: U-mode, mstatus.VM=9, and VA 0x2000 mapped by a
  leaf whose PTE_T type allows read but not write (T=4 S/U read-only; refuter 1 also used T=6).
  x2=0x2000, x3=0x12345678.
  - `sw x3,0(x2)` (0x00312023) traps with cause 7.
  - `lr.w x1,(x2)` (0x100120AF) then `sc.w x4,x3,(x2)` (0x1831222F): no trap, x4=0, memory
    written. The LR.D/SC.D pair behaves the same. Expected: a store/AMO fault.
  - On a writable page, a successful SC leaves PTE.D clear, while SW sets it.
  - `sc.w x4,x3,(x5)` (0x1832A22F) to an unmapped VA retires with x4=1, while SW to the same VA
    faults.
- **Fix:** In SC_W/SC_D, call `translateAddr(vAddr, Data, Write)` first and raise
  Store_AMO_Fault on None. Then check the reservation: on a mismatch write rd=1, on a match write
  memory and rd=0. Cancel the reservation in both cases, which subsumes F3. The natural time is
  the WP2.5 PMP work or WP7.

#### F25. SML export raises Option for NaN or ±inf inputs to all eight FCVT.int.fmt

- **L3:** 3374, 3397, 3442, 3465, 3825, 3848, 3893 and 3916 each have
  `val = ValOf(FP32_ToInt(r, inp))` (or FP64), bound before the if-chain that handles NaN and
  ±inf. `FP32/64_ToInt` return None for NaN and ±inf (L3 lib `FP32.sml:125`, `FP64.sml:133`).
  The SML export evaluates the binding eagerly (riscv.sml 7254, 7281, 7320, 7347, 7744, 7771,
  7810, 7837), and `Next` has no handler.
- **HOL export:** unaffected. `ValOf NONE` is just an unspecified value that the guards discard,
  so the HOL result is the correct saturated value (only NV is missing, F11).
- **Expected:** Manual §6.1.7, table of float-to-integer behaviour for invalid inputs. sail's
  `riscv_f32ToI32` and the other conversions always return a value.
- **Test** (executed; `fconv/t.sml`, `fpconv-valof-refute1/2`). FCVT.W.S x3,f1 (0xC00081D3)
  with boxed 0x7FC00000, 0xFFC00000, sNaN, +inf or −inf raises SML `Option`. The expected
  results are 0x7FFFFFFF, or 0xFFFFFFFF80000000 for −inf, with NV. All eight
  FCVT.{W,WU,L,LU}.{S,D} raise the same exception on NaN/±inf. Control: 1.5 converts to 2 in all
  eight.
- **Fix:** Match on the option rather than taking ValOf:
  ```
  ; res = match FP32_ToInt(r, inp)
          { case None    => if FP32_IsNan(inp) or not FP32_Sign(inp) then max else min
            case Some(v) => if v > max then max else if v < min then min else [v] }
  ```
  Combine this with F6 (sign extension of the WU result) and F11 (NV and NX).
- **Resolution:** a9499320d (`val` matches on the option; the NaN/infinity tests already ran first).

#### F26. The time CSR can go backwards with more than one hart

- **L3:** `tickClock` (5266-5270) does `clock <- cycles div [CYCLES_PER_TIMER_TICK]` with
  `cycles = c_cycles(procID)+1`. `clock` is a single global (653), while `c_cycles` is per hart
  (656). `tickClock` runs at the end of every `Next` (5355), so the global clock is overwritten
  from whichever hart stepped last. The time CSR read (937) returns `clock + time_delta`. A
  single hart, which is the HOL/HolBA configuration, is unaffected.
- **Expected:**
  - Manual §4.3: "The real-time clocks of all harts must be synchronized to within one tick of
    the real-time clock". The accompanying commentary says software observes time across harts
    as monotonically non-decreasing, and time counts wall-clock time.
  - sail `zicntr_control.sail:26` reads a single platform `mtime`. Sail's CLINT is single-hart,
    so the multi-hart case rests on the manual.
- **Test** (executed; `zicsr/tests4.sml` T14, `time-mono-refute1/2`). From reset with
  totalCore=2:
  - Hart 0 runs 400 nops, then `csrrs x1,time,x0` (0xC01020F3): x1=2.
  - Hart 1 runs one nop, which sets clock to 0.
  - Hart 0 runs `csrrs x2,time,x0` (0xC0102173): x2=0. Time went backwards on hart 0 itself.

  A single hart and strict round-robin scheduling both stay monotone.
- **Fix:** Use a single platform mtime advanced once per scheduling round, in the WP2 counter
  step. `max(clock, cycles div N)` would make time monotone, but harts could still drift more
  than one tick apart. `checkTimers` (5276-5279) reads the same clock, so it changes with this
  fix.

#### F27. HOL export: NaN results are unspecified, and there is no RMM

- **L3:**
  - The FArith defines write their results without canonicalising them (F10), and `l3round`
    (823-831) has no RMM.
  - In the import, FP32_Add and the other operations become `machine_ieee` fp32_add etc.
    (`common/Import.sml:827-846`), which wrap binary_ieee `float_add` etc.
  - For any NaN result those return `float_some_qnan` (`binary_ieeeScript.sml:495-498`), a
    choice term. Conversions use the `convert_def` NaN case `from_float (@fp. float_is_nan fp)`.
- **Problem:** riscvTheory does not determine rd after any NaN-producing FP instruction. The SML
  export's x86 NaN is a legal refinement of the HOL term, so the two exports do not contradict
  each other, but their agreement cannot be proved, and neither matches Sail. The HOL `rounding`
  type has four modes (F13), and `float_mul_add` raises no NV for ∞×0+qNaN (F12).
  `riscv_stepLib` has no FP step theorems today, so this becomes a problem in WP3.
- **Expected:** Manual §6.1.3 (canonical NaN); sail produces deterministic canonical NaNs.
- **Evidence:** reading the HOL sources, plus `EVAL` in a plain `hol` session
  (`refute2-fp-hol/t.sml`):
  - `fp32_add roundTiesToEven 0x7F800000w 0xFF800000w` gives
    `float_to_fp32 (float_some_qnan (FP_Add …))`.
  - `fp32_isNan` of that result gives T, so a canonicalising wrapper reduces it.
  - `fp32_mul_add_with_flags roundTiesToEven 0x7F800000w 0w 0x7FC00000w` gives
    `InvalidOp := F`.
- **Fix:** F10 (canonicalise in the spec), F13 (RMM) and F12 (explicit NV check). No further
  change is needed.
- **Resolution:** NaN results by F10 (a88125e3d) at the spec level; RMM deferred with F13. Batch B also found that HOL's `convert` and `int_to_fp*` get the sign of a zero result wrong (FCVT.S.D/FCVT.D.S of -0.0 give +0.0, FCVT.S.D of a tiny negative gives +0.0, int-to-float of 0 under RDN gives -0.0); not fixed.

#### F28. Misaligned loads and stores always complete, but plan WP2.5 says they trap

- **L3:**
  - The Load/Store defines (2559-2717) have no alignment check.
  - `rawReadData`/`rawWriteData` (1690-1736) handle the within-block case, the two-block case
    and the 2^64 wrap correctly.
  - The nbytes=8 mask `(1<<64)-1` is all ones in both exports, because `BitsN.<<` saturates the
    shift amount (`BitsN.sml:240-241`) and HOL `word_lsl` by 64 gives 0.
- **Problem:** L3 conforms to the manual today, but disagrees with the planned design and with
  the configured oracle. `RISCV_MODEL_PLAN.md` WP2.5 pins "Misaligned accesses: trap (codes
  4/6)". The oracle override `~/Documents/riscv-tools/rv64gc_mu_pmp.json` already sets the
  misaligned load_store/amo/lrsc exceptions to `{"Some":"AlignmentException"}` (plan
  Appendix B; rv64ui-p-ma_data is an expected failure). Until WP2.5 lands, L3 and that oracle
  disagree on every misaligned access.
- **Expected:**
  - Manual §2.1.6: misaligned accesses "may either complete execution successfully or raise an
    exception", depending on the EEI. Zicclsm is not part of RV64GC.
  - sail's default `config/config.json.in` has `memory.misaligned.exceptions.load_store =
    {"None": null}`, meaning the access completes.
- **Test** (executed; `rv64i-ctrl-mem/t2.sml`, `t4.sml`, `misalign-ls-refute1`,
  `refuter2-misalign`).
  - 224 loads and 128 stores at offsets 0-15, around 0x10000 and 0x2000FF8 (a block crossing),
    checked against a byte-wise little-endian reference: 0 failures.
  - U-mode `lw x2,0(x1)` (0x0000A103) with x1=0x5003 and memory = LE 0x1122334455667788 gives
    x2=0x22334455, PC+4, no trap.
- **Fix:** None needed for conformance. If WP2.5 keeps "trap":
  - add Load_Misaligned (shared with F16);
  - check vAddr alignment before `translateAddr` in every Load/Store and in FLW/FLD/FSW/FSD (the
    C forms decode to these);
  - raise Load_Misaligned, or AMO_Misaligned (cause 6) for stores.

  WP7 must also translate both pages when an access crosses a page boundary (Appendix R2).

#### F29. SML runtime: FCVT.S.LU with rs1 ≥ 2^63 raises Fail

- **L3:** FCVT_S_LU (3428-3433) calls `FP32_FromInt(r, [0`1 : GPR(rs)]::int)`, whose argument
  can be as large as 2^64−1. L3 lib `FP32.sml:120-123` `fromInt` accepts only [−2^63, 2^63−1]
  and otherwise raises `Fail "FP32.fromInt: too large"` before any SSE call. `FP64.fromInt`
  (`FP64.sml:130`) uses `Real.fromLargeInt` and has no such limit. The HOL side
  (`int_to_fp32` via the reals, `Import.sml:823`) is total and correct.
- **Expected:** sail FCVT_S_LU calls `riscv_ui64ToF32` for every value; 2^64−1 under RNE gives
  0x5F800000 with NX.
- **Test** (executed; `fconv/t.sml`, `fcvtslu-refute1/2`). FCVT.S.LU f3,x1 rne (0xD03081D3):
  - x1=0xFFFFFFFFFFFFFFFF raises `Fail`.
  - x1=0x8000000000000000 (expected 0x5F000000) raises `Fail`.
  - x1=0x7FFFFFFFFFFFFFFF gives 0x5F000000, which is correct.
  - FCVT.D.LU of 2^64−1 gives 0x43F0000000000000, which is correct.
- **Fix:** In the runtime used by the WP0 harness, handle |i| ≥ 2^63 by converting
  j = (i >> 1) | (i & 1) and doubling the result. Keeping the low bit as a sticky bit
  (round-to-odd) preserves rounding in every mode, and the doubling is exact. Alternatively,
  keep a patched `FP32.sml` beside the harness, or use a softfloat binding.
- **Resolution:** 14710aca4, in the spec: under `not PROVER_EXPORT`, x >= 2^63 is converted as x/2 rounded to odd, times 2; the HOL export is alpha-equivalent. The audit missed that FP64.fromInt also misrounds values below -2^62 in RDN/RUP (FCVT.D.L): deb792f21.

#### F30. The stock PolySSE FP64 FFI returns garbage under Poly/ML 5.9.2

- **Not in riscv.spec.** L3 lib `PolySSE.sml` declares the fp64 operations as returning
  `cStruct2(cUint32, cUint64Large)`. On the C side, `sse_float.c` returns
  `struct {uint32 mxcsr; uint64 result}` in RAX:RDX, as the SysV ABI requires.
- **Problem:** Poly/ML 5.9.2's x86-64 FFI mishandles 16-byte structs returned in two registers.
  It stores RDX at offset 0 and leaves offset 8 uninitialised. A controlled test returning
  `{0x1111…, 0x2222…}` comes back as `a=0x2222…` with garbage in b.
  - **Affected:** the 8-byte `{u32,u32}` returns used for FP32 work. FP64 add, sub, mul, div,
    sqrt, mul_add and mul_sub are all broken, which covers every D arithmetic instruction,
    including today's FMADD.D (add of mul).
  - **Unaffected:** compare, toInt, fromInt and the conversions.
- **Test** (executed; `harness-ffi-refute1`, `polysse-refute2`). FADD.D f3,f1,f2 rne
  (0x022081D3) of 1.0+2.0 gives a heap-pointer-like value such as 0x70742220E570 with the stock
  binding, and 0x4008000000000000 with the shim. FDIV.D 1/3 gives 0x3FD5555555555555 with the
  shim.
- **Fix:** Return the result through an out-pointer: `work/fparith/shim.c` plus
  `PolySSE_fixed.sml`. The WP0 harness in `examples/l3-machine-code/riscv/sim` already ships
  `lib/sse_fp64_shim.c` and `lib/SSEFix.sml`. Sanity-check any emulator binary with FADD.D
  1+2 = 0x4008000000000000; the older `~/Documents/riscv-tools/work/sim/riscv-sim` printed
  garbage for fnmsub.d/fnmadd.d. Longer term, a softfloat binding would also give RMM (F13) and
  RISC-V NaN behaviour (F10) in the SML export.
- **Resolution:** no spec change; the `sim/` shim is documented and needs no extension for batch B.

#### F31. Poly/ML 5.9.2 `IntInf.~>>` is wrong for negative bignums

- **Not in riscv.spec.** For a negative value outside the short-int range (|x| > 2^62) whose
  shifted-out bits are not all zero, Poly/ML returns −(|x| >> n), rounding toward zero instead
  of down. The L3 runtime is not affected:
  - `BitsN.sml` lines 95 (`bits`) and 243 (`>>+`) apply `~>>` only to the payload of `B(i,_)`,
    which is never negative. Line 100 is commented out.
  - The Map and Ptree uses are on non-negative keys.
  - `riscv.sml` never calls `IntInf.~>>`, and the export's MULH\* use 128-bit BitsN products.
- **Test** (executed; `mext/t8.sml`, `refute-m-intinf`, `m-refuter2`):

  | Expression | Poly/ML result | Correct |
  |---|---|---|
  | `~>>(~2^63, 64)` | 0 | ~1 |
  | `~>>(~2^62-1, 63)` | 0 | ~1 |
  | `~>>(~2^64+1, 64)` | 0 | ~1 |
  | `~>>(~2^64-1, 64)` | ~1 | ~2 |
  | `~>>(~2^127, 128)` | 0 | ~1 |

  `~>>(~2^100-3, 2)` is off by one. A sweep found 2,543 mismatches against `IntInf.div`. A
  `~>>`-based MULH/MULHSU oracle reported about 4,000 false mismatches.
- **Fix:** None in the spec. SML oracles and harnesses should use `IntInf.div(x, 2^n)`, or mask
  to a non-negative value before shifting. Record this in the WP0 harness notes.
- **Upstream:** Poly/ML issue #243, fixed after the 5.9.2 release (master 64eb08b0 and branch
  fixes-5.9.2 ccd3e371, December 2025): `PolyShiftRightArbitrary` in `libpolyml/arb.cpp` shifted
  the magnitude and kept the sign. Reproduction on the 5.9.2 release (x86-64, GMP), which prints
  `0 ~1`:
  ```sml
  val x = ~(IntInf.pow (2, 63));
  val got = IntInf.~>> (x, 0w64);
  val expected = IntInf.div (x, IntInf.pow (2, 64));
  val () = print (IntInf.toString got ^ " " ^ IntInf.toString expected ^ "\n");
  ```
- **Resolution:** no spec change; `sim/lib/IntInfFix.sml` corrects `~>>` before L3's library loads.

## 3. Coverage: checked and found correct

**Decode / encoding inventory.**

- `Decode` and `DecodeRVC` are total over the 1,323,707-word corpus; `#UNDEFINED` is never
  reached during decode.
- Every RV64GC riscv-opcodes entry decodes to the right constructor and operands.
- All non-RV64GC space decodes to `UnknownInstruction`: Zb\*, V, Zfh, Q, H, Zicbo\*, Zicond,
  custom, and the 48-bit-and-longer prefixes. The only exceptions are F15 and F17.
- Fields are checked where required:
  - shamt[5]=1 for the \*IW shifts is rejected, as are FP fmt=10/11 (H/Q) and FSQRT with rs2≠0;
  - FMIN/FMAX/FSGNJ require their funct3 values;
  - LR with rs2≠0 and JALR with funct3≠0 are rejected;
  - LOAD funct3=7, STORE funct3≥4, MISC-MEM funct3 2/3/7 and OP-32 with funct7=1 and funct3 1-3
    are rejected.
- Some fields are correctly ignored: FENCE accepts any fm (the manual says to treat reserved fm
  as FENCE), and FENCE.I ignores imm/rs1/rd. ECALL and EBREAK match exactly.
- Reserved rm 101/110 decode and then trap in `Run`, which has the same visible outcome as Sail.
- HINTs execute as nops. This covers all 394 RVC HINT words: c.nop with imm≠0, c.addi with
  imm=0, c.li/c.lui/c.mv/c.add with rd=0 (including c.ntl.\*), c.slli with rd=0 or shamt=0, and
  c.srli/c.srai with shamt=0. It also covers fence.tso, pause, ntl.\*, ALU operations with
  rd=x0, lui/auipc with rd=x0, and fence with pred or succ zero.
- rdcycle, rdtime and rdinstret decode to CSRRS rd,x0,0xC00/0xC01/0xC02 and run in U-mode.
- Encode(Decode(w)) = w for every legal RV64I/M computational encoding, and the FP
  disassembler/encoder tables agree with Decode.
- mret, wfi and sfence.vma in their modern encodings decode to `UnknownInstruction`. That is
  WP2's job.

**RV64I computational** (2060-2286; Decode 4297-4330).

- ADDI, SLTI, SLTIU, ANDI, ORI and XORI sign-extend imm12; SLTIU −1 compares against all ones.
- ADDIW, ADDW and SUBW truncate to 32 bits and then sign-extend. LUI sign-extends imm<<12.
- AUIPC adds its own PC, including after a C instruction and at the 2^64 wrap.
- RV64 shifts mask rs2<5:0>. The W forms use rs2<4:0> on rs1<31:0> and sign-extend the result.
  SRA and SRAI are arithmetic.
- x0 reads 0 even when the backing `gpr(0)` is poisoned, and writes to it are discarded. The
  Table 5 HINTs, including the semihosting markers, are nops.
- rd=rs1=rs2 aliasing works.
- 6,000 random cases against Sail semantics: 0 mismatches.
- Reserved funct7/funct6/funct3 combinations in these opcodes trap with cause 2.

**RV64I control transfer, memory, fences and traps.**

- **Branches:** B-type immediate and target are correct, with signed and unsigned compares
  (2,688 cases, 0 failures). An untaken branch whose target is misaligned (C off) does not trap.
  A taken one traps with cause 0, mepc=PC and mbadaddr=target.
- **JAL:** the J-type immediate is correct at all edge offsets, and `PC + (SignExtend(imm) << 1)`
  has the right precedence in riscv.sml.
- **Links and JALR:** the link is PC+4, or PC+2 through Skip for C.JALR. JALR computes
  (rs1+imm)&~1 before writing the link, so rd==rs1 works.
- **Fetch:** a misaligned PC raises Fetch_Misaligned with mbadaddr=PC. A 32-bit fetch whose
  second half is on another page translates that half separately.
- **Loads:** sign and zero extension are correct for all widths; rd==rs1, negative offsets and
  rd=x0 work, and the access is still performed for rd=x0.
- **Stores:** SB/SH/SW/SD write exactly their width, aligned or misaligned, within a block,
  across two blocks, and across the 2^64 wrap.
- **Fences:** FENCE, FENCE.TSO, PAUSE, fm=1111 and iorw are all no-ops. FENCE.I as a no-op is
  correct, because fetch reads MEM8 every step.
- **Traps:**
  - ECALL raises cause 11 in M-mode and 8 in U-mode; EBREAK and C.EBREAK raise cause 3.
  - mepc is the PC of the trapping instruction, trapping instructions do not increment
    instret, and no Skip is added to the trap PC.
  - The all-ones word, 0x0000 and the 48-bit prefix all raise Illegal_Instr.

**M.**

- All 13 encodings decode correctly.
- 95,836 cases against Sail's rules, covering edge pairs, random pairs, rd=x0, rd=rs1, rd=rs2,
  rs1=x0, rs2=x0 and rd=rs1=rs2: every destination value matches. F20 is an SML-only Delta
  issue.
- The MULH variants take bits 127:64 of the correctly signed or unsigned 128-bit product. MULW
  sign-extends the low 32 bits of the product.
- Division by zero: the quotient is all ones and the remainder is the dividend. The W forms,
  REMUW included, sign-extend rs1<31:0>.
- −2^63/−1 = −2^63 with remainder 0, and likewise for the 32-bit −2^31/−1.
- No M instruction ever raises an exception.
- HOL `word_quot`/`word_rem` give the right overflow results. HOL's unspecified n DIV 0 is never
  reached, because the spec guards against a zero divisor.

**A.**

- Decode of every LR/SC/AMO funct5 in .W and .D form is correct. LR with rs2≠0, funct3 000/100
  and funct5 00101 (AMOCAS) are illegal. aq/rl are decoded and ignored, which is correct for a
  sequential model.
- LR.W sign-extends, and LR.D/SC.D succeed as expected.
- SC.W stores exactly 4 bytes. SC writes 0 on success and 1 on failure, an SC with no
  reservation fails without storing, and an SC to another address fails (allowed).
- A same-hart store between LR and SC keeps the reservation, as in Sail. A trap cancels it
  (`takeTrap` 1562).
- Misaligned AMOs and SCs raise cause 6 with mbadaddr set. An AMO translation failure raises
  cause 7, and an LR translation failure raises cause 5.
- AMOSWAP/ADD/XOR/AND/OR.W compute the right low word, write 4 bytes, carry nothing into the
  upper word, and sign-extend rd.
- The .D min/max forms are correctly signed or unsigned.
- rs2 and the address are read before rd is written. rd=x0 still updates memory.
- Atomicity is indistinguishable from Sail's. The reservation is keyed on vAddr, which the
  manual allows.

**F/D.**

- All F/D computational, R4, conversion, move, compare, classify and load/store encodings decode
  correctly.
- Rounding modes:
  - static rm 0-3 select RNE/RTZ/RDN/RUP, checked on ties and on directed cases;
  - rm=7 uses frm;
  - frm 5-7 and static rm 5/6 trap, which is allowed.
- Accrued flags are never cleared by arithmetic.
- The canonical-NaN constants and `FP32/64_IsSignalingNan` are correct.
- Non-NaN results of FADD, FSUB, FMUL, FDIV and FSQRT (S and D) are correctly rounded on the
  tested inputs.
- The FMA family is correct when the product is exact and the result is not a signed zero.
  FNMADD(0,1,0) and FMADD(1,1,−1) under RDN give −0.
- writeFPRS/writeFPRD and the fflags/frm/fcsr writes set FS to Dirty and SD to true. F5 is the
  exception.
- FCVT.W/L(U).S/D round correctly in range and saturate finite out-of-range values; the signed
  results are sign-extended (F6 covers WU).
- FCVT.S/D.W/WU/L/LU read the right source bits and round correctly. FCVT.S.D rounds finite
  values correctly, including overflow to +inf.
- FMV.X.W sign-extends the raw low 32 bits. FMV.X.D and FMV.D.X move all 64 bits.
- FSGNJ\*.D, and FSGNJ\*.S on boxed inputs, are correct, preserve payloads and set no flags.
- FEQ is quiet: NV only for an sNaN. FLT and FLE signal: NV for any NaN. −0 == +0, and
  −0 <= +0.
- FCLASS bits 0-8 are correct.
- FSW, FSD and FLD are bit-exact. FLW reads the right word at offsets 0 and 4.
- In HOL, `FP32/64_ToInt` map to `float_to_int`, so the HOL FCVT values are correct despite the
  eager ValOf (F25).

**C.**

- All 49,152 halfwords were checked against the objdump-validated reference. The only
  mismatches are the 64 of F15.
- The immediate scrambles and sign/zero extensions of all seven formats are correct, and
  rd'/rs' map to x8-x15 and f8-f15.
- The RV64 meanings of the funct3 slots are used: c.ld/c.sd/c.ldsp/c.sdsp/c.addiw, with no
  c.jal/c.flw/c.fsw/c.flwsp/c.fswsp.
- These reserved points are illegal: 0x0000, c.addi4spn with zero immediate, c.addi16sp with
  zero immediate, c.lui with zero immediate for any rd (which also covers Zcmop), c.lwsp/c.ldsp
  with rd=0, c.jr with rs1=0, quadrant 0 funct3=100, and CA 100-1-11 with funct2 10/11.
- c.addi16sp takes precedence over c.lui for rd=2, and c.ebreak is decoded only for rs1=rs2=0.
- Skip is 2 or 4 from bits[1:0] of the first halfword; links are PC+2; branch and jump targets
  are relative to the compressed instruction's PC.
- A mixed 16/32-bit instruction stream steps through the right PCs. With C off, halfwords trap.
  `DecodeRVC` has no `#UNDEFINED`.
- Directed execution of every compressed instruction: 0 failures.

**Zicsr / Zicntr / Zifencei.**

- **Reads vs writes:**
  - CSRRS/CSRRC with rs1=x0 and CSRRSI/CSRRCI with zimm=0 are pure reads: no write, and no trap
    on a read-only CSR.
  - CSRRS with rs1≠x0 counts as a write even when the value is 0, so it traps on cycle.
  - `csrrw x0,cycle,x0` traps.
- **Access checks:** the read-only test is csr<11:10>==11 and the privilege test is
  csr<9:8> ≤ priv, as in Sail. U-mode can read cycle, time, instret and fcsr. U-mode access to
  mstatus or sstatus traps, as do undefined CSRs (0x004, 0xC03, and 0xC80, which is RV32-only).
- **Counters:** cycle, time and instret are full 64-bit values. instret reads the count before
  the current instruction, and trapping instructions do not increment it.
- **FP CSRs:** fflags is fcsr<4:0>, frm is fcsr<7:5>, and fcsr reads <7:0>. Writing one field
  preserves the others. Writes set FS to Dirty; reads do not.
- **Operands:** rd gets the old value, also when rd==rs1. zimm is zero-extended. Set and clear
  are computed at 64 bits before masking.
- **Decode:** the six CSR instructions decode correctly, funct3=100 is illegal, and there are no
  compressed CSR forms.
- **FENCE.I** with any imm/rs1/rd is a no-op with PC+4.
- **Totality:** `is_CSR_defined` and `CSRMap` agree on all 4,096 addresses (45 are defined).
  Every defined CSR has a read case and every writable one a write case, so `#UNDEFINED` and
  `#INTERNAL_ERROR` cannot be reached from CSR instructions.

## 4. Appendix: refuted findings

Each of these was confirmed as a fact about L3 but rejected as a user-level finding. Do not
report them again here; pass them on to the work package named.

- **R1.** *mbadaddr is not written on illegal-instruction, EBREAK or ECALL traps* (takeTrap
  1583-1584). Out of scope:
  - mbadaddr is an M-mode CSR; reading it from U-mode traps.
  - mcause and mepc are correct.
  - priv 1.7 specified "mbadaddr is not modified for other exceptions".

  → WP2 trap entry: write mtval on every trap (instruction bits, PC, or 0, as Sail does).
- **R2.** *A misaligned access that crosses a page is translated only at its first byte.* Out of
  scope: it is reachable only through priv-1.7 paging, which WP2 removes (WARL-Bare satp), WP7
  rewrites, and WP2.5 makes trap anyway. → WP7: translate both pages, as Sail's
  `split_on_page_boundary` does. *WP7 note:* not needed: a misaligned access traps before it is
  translated (`design-smode.md` [S15], [D55]), so no data access crosses a page.
- **R3.** *FP instructions do not trap when mstatus.FS=Off.* Privileged rule (mstatus FS
  semantics). Reset sets FS=Initial and U-mode cannot write mstatus or sstatus, so no user
  program can reach FS=Off. → WP2.1/2.2 requirement: FS=Off makes F/D/C.F\* instructions
  illegal.
- **R4.** *fflags, frm and fcsr are accessible when FS=Off.* Same reasoning as R3.
  → WP2: `is_CSR_accessible(0x001-0x003)` must depend on FS, as in Sail.
- **R5.** *An explicit write to the instret shadow 0x902 is followed by the retirement increment,
  so the next read gives v+1.* 0x902 is a priv-1.7 S-level CSR that U-mode cannot write, and
  Sail has no CSR at that address; the modern CSR is minstret 0xB02. → WP2 counter step:
  suppress the increment on an explicit minstret write, as Sail does with `minstret_increment`.
