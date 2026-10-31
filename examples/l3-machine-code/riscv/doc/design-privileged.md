# Privileged architecture design for the L3 RISC-V model (priv 1.13, M/U + PMP)

**Scope.** This document specifies how the privileged parts of HOL4's L3 RISC-V model (`examples/l3-machine-code/riscv/src/riscv.spec`, branch `riscv-l3`) are rewritten from privileged spec 1.7 to **Machine-Level ISA 1.13 and Supervisor-Level ISA 1.13 of the privileged specification version 20260120**. The target is one RV64-only hart (MXLEN = SXLEN = UXLEN = 64), with extensions **I M A F D C Zicsr Zifencei Zicntr** (RV64GC), **M-mode and U-mode executed and validated**, and **physical memory protection (PMP)** with 16 entries. **S-mode is present only as storage**: `misa.S = 1`, every S-mode CSR exists with 1.13 numbering and legalisation, `medeleg`/`mideleg`/`sret` are implemented as specified, but S-mode execution is outside the validated scope. Nothing here may need rework when S-mode and Sv39/Sv48 are added later (plan WP7). *WP7 amendment:* `design-smode.md` validates S-mode execution (its stage 1) and adds Sv39/Sv48/Sv57 translation; it revises the decisions it names ([D5], [D21], [D23], [D32], [D46]), and this document stays in force for everything else. Not implemented: H, V, Sv* translation (`satp` accepts only Bare; *WP7 amendment:* its stage 2 adds Sv39, Sv48 and Sv57, `design-smode.md` §3), debug mode and triggers, NMI/Smrnmi, Sstc, Sscofpmf, Smstateen, Smepmp, Smdbltrp/Ssdbltrp, Zicfilp/Zicfiss, Zihpm, Zkr. Fields of those extensions appear only as read-only zero. The document fixes behaviour; it does not design L3 code, but names the existing L3 functions each rule replaces.

## 0. Conventions

**Citations.**
- **P §x p.N**: privileged spec (`riscv-privileged.pdf`, 20260120), section and **printed** page. PDF page = printed page + 7 (chapter 3 "Machine-Level ISA" starts on printed p.27 = PDF p.34).
- **U §x p.N**: combined manual `riscv-spec-8fb3965-2026-10-30.pdf` (unprivileged volume), printed page. PDF page = printed page + 6.
- **sail**: sail-riscv tag `2026-10-26-6f886e6`, cited as `path:line` under `model/`. "sail default" is `config/config.json.in`; **cfg** is the project overlay `~/Documents/riscv-tools/rv64gc_mu_pmp.json`. The consolidated list of cfg settings this design requires is §6.10.
- **L3 lines** refer to `riscv.spec` on `riscv-l3` at `55e74e68b` (5401 lines).
- **Plan** is `HolBA/RISCV_MODEL_PLAN.md`.

**Notation.** Bits are `x<hi:lo>` (L3) or `x[hi:lo]`; bit 0 is the LSB. `&&`, `||`, `~` are bitwise and/or/not on words. Comparisons on addresses are unsigned. "RO0" = read-only zero (writes ignored, reads 0). "Illegal" = illegal-instruction exception, `mcause` 2. Privilege encodings: U = `00`, S = `01`, M = `11` (P §1.2 Table 1 p.11). `[Dn]` refers to row n of the Decisions table (§7); `[Rn]` to a resolved contradiction listed below; §x.y refers to this document.

**Contradictions between the source analyses, and how they are resolved.** Each is also discussed where it arises.

| # | Topic | Positions | Resolution | What decides |
|---|---|---|---|---|
| R1 | Type of the current-privilege state | Plan WP2.1 and the status analysis: `id -> Privilege` (enum). Compatibility analysis: `id -> bits(2)`. | `c_privilege :: id -> bits(2)`, written only via `privLevel(p)`, read via a total `privilege()` (§1.4.1, [D1]). | The spec is silent on representation; P §1.2 Table 1 p.11 fixes the 2-bit encoding stored. HolBA can lift only word-valued state (F5, §1.1). |
| R2 | PMP grain G | PMP analysis, plan WP0.2, sail default: G = 0. Compatibility analysis: G = 1 so the M-mode PMP lemma needs only "no entry locked". | **G = 0**; the M-mode hypothesis is strengthened with a word-level "every entry is OFF or NAPOT" conjunct (§1.5, §5.4.1, [D48]). | P §3.7.1.1 p.73 permits any G; P §3.7.1.3 p.73 (partial match fails even in M-mode) is why the hypothesis must be strengthened. Oracle and arch-test alignment decide G. |
| R3 | `pmpCheck` result | PMP analysis: `bool`, caller picks 1/5/7. Compatibility analysis: `ExceptionType option`. | **`bool`** ([D53]). | P §12.3.2 steps 2 and 9 p.134: an implicit PTE access that fails PMP raises the access fault of the *original* access type, so the code cannot be chosen by `pmpCheck` from its own access kind (needed in WP7). |
| R4 | PMP storage | PMP analysis: per-entry arrays/maps. Compatibility analysis: raw CSR images in `MachineCSR`. | **Raw images** `pmpcfg0`, `pmpcfg2`, `pmpaddr0..15 :: regType` inside `MachineCSR` ([D52]). | P §3.7.1 Figure 31 p.71 defines the CSRs as packed images; consumer constraints F3, F5, F7 (§1.1) rule out maps. |
| R5 | `mtime`/`mtimecmp` | Compatibility analysis and plan: declared state (`clock` renamed `mtime`, new `c_mtimecmp`). Counters analysis: memory-backed CLINT words. | **Memory-backed** CLINT words in `MEM8`; no new declared timer state; `clock` is deleted ([D67]). | P §3.2.1 p.59: `mtime` and `mtimecmp` are *memory-mapped* registers; declared state is only correct with an MMIO dispatch in every load/store, which costs a case split in every HOL step theorem. |
| R6 | Platform interrupt inputs | Traps analysis: `MSIP`, `MEIP`, `SEIP_ext` are harness-set state. Counters analysis: `MSIP` from CLINT memory, `MEIP` constant 0. | `MSIP` from the CLINT `msip` word (memory-backed, like R5); `MEIP` and external `SEIP` are declared hidden per-hart booleans that the spec never writes, reset to false, settable only by the harness ([D42]). | P §3.1.9 p.44: MSIP is written through memory-mapped `msip`; MEIP/SEIP come from a platform interrupt controller, which is not modelled. |
| R7 | `mcycle`/`minstret` storage | CSR analysis: new `MachineCSR` fields. Compatibility analysis: keep top-level `c_cycles`/`c_instret`. | **Top-level** `c_cycles`/`c_instret` ([D68]). | Spec silent; they are already hidden in `prog` (F3). |
| R8 | `sstatus` write mask | CSR analysis: `0xC6122` (includes SUM). Status analysis: `0x86122`. | **`0x86122`**. Both give the same stored value because `legalize_mstatus` clears SUM. *WP7 amendment ([S19]):* SUM is writable from WP7 stage 2, so the effective mask is `0xC6122`. | SUM is RO0 when `satp.MODE` is read-only 0: P §3.1.6.4 p.35, §12.1.1.2 p.114. |
| R9 | `mstatus.SD` storage | Current L3, sail and the CSR analysis store SD. Status analysis: derive it on read. | **Derived on read**; stored SD/UXL/SXL/RO0 bits are don't-care ([D20]). | P §3.1.6.7 p.40 defines SD as a read-only function of FS/XS/VS; either is conformant; arbitrary HOL states decide. |
| R10 | Number of present CSR addresses | CSR analysis stated 116 (6 + 12 + 98). | Recount of its own table gives **114** (6 U + 11 S + 97 M). | Arithmetic (§3.6.1). |
| R11 | Plan WP2.4 "SRET illegal in M-mode if TSR" | Plan vs status/traps analyses. | **SRET in M-mode is legal whatever TSR is.** | P §3.1.6.6 p.37: TSR traps SRET "while executing in S-mode". |
| R12 | Plan WP3 M-mode PMP side condition "trivially true when priv = M and no entry is locked" | Plan and compatibility H3 vs PMP analysis. | Insufficient for 8-byte accesses under G = 0; add H4 (§1.5). | P §3.7.1.3 p.73. |
| R13 | Plan WP2.5 "R=0,W=1 → R=W=0" | Plan vs PMP analysis. | **R = W = X = 0**, L and A kept ([D49]). | P §3.7.1 p.71 only requires a legal value; sail's `PMP_ClearPermissions` decides. |
| R14 | Plan Appendix A: `hpmcounter3–31` RO0, `menvcfg` all zero, no `mconfigptr` | Plan vs CSR and counters analyses. | `hpmcounter3–31` **illegal** ([D25]); `menvcfg.FIOM` **writable** ([D29]); `mconfigptr` **exists**, reads 0 (P §3.1.17 p.53). | P §3.1.17 p.53 (mconfigptr must be implemented); P §3.1.18 p.54 (FIOM); U §4.4 p.68 (unimplemented counters). |
| R15 | Name of exception 6 | PMP analysis keeps `AMO_Misaligned`; compatibility analysis renames. | **`Store_AMO_Misaligned`** ([D7]). | P Table 16 p.50 names code 6 "Store/AMO address misaligned"; no consumer names the constructor. |

---

## 1. Current spec and compatibility constraints

Baseline: `riscv.spec` on `riscv-l3` at `55e74e68b`. Consumers as checked out on 2026-10-30: HOL `riscv-l3` (`step/`, `prog/`, `decompiler/`); HolBA `misc_fixes` (and the `riscv_lifter` branch); CakeML `73ba86109`, which builds against HOL `develop` (without the `riscv-l3` C changes). The privileged sections being replaced are L3 lines 89–780 (types, privilege, VM modes, CSR registers and records), 888–1600 (`is_CSR_defined`, `CSRMap`, `csrName`, exceptions, delegation, interrupts, `takeTrap`, `writeCSR`), 1774–2030 (translation), 4060–4280 (System instructions, `Fetch`) and 5236–5401 (`Next`, `initIdent`, `initMachine`).

### 1.1 Structural facts the rewrite must respect

- **F1. No consumer runs the spec's `Next`.** HOL step, CakeML and HolBA use `riscv_step$NextRISCV` (`step/riscv_stepScript.sml:48-61`), built on a hand-written `riscv_step$Fetch` (`:28-36`: misaligned PC gives `UNDEFINED`, then `translateAddr (pc, Instruction, Read)`, then `rawReadInst`). A PMP check added to the spec's `Fetch` is invisible to consumers unless it is also added to `riscv_step$Fetch_def`; if it is not, `NextRISCV` fetches from PMP-denied memory and no longer refines `Next`. This is a **soundness obligation on WP3**. Likewise `NextRISCV` does not take interrupts, so its theorems need a "no takeable interrupt" hypothesis (§1.5 H6). The spec's `Next`, interrupt check, `takeTrap`, HTIF and `initMachine` are used only by the SML emulator and can be rewritten freely.
- **F2. `#UNDEFINED` makes a function state-passing in the HOL export** (`architecture_def` returns `(Architecture, state)`). Every function the step libraries evaluate (`privilege`, `curPrivilege`, `in32BitMode`, `haveRVC`, `translateAddr`, `checkCSROp`, legalisers) must be total.
- **F3. `prog` turns every top-level `declare` into a separation-logic component unless hidden** (`prog/riscv_progScript.sml:10-15`; mechanism `common/stateLib.sml:295-325`). Hidden today: `c_update log totalCore done clock c_tlb c_instret c_cycles c_UCSR c_SCSR c_ReserveLoad c_HCSR c_ExitCode`. A stale hidden name is ignored. Anything M-mode step theorems read must stay visible; therefore `translateAddr` and the M-mode PMP path must not read `c_SCSR` (e.g. `satp`). *WP7 amendment ([S1]):* `translateAddr` reads `satp` only when the privilege it is given is not M, which it tests first, so the M-mode path still reads no `c_SCSR`.
- **F4. HolBA's `bmr_extra` (= `riscv_state_is_OK`) must hold before and after every lifted instruction** (`src/theory/tools/lifter/bir_inst_liftingScript.sml:158-221`). Only true invariants go there; state that instructions change (current privilege, `pmpcfg*`, `pmpaddr*`, `mstatus`) must be lifted BIR variables.
- **F5. The lifter can only turn word-valued hypotheses into BIR asserts** (`BMLI` returns `Imm8`/`Imm64`). `curPrivilege () s = Machine` cannot be lifted; `s.c_privilege s.procID = 3w` can.
- **F6. L3 allows the same field name in different register types** (`mie.SSIE` and `sie.SSIE` both exist), so unprefixed spec field names work in both `mstatus` and `sstatus`.
- **F7. No existing L3 spec has a function-typed record field**; maps exist only as top-level `declare`s. Treat a map inside `MachineCSR` as untested.
- **F8. HolBA's model is not an export of a committed spec**: `src/shared/l3-machine-code/riscv/model/riscvScript.sml` was hand-edited (HolBA `9cc7ffb9`: `mbadaddr→mtval`, `sbadaddr→stval`, `mhartid` at 0xF14, `csr >= 0xB01`), has no C, and its step library is a fork. WP4 replaces it with HOL's new export.

### 1.2 Keep / rename / remove table (privileged part of `riscv.spec`)

| Spec item (line) | Verdict | Note |
|---|---|---|
| `arch_base`, `construct Architecture {RV32I,RV64I,RV128I}` (93-98) | keep | used by `cond_rand_thms` (HOL step `:185`) |
| `archBase`, `architecture` (100-113) | rewrite | MXL encoding 1 = 32, 2 = 64, 3 = 128 (P §3.1.1 Table 11 p.27); today RV32I = 0. `architecture(0)` may stay `#UNDEFINED` only because nothing on the step path calls it ([D4]) |
| `archName` (115) | keep | |
| `priv_level`, `construct Privilege` (126-133) | rewrite: `{User, Supervisor, Machine}`, drop `Hypervisor` | 1.13 has no H mode; `10` is reserved (P §1.2 Table 1 p.11) |
| `privLevel` (135) | keep | U→`00`, S→`01`, M→`11` |
| `privilege` (143) | rewrite, **total** | `00`→U, `01`→S, `11`→M, `10`→U ([D2]) |
| `privName` (151) | keep, drop "H" | |
| `vm_mode`, `VM_Mode`, `vmType`, `isValidVM`, `vmMode`, `vmModeName` (161-220) | remove | 1.7 `mstatus.VM`; translation mode lives in `satp` |
| `ext_status`, `ExtStatus`, `extStatus`, `extStatusName` (221-256) | keep | encoding P Table 13 p.38 |
| `construct Interrupt {Software, Timer}`, `interruptIndex` (260-269) | rewrite | six constructors, codes 1, 3, 5, 7, 9, 11 (§4.2) |
| `construct ExceptionType` (271-283), `excCode`, `excName` | rewrite | §4.2; names per [D7] |
| `excType` (302) | remove | unused; partial |
| `register mcpuid` (344) | rename → `misa` (0x301) | §2.2; keep field name `C` |
| `register mimpid` (353) | rewrite as constant | §6.8 |
| `register mstatus` (358-373) | keep type name, new layout | §2.3; `MPRV` becomes bit 17 (was the 2-bit current privilege); `VM` removed; `MFS/MXS/MSD/MMPRV` → `FS/XS/SD/MPRV` |
| `register mtdeleg` (375) | remove → `medeleg` 0x302, `mideleg` 0x303 | §4.1.2 |
| `register mip`, `register mie` (380-400) | keep type names, new fields | §4.1.3 |
| `register mcause` (402-410) | keep type name; Interrupt bit 63, code 62:0 | §4.1.6 |
| `record MachineCSR`, `c_MCSR`, `component MCSR` (411, 667, 738) | keep names, change fields | §1.4.2 |
| `record HypervisorCSR`, `c_HCSR`, `component HCSR` (444, 666, 733) | remove | hide-list entry becomes stale |
| `register sstatus` (460) | keep name, now a view | §2.4 |
| `register sip`, `register sie` (470-478) | keep names, views | §4.1.3 |
| `record SupervisorCSR`, `c_SCSR`, `component SCSR` (480, 665, 728) | keep names, change fields | §1.4.3; stays hidden in prog |
| `register FPCSR`, `record UserCSR`, `c_UCSR`, `UCSR`, `fcsr` (502-517, 664, 697, 723) | keep | drop `cycle_delta/time_delta/instret_delta`; `fcsr` assign sets `FS := Dirty` only ([D20]) |
| `lift_mip_sip`, `lift_mie_sie`, `lower_sip_mip`, `lower_sie_mie` (521-547) | rewrite | views masked by `mideleg` (§4.1.3) |
| `update_mstatus` (549-571) | rewrite → `legalize_mstatus` | §2.3.3 |
| `lift_mstatus_sstatus`, `lower_sstatus_mstatus` (574-603) | rewrite | §2.4 |
| `popPrivilegeStack`, `pushPrivilegeStack` (605-628) | remove | §4.6, §4.7 |
| `record SynchronousTrap {trap; badaddr}` (632) | keep; `badaddr :: vAddr option` → `tval :: regType` | §4.1.7 |
| `construct TransferControl {Trap, BranchTo, Ereturn, Mrts}` (637) | `Ereturn`→`Mret`, add `Sret`, remove `Mrts` ([D8]) | consumers match `\| _ => NONE` |
| `declare clock` (654) | remove ([D67]) | prog hide entry becomes stale |
| `c_instret`, `c_cycles` (656-657) | keep, as storage of `minstret`/`mcycle` ([D68]) | hidden |
| `c_gpr c_fpr c_PC c_Skip c_NextFetch c_ReserveLoad` | keep | |
| `c_ExitCode`, `done`, `exitCode` | keep (harness) | HTIF logic leaves `Next` ([D13]) |
| `curArch()` (760) | remove | |
| `in32BitMode()` (763) | keep name; body `MCSR.misa.MXL == 1` ([D4]) | pure; always false here |
| `haveRVC()` (766) | keep name; body `MCSR.misa.C` | |
| `legalizeEPC` (769) | rewrite → `write_xepc`/`read_xepc` | §4.1.5 |
| `curPrivilege()` (772) | keep name and unit shape; body `privilege(c_privilege(procID))` ([D3]) | |
| `curEPC()` (775), `sendIPI` (783) | remove | |
| `csrRW`, `csrPR`, `check_CSR_access`, `is_CSR_defined` (883-922) | keep names and signatures, rewrite bodies | §3.2 |
| `component CSRMap(csr)` (926-1132) | keep as a component | `case _ => #UNDEFINED` only for addresses rejected by `is_CSR_defined` |
| `csrName` (1134-1240) | rewrite | 1.13 names; hex fallback for absent addresses |
| `StateDelta`, `c_update`, `Delta`, logging (1250-1450) | keep; remove `log_tohost` | |
| `setTrap`, `signalException`, `signalAddressException` (1451-1468) | keep names; carry `tval` | §4.6 |
| `signalEnvCall` (1470) | rewrite | U→8, S→9, M→11 |
| `checkDelegation` (1482) and `src/checkDelegation.sml` | remove (also `HELPERS` in `src/Makefile`) | replaced by non-recursive `ExcDest` (§4.4) |
| `checkPrivInterrupt`, `checkInterrupts` (1502-1555) | rewrite | §4.5 |
| `takeTrap` (1557-1593) | rewrite | §4.6 |
| `component CSR(n)`, `writeCSR(csr, val)` (1595-1610) | keep names and signatures | logging of the read-back value kept |
| `writeFPRS`, `writeFPRD` (1642-1653) | keep; `MFS/MSD` → `FS` | |
| translation: `permType`, `checkMemPermission`, `SV_PTE`, `walk64`, `TLBMap`, `c_tlb`, `translate64`, ... (≈1774-2010) | remove | WP7 re-adds Sv39/48 |
| `translateAddr(vAddr, ft, ac)` (2012) | keep name and signature; body = identity ([D5]) | the single WP7 hook |
| *(new)* `pmpCheck`, `effectivePrivilege` | add | §5.4, §2.3.6 |
| `System > ECALL`, `EBREAK` (4096, 4102) | keep, rewrite bodies | §4.7 |
| `System > ERET`, `MRTS` (4107, 4113) | remove → `MRET`, `SRET` | §4.7 |
| `System > WFI` (4126) | keep constructor; decode `0x10500073` | §4.7.6 |
| `checkCSROp(csr, rs1, a)` (4130) | keep name and signature | extra conditions via one helper ([D9]) |
| `System > CSRRW..CSRRCI` (4136-4206) | keep constructors, one shared body | fixes `CSRRWI` bug (§1.6) |
| `System > SFENCE_VM(rs1)` (4209) | rename → `SFENCE_VMA(rs1, rs2)` | §4.7.7 |
| `FetchResult`, `Fetch()` (4242-4280) | keep shape; add PMP per parcel | §5.6.3 |
| `Next` (5282), `tickClock`, `incrInstret`, `checkTimers`, `CYCLES_PER_TIMER_TICK` | rewrite | §4.5, §6.5 |
| `initIdent` (5358), `initMachine` (5370) | rewrite | §6.7 |
| `initRegs(pc)` (5389) | keep | |
| Decode/print/Encode of `ERET`, `MRTS`, `WFI`, `SFENCE_VM` (4473-4477, 4732-4745, 4955-4961) | rewrite | §4.7.1 |

### 1.3 Consumer dependencies

Classes: **U** unaffected; **R** mechanical rename (map in §1.6); **N** needs new theorem or logic.

**HOL `step/riscv_stepScript.sml`, `riscv_stepLib.sml`.**

| Line | Dependency | Class | Change |
|---|---|---|---|
| Script 28-36 | `Fetch_def` | **N** | add the PMP fetch check per parcel with privilege `c_privilege` (F1) |
| 48-61 | `NextRISCV_def` | U | WP3 adds trap/`Mret` arms |
| 69, 81, 95, 110, 592; Lib 292, 296, 411 | `(s.c_MCSR s.procID).mcpuid.C` | R | `misa.C` |
| 76-115 | `NextRISCV_Half_noC` proof defs | U or N | needs more defs if `signalException` reads instruction bits for `mtval` |
| 590 | `bare = ... mstatus.VM = 0w` | R | delete; contract §1.5 replaces it |
| 591, 593, 869-948 | `mcpuid.ArchBase`, `^archbase = 0w`, `<> 0w` | R + value | `misa.MXL`; RV32 test becomes `1w` |
| 605 | `datatype_rewrites ... "VM_Mode"` | R | delete `VM_Mode` |
| 648-651 | `EV [translateAddr_def, MCSR_def, vmType_def, ...] [[bare]]` | R | `EV [translateAddr_def] [] []` (*WP7 amendment:* deleted in WP7 stage 3; the step theorems use the lemma `translateAddr_Machine` instead, `design-smode.md` §1.4) |
| 653-655 | `EV [in32BitMode_def, curArch_def, MCSR_def, architecture_def, not1]` | R | `[in32BitMode_def, MCSR_def]` |
| 689-726 | `Fetch`, `Fetch32`, `Fetch16` with hypothesis `mstatus.VM = 0w` | **N** | PMP lemma and contract §1.5 |
| 826-849 | load/store/AMO rewrite list, `signalAddressException` avoidance | **N** | `pmpCheck` and misaligned trap; avoid lists need alignment hypotheses for `LW LH LWU LHU SW SH` (LD/SD already carry `aligned_d`) |

**HOL `prog/`.** `riscv_progScript.sml:10-15` hide list: `"clock"`, `"c_HCSR"`, `"c_tlb"` become stale (harmless); **do not hide `c_privilege`**. `:51-55` `riscv_ID id mcsr = ... * cond (mcsr.mstatus.VM = 0w)` is **N**: replace by `riscv_c_privilege id 3w * cond (H2 ∧ H3 ∧ H4)` (§1.5), keeping two arguments ([D11]). `:70-78` `mcpuid.ArchBase = 2w`, `mcpuid.C` are R (`misa.MXL = 2w`, `misa.C`). `riscv_progLib.sml:284-289` `mkselnm "MachineCSR" "mcpuid"`, `("mcpuid","ArchBase")`, `("mcpuid","C")` are R and fail at load time if not changed. Decompilers (`decompiler/*.sml`, `examples/machine-code/graph/file_readerLib.sml:296-298`) are U.

**HolBA lifter (`src/theory/tools/lifter/bir_lifting_machinesScript.sml`).**

| Line | Dependency | Class | Change |
|---|---|---|---|
| 934, 1185-1189 | `mstatus.VM = 0w` in `riscv_state_is_OK` | R + N | delete; H2 (`~mstatus.MPRV`) may be added (it is invariant except under `mstatus` writes, which are lifted) |
| 967-968 | `mcpuid.ArchBase <> 0w`, `<> 1w` | R | `misa.MXL` |
| 1036-1038 | `BVar "MPRV" ... Imm8 (w2w(...mstatus.MPRV))` | R | type error otherwise; `Imm8 (w2w (ms.c_privilege ms.procID))`, BIR name `"priv"` ([D12]) |
| 1033-1053 | `mhartid`, `mscratch`, `mepc`, `reg'mcause`, `mtval`, `reg'mip` | U | names kept |
| new | `pmpcfg0`, `pmpcfg2`, `pmpaddr0-15`, `reg'mstatus`, `mtvec`, `mie` | **N** | raw images lift as `Imm64` ([D52]) |

Vendored step fork `src/shared/l3-machine-code/riscv/step/`: Script 552-555, 565, 608-615 R as above; 554 `privilege_level = mstatus.MPRV` → `^s.c_privilege ^s.procID` (stays 2-bit, `= 3w` still parses); 657, 670 **N**; 776-786 EV lists add the new access helper ([D9]); **788-812 `riscv_privilege_cases` (4-arm case over `mstatus.MPRV = 0w..3w`) is N**: restate as 3 constructors on `c_privilege`, with `2w` mapping as `privilege` does; 815 ``privLevel (curPrivilege () s)`` U by [D3]; Simps 43-83 `writeCSR_conv` is **N**: add every `legalize_*` def and record rewrites for the new register types. `bir_lifting_machinesLib_instances.sml:623-629` may need `type_rws` for `mstatus`, `misa`. Backlifter (`bir_riscv_backlifterScript.sml:252-253, 430, 442, 1130-1229`) R (`"MPRV"` expression and name). `selftest_riscv.sml:313-336` and its log are **N**: `30405073`/`30005073` (`csrwi mie,0`, `csrwi mstatus,0`) now write (CSRRWI fix) and the log must be regenerated. `examples/riscv/kernel-trap/kernel_trap_spec_riscvScript.sml:92, 225` R (`m.c_privilege m.procID = 3w`); `:286` `mepc = 0xFFFFFFFFFFFFFFFCw && ...` is **N** (new `mepc` legalisation, §4.1.5).

**CakeML `compiler/encoders/riscv`.** `riscv_targetScript.sml:19-24` `riscv_ok`: delete `mstatus.VM = 0w` (R), rename `mcpuid.ArchBase = 2w` → `misa.MXL = 2w` (R), add H1–H4 and H6 (N). `:287-296` `riscv_proj`: must include every field `riscv_ok` reads (`c_privilege`, `mstatus`, `pmpcfg0`, `pmpcfg2`), N. `proofs/riscv_targetProofScript.sml:14-37, 245-250` R + new conjuncts; still closed by `UPDATE_APPLY` because CakeML's instruction subset writes none of them. Upstreaming (WP6) needs a CakeML change in the same window, including the existing C changes.

**Summary.** New logic is caused by three changes only: PMP in fetch/load/store; privilege moving out of `mstatus`; CSR legalisation. About 60 sites are renames.

### 1.4 State shape

#### 1.4.1 Top-level declarations

| Declaration | Type | prog | Why |
|---|---|---|---|
| `c_privilege` *(new)* | `id -> priv_level` (bits(2)) | **visible**; fixed to `3w` in `riscv_ID` | [D1], F5. Only writer: `setPrivilege(p) = c_privilege(procID) <- privLevel(p)`, so `10` is unreachable |
| `c_gpr c_fpr c_PC c_Skip c_NextFetch c_ReserveLoad c_update` | unchanged | unchanged | |
| `c_MCSR`, `c_SCSR`, `c_UCSR` | records §1.4.2–1.4.3 | MCSR visible; S, U hidden | F3 |
| `c_cycles`, `c_instret` | `id -> regType`, storage of `mcycle`/`minstret` | hidden | [D68] |
| `c_minstret_written` *(new)* | `id -> bool`, model-internal | hide (add) | §6.5 |
| `c_extMEIP`, `c_extSEIP` *(new)* | `id -> bool`, platform inputs, never written by the spec | hide (add) | [D42] |
| `c_ExitCode`, `done`, `log`, `totalCore`, `procID` | unchanged | hidden | |
| removed: `clock`, `c_HCSR`, `c_tlb` | | stale hide entries | |

`mtime`, `mtimecmp` and `msip` are **not** declared state; they are words of `MEM8` (§6.6).

#### 1.4.2 `MachineCSR` (keep name; `c_MCSR`, `MCSR`)

- Kept: `mhartid :: regType`, `mstatus :: mstatus`, `mtvec :: regType`, `mie :: mie`, `mscratch :: regType`, `mepc :: regType`, `mcause :: mcause`, `mip :: mip` (stores only the software-writable bits, §4.1.3).
- Renamed: `misa :: misa` (was `mcpuid`); `mtval :: regType` (was `mbadaddr`).
- Added (raw `regType` + legaliser unless noted): `medeleg`, `mideleg`, `mcounteren`, `mcountinhibit`, `menvcfg`, `pmpcfg0`, `pmpcfg2`, `pmpaddr0` … `pmpaddr15`.
- Constants, not stored: `mvendorid`, `marchid`, `mimpid`, `mconfigptr` (all 0, §6.8).
- Removed: `mtdeleg mtimecmp mtime_delta mbase mbound mibase mibound mdbase mdbound mtohost mfromhost`.
- Accessors over the raw images: `pmpcfg_ent(i::bits(4)) :: pmpcfg` (8-bit register type: `L` 7, `A` 4:3, `X` 2, `W` 1, `R` 0) selecting byte `i<2:0>` of `pmpcfg0` (i < 8) or `pmpcfg2`; `pmpaddr(i::bits(4))` a 16-way match.

**Storage rule.** A CSR whose fields the spec reads individually is an L3 register type with a `reg'` function (`mstatus`, `misa`, `mie`, `mip`, `mcause`, and the views `sstatus`, `sie`, `sip`). Everything else is raw `regType` plus a legaliser. No function-typed record fields (F7).

#### 1.4.3 `SupervisorCSR`, `UserCSR`

- `SupervisorCSR { stvec, scounteren, senvcfg, sscratch, sepc, stval, satp :: regType; scause :: mcause }`. Removed: `stimecmp stime_delta sbadaddr sptbr sasid`. `sstatus`, `sie`, `sip` are views.
- `UserCSR { fpcsr :: FPCSR }`.
- Note: the U-mode counter-enable check reads `scounteren` (in hidden `c_SCSR`); this only affects U-mode CSR theorems, never M-mode ones, because the check short-circuits in M (§6.4).

#### 1.4.4 Names and signatures that must not change

`translateAddr :: (vAddr, fetchType, accessType) -> pAddr option` (*WP7 amendment ([S1], [S2]):* `translateAddr :: (vAddr, fetchType, accessType, Privilege) -> TransResult`, and `fetchAddr`/`dataAddr` return `TransResult`, `design-smode.md` §3.11); `haveRVC()`, `in32BitMode()`, `curPrivilege() :: Privilege`; `privLevel`, total `privilege`; `checkCSROp :: (creg, reg, accessType) -> bool`; `check_CSR_access :: (csrRW, csrPR, Privilege, accessType) -> bool`; `is_CSR_defined :: creg -> bool`; `csrRW`, `csrPR`; `component CSRMap(creg)`, `component CSR(creg)`; `writeCSR :: (creg, regType)`; `setTrap`, `signalException(ExceptionType)`, `signalAddressException(ExceptionType, vAddr)`; `branchTo`; `rawReadInst`, `rawReadData`, `rawWriteData`; `component Skip/PC/NextFetch/MCSR`; constructors `BranchTo`, `Trap`, `NoException` and every `instruction` constructor including `System(CSRRW…)`.

### 1.5 Step-theorem hypothesis contract (replaces `mstatus.VM = 0w`)

M-mode step theorems carry exactly these word-level conjuncts ([D10]):

| Id | Conjunct | Needed by |
|---|---|---|
| H1 | `s.c_privilege s.procID = 3w` | every instruction (fetch PMP check, CSR privilege) |
| H2 | `~(s.c_MCSR s.procID).mstatus.MPRV` | explicit loads, stores, AMOs (effective privilege, §2.3.6) |
| H3 | `P_unl mcsr :≡ (mcsr.pmpcfg0 && 0x8080808080808080w = 0w) ∧ (mcsr.pmpcfg2 && 0x8080808080808080w = 0w)` (no entry locked) | fetch and data |
| H4 | `P_nt mcsr :≡ (((mcsr.pmpcfg0 >>> 1) ?? mcsr.pmpcfg0) && 0x0808080808080808w = 0w) ∧ (same for pmpcfg2)` (every entry's `A<1> = A<0>`, i.e. A ∈ {OFF, NAPOT}) | 8-byte data accesses only (LD, SD, FLD, FSD, AMO*.D, LR.D, SC.D) |
| H5 | natural alignment of the data address | loads, stores, AMOs (misaligned accesses trap, [D55]) |
| H6 | `~(s.c_MCSR s.procID).mstatus.MIE` (or `mie && 0x888 = 0w`) | `NextRISCV` refinement: no interrupt can be taken in M-mode (§4.5) |

**Lemma** (one, in `riscv_stepScript`): H1 ∧ H3 ∧ (access naturally aligned with width ≤ 4, or a 2-byte fetch parcel) ⇒ `pmpCheck(...) = T`; and H1 ∧ H3 ∧ H4 ∧ (8-byte aligned access) ⇒ `pmpCheck(...) = T`. Why H4 is needed with G = 0 (R2, R12): an entry matching only some bytes of an access makes it fail **even in M-mode with L = 0** (P §3.7.1.3 p.73; sail `pmp/pmp_control.sail:154-158`). With G = 0 all region bounds are multiples of 4, so only 8-byte accesses can partially match, and only via NA4 or TOR; NAPOT regions are at least 8 bytes and 8-aligned (§5.3). CakeML and prog never write PMP, so H4 holds from reset (all OFF).

Where each consumer puts the contract: **prog** in `riscv_ID`; **CakeML** in `riscv_ok` and `riscv_proj`; **HolBA** may put H2 in `riscv_state_is_OK` (MRET clears MPRV when leaving M and traps never set it; P §3.1.6.4 p.35), but H1, H3, H4 must be lifted asserts on BIR variables because MRET and `csrw pmpcfg0` (S3K `trap_resume`) change them (F4).

### 1.6 Rename map and required fixes

```
(s.c_MCSR s.procID).mcpuid.C          -> (s.c_MCSR s.procID).misa.C
(s.c_MCSR s.procID).mcpuid.ArchBase   -> (s.c_MCSR s.procID).misa.MXL   ; RV32 test 0w -> 1w; RV64 stays 2w
mkselnm "MachineCSR" "mcpuid" / "mcpuid" "ArchBase" / "mcpuid" "C"
                                      -> "MachineCSR" "misa" / "misa" "MXL" / "misa" "C"
(s.c_MCSR s.procID).mstatus.VM = 0w   -> (delete; add the §1.5 contract)
(s.c_MCSR s.procID).mstatus.MPRV      -> s.c_privilege s.procID        ; where it meant "current privilege"
w2w((ms.c_MCSR ms.procID).mstatus.MPRV) -> w2w (ms.c_privilege ms.procID); BIR name "MPRV" -> "priv"
(s.c_MCSR s.procID).mbadaddr          -> (s.c_MCSR s.procID).mtval    ; HOL side only
"VM_Mode" in datatype_rewrites lists  -> (delete)
vmType_def in translateAddr EV        -> (delete), also [[bare]]
[in32BitMode_def, curArch_def, MCSR_def, architecture_def, not1] -> [in32BitMode_def, MCSR_def]
prog hide list: add "c_minstret_written", "c_extMEIP", "c_extSEIP"; "clock", "c_HCSR", "c_tlb" become stale
TransferControl Ereturn -> Mret (+ Sret); Mrts removed
System ERET/MRTS -> MRET/SRET; SFENCE_VM(rs1) -> SFENCE_VMA(rs1, rs2)
spec-internal: mstatus.MFS/MXS/MSD/MMPRV -> FS/XS/(SD derived)/MPRV; AMO_Misaligned -> Store_AMO_Misaligned
```

Fixes that are not choices:
1. **`CSRRWI` with `uimm = 0` must write and must check write access** (U §4.2.1 Table 21 p.63). Today (L3 4171-4180) it passes `Read` and skips the write, so `csrwi mstatus,0` is a no-op.
2. **Non-existent CSRs are reserved** (P §2.1 p.13); the model raises illegal instruction ([D24]); `CSRMap`'s `#UNDEFINED` default stays unreachable behind `is_CSR_defined`.
3. **`misa` write suppression** when clearing C at a PC that is not 4-aligned (P §3.1.1 p.29; §2.2.3).
4. **`mepc[1]` is masked on read when IALIGN = 32 but stays writable** (P §3.1.14 p.48; §4.1.5).
5. **`satp` writes with an unsupported MODE have no effect** (P §12.1.11 p.125), so `translateAddr` is exactly the identity. (*WP7 amendment:* Sv39, Sv48 and Sv57 become supported in its stage 2, and `translateAddr` translates below M, `design-smode.md` §3.)
6. **`takeTrap` must not clear `MPRV` or the load reservation** (§4.6).
7. **Misaligned LR raises 4, not 6** (§5.6.1).
8. **`csrName(0x144)` returns "sip"**, not "mip".
9. Side findings for WP1: `setFP_Underflow`/`setFP_Inexact` (≈L3 871-880) set `fcsr.OF`; the 1.7 `MFS`/`MXS` positions (13:12, 15:14) are wrong for 1.13 (FS 14:13, XS 16:15; P Fig. 8 p.32); FP arithmetic accrues no IEEE flags except NV on compares.

---

## 2. Privilege and status registers (`misa`, `mstatus`, `sstatus`)

### 2.1 Privilege levels (P §1.2 p.11–12)

| Level | Encoding | Name | This hart |
|---|---|---|---|
| 0 | `00` | User (U) | implemented, validated |
| 1 | `01` | Supervisor (S) | implemented (`misa.S = 1`), not validated |
| 2 | `10` | reserved (Hypervisor in 1.7) | does not exist |
| 3 | `11` | Machine (M) | implemented, validated |

Legal mode sets are {M}, {M,U}, {M,S,U} (P Table 2 p.12); this hart is {M,S,U}. Reset enters M (P §3.4 p.63).

Rules:
1. `Privilege = {User, Supervisor, Machine}`; `privLevel`: U→`00`, S→`01`, M→`11`.
2. `privilege(b::bits(2))` is total: `00`→U, `01`→S, `11`→M, **`10`→U** ([D2]). `10`→U is also what `legalize_mstatus` stores for `MPP = 10` (§2.3.3), so decoding a stored and a freshly legalised `MPP` always agree.
3. The current privilege is **not visible in any CSR** in 1.13. It is `c_privilege` (§1.4.1), replacing `curPrivilege() = privilege(MCSR.mstatus.MPRV)` (L3 772), which read the 1.7 `mstatus.PRV` field.
4. CSR privilege check: §3.1.

### 2.2 `misa` (0x301, MRW) (P §3.1.1 p.27–29)

#### 2.2.1 Layout (P Figure 2, Tables 11–12 p.27–28)

| Bits | Field | Value | Writable |
|---|---|---|---|
| 63:62 | MXL | `10` (XLEN 64) | read-only (p.27) |
| 61:26 | 0 | 0 | RO0 (p.28) |
| 25:0 | Extensions | see below | WARL |

| Bit | Letter | Value | Writable ([D14]) | Note |
|---|---|---|---|---|
| 0 | A | 1 | no | |
| 1 | B | 0 | no | Zba/Zbb/Zbs absent |
| 2 | C | 1 at reset | **yes** | IALIGN rule §2.2.3 |
| 3 | D | 1 | no | D depends on F (p.29) |
| 4 | E | 0 | no | complement of I (p.29) |
| 5 | F | 1 | no | |
| 7 | H | 0 | no | |
| 8 | I | 1 | no | |
| 12 | M | 1 | no | |
| 18 | S | 1 | no | S depends on U (p.29) |
| 20 | U | 1 | no | |
| 21 | V | 0 | no | |
| 23 | X | 0 | no | no non-standard extensions |
| others | | 0 | no | |

Constants: `MISA_RESET = 0x8000_0000_0014_112D` (A C D F I M S U; the "maximal set", P §3.1.1 p.27, §3.4 p.63); with C = 0 the value is `0x8000_0000_0014_1129`. `MISA_WMASK = 0x4`.

#### 2.2.2 Spec rules

- p.29: enabling x while disabling a y that x depends on disables both (cannot arise with only C writable).
- p.29: "If an instruction that would write misa increases IALIGN, and the subsequent instruction's address is not IALIGN-bit aligned, the write to misa is suppressed, leaving misa unchanged."
- p.28: a disabled extension behaves as if not implemented; p.29: state of a re-enabled extension is UNSPECIFIED (C has no state).
- P §2.3.3 p.25: WARL writes never trap.

#### 2.2.3 `legalize_misa(v, m, pc) -> misa`

`pc` is the address of the writing CSR instruction; CSR instructions are 32-bit, so the subsequent instruction is at `pc + 4` (L3 `PC + Skip`, `Skip = 4`).
1. `newC := v<2>`.
2. If `newC = 0 ∧ m.C = 1 ∧ pc<1> = 1` (equivalently `(pc+4)<1> = 1`): return `m` (whole write suppressed; sail `legalize_misa`, `core/sys_regs.sail:130`, tests `nextPC[1]`).
3. Else return `m` with `C := newC`; all other bits keep their constant values.

**Effects of `misa.C`** (replaces every `haveRVC()` = `MCSR.mcpuid.C`, L3 766):
- `misa.C = 0` ⇒ IALIGN = 32; a taken branch/jump to an address with bit 1 set raises cause 0 (already in `riscv-l3` commit 116d411e1); 16-bit parcels decode as illegal; `mepc<1>`, `sepc<1>` are masked on read (§4.1.5).
- Invariant: with `misa.C = 0`, no reachable state has `PC<1> = 1` (suppression, jump checks, 4-aligned `mtvec`, masked `xepc`).

**Replaces:** `register mcpuid` (L3 344) and CSR 0xF00 (L3 916, 993, 1199); `initIdent`'s `mcpuid` assignments (L3 5359-5364); `curArch()`/`in32BitMode()` (L3 760-764), now constant RV64 ([D4], [D19]).

### 2.3 `mstatus` (0x300, MRW), RV64 (P §3.1.6 p.31–41)

#### 2.3.1 Field table (P Figure 8 p.32)

"Reset" values marked **(M)** are spec-mandated (P §3.4 p.63); others are UNSPECIFIED and chosen per [D70].

| Bits | Field | Status on this hart | Reset | In `sstatus`? |
|---|---|---|---|---|
| 0 | WPRI | RO0 (P §2.3.1 p.24) | 0 | no |
| 1 | SIE | RW (S implemented; RO0 only without S, p.32) | 0 | RW |
| 2 | WPRI | RO0 | 0 | no |
| 3 | MIE | RW | **0 (M)** | no |
| 4 | WPRI | RO0 | 0 | no |
| 5 | SPIE | RW | 0 | RW |
| 6 | UBE | RO0 (little-endian only, p.36) | 0 | visible, RO0 |
| 7 | MPIE | RW | 0 | no |
| 8 | SPP | RW, 0 = U, 1 = S (p.32, P §12.1.1 p.113) | 0 | RW |
| 10:9 | VS | RO0 ([D18]; allowed with S and no V, p.38) | 0 | visible, RO0 |
| 12:11 | MPP | WARL, legal {`00`,`01`,`11`} (p.33); `10`→`00` ([D15]) | `00` | no |
| 14:13 | FS | WARL, all four values legal ([D16]) | `00` (Off) ([D70]) | RW |
| 16:15 | XS | RO0 (no other user extension state, p.38) | 0 | visible, RO0 |
| 17 | MPRV | RW (U implemented) | **0 (M)** | no |
| 18 | SUM | **RO0**: "read-only 0 if S-mode is not supported or if satp.MODE is read-only 0" (p.35; P §12.1.1.2 p.114); `satp.MODE` is read-only 0 because writes with an unsupported MODE have no effect (P §12.1.11 p.125). sail: `SUM = if virtual_memory_supported() then v[SUM] else 0`. *WP7 amendment ([S19]):* RW from WP7 stage 2, where `satp` accepts Sv39, Sv48 and Sv57 | 0 | visible, RO0 (RW from WP7) |
| 19 | MXR | RW (S implemented); no effect (no paging; never affects PMP, p.35) | 0 | RW |
| 20 | TVM | RW (S implemented); effect only in S (§2.3.7) | 0 | no |
| 21 | TW | RW; effect only in S/U (§2.3.7) | 0 | no |
| 22 | TSR | RW (S implemented); effect only in S | 0 | no |
| 23 | SPELP | RO0 (no Zicfilp, P §3.1.6.8 p.41) | 0 | visible, RO0 |
| 24 | SDT | RO0 (no Ssdbltrp, P §12.1.1.5 p.115) | 0 | visible, RO0 |
| 31:25 | WPRI | RO0 | 0 | no |
| 33:32 | UXL | read-only `10` ([D19], p.34) | `10` | visible, RO |
| 35:34 | SXL | read-only `10` | `10` | no |
| 36 | SBE | RO0 | 0 | no |
| 37 | MBE | RO0 | **0 (M)** | no |
| 38 | GVA | RO0 (no H) | 0 | no |
| 39 | MPV | RO0 (no H) | 0 | no |
| 40 | WPRI | RO0 | 0 | no |
| 41 | MPELP | RO0 (no Zicfilp) | 0 | no |
| 42 | MDT | RO0 (no Smdbltrp, P §3.1.6.2 p.33; no reset-to-1 rule) | 0 | no |
| 62:43 | WPRI | RO0 | 0 | no |
| 63 | SD | read-only, derived: `SD = (FS = 11)` (since XS = VS = 0; p.40) ([D20]) | 0 | visible, RO |

`mstatush` (0x310) is RV32-only; on RV64 it is reserved, so access is illegal (P §2.7 p.26, §3.1.6 p.32).

#### 2.3.2 Constants

```
MSTATUS_WMASK = 0x0000_0000_007A_79AA   -- SIE MIE SPIE MPIE SPP MPP FS MPRV MXR TVM TW TSR
MSTATUS_CONST = 0x0000_000A_0000_0000   -- SXL = 2, UXL = 2
MSTATUS_SD    = 0x8000_0000_0000_0000
MSTATUS_RESET = 0x0000_000A_0000_0000   -- read value after reset
```

#### 2.3.3 `legalize_mstatus(v :: dword, misa) -> mstatus`

Applied to every explicit write of 0x300 (and, via §2.4, of 0x100). The CSR instruction forms the full 64-bit write value first (§3.2).
1. `w := v && MSTATUS_WMASK` (RO0/WPRI fields become 0; SD, XS, UXL, SXL of `v` are discarded).
2. MPP (p.33: "xPP fields are WARL fields that can hold only privilege mode x and any implemented privilege mode lower than x"): legal values are `11`, `01` iff `misa.S`, `00` iff `misa.U`. If `w<12:11>` is illegal, set it to `00` if `misa.U` else `11`. On this hart (S, U read-only 1) this is: `if w<12:11> = 10 then w<12:11> := 00` ([D15]; sail: `lowest_supported_privLevel()`).
3. FS unchanged (all values legal, [D16]).
4. Store `w`. (UXL/SXL/SD are not stored; they are produced by the read, [D20].)

The result is independent of the old value (as in sail) and depends on `misa` only through the constant S/U bits, so writing `misa` never changes another CSR's legal set (no P §2.4 field modulation, §3.4). **Replaces** `update_mstatus` (L3 549-571), the 1.7 layout (L3 358-373) and the `VM` field handling.

#### 2.3.4 Reading `mstatus`

`read_mstatus() = (stored && MSTATUS_WMASK) || MSTATUS_CONST || (if stored<14:13> = 11 then MSTATUS_SD else 0)`. Every HOL state therefore reads a legal value, except `MPP = 10`, which `privilege()` decodes as U ([D2]).

#### 2.3.5 Global interrupt enables (P §3.1.6.1 p.32)

- An interrupt targeting M is globally enabled iff `cur < M` or (`cur = M` ∧ `MIE = 1`).
- An interrupt targeting S is globally enabled iff `cur = U` or (`cur = S` ∧ `SIE = 1`); never when `cur = M`.
- "Interrupts for higher-privilege modes, y>x, are always globally enabled regardless of the setting of the global yIE bit": M-level interrupts are always enabled in U whatever MIE is.
This replaces `checkInterrupts`' `curIE = MCSR.mstatus.MIE` (L3 1531-1533). The selection algorithm is §4.5. The trap-entry and xRET updates of MIE/MPIE/MPP/SIE/SPIE/SPP/MPRV are defined once, in §4.6 and §4.7.4–4.7.5.

#### 2.3.6 MPRV, MXR, SUM (P §3.1.6.4 p.35)

- **Effective privilege for explicit data accesses** (loads, stores, LR/SC, AMOs, FP loads/stores; not fetch):
  `effectivePrivilege() = if mstatus.MPRV then privilege(mstatus.MPP) else curPrivilege()` ([D22]; sail `sys/sys_control.sail:11`). Instruction fetch always uses `curPrivilege()` ("Instruction address-translation and protection are unaffected by the setting of MPRV"). For PMP only M vs non-M matters, so effective S behaves like U. XLEN is 64 in every mode, so the "XLEN of MPP" rule is vacuous.
- **Reachable-state invariant**: `cur ≠ M ⇒ MPRV = 0` (reset clears it; only an M-mode `mstatus` write sets it; `sstatus` does not expose it; every xRET to a mode below M clears it; trap entry never lowers privilege). So [D22] equals the "only in M-mode" form (plan WP2.5) on reachable states; step theorems use H2 (§1.5).
- **MXR**: storage only (no paging; p.35: MXR and SUM "have no impact on whether access-fault exceptions are raised due to PMAs or PMP").
- **SUM**: RO0 (§2.3.1). WP7 (Sv39) makes it writable by adding bit 18 to `MSTATUS_WMASK` and the `sstatus` write mask; nothing else changes.
- *WP7 amendment ([S19], `design-smode.md` §2.1, §3.5).* Done in WP7 stage 2: `MSTATUS_WMASK = 0x7E79AA`. MXR and SUM now take part in translation (the leaf checks of `ptePermits`), and SUM also applies with MPRV = 1 and MPP = S (p.35); neither affects the PMP.

#### 2.3.7 TVM, TW, TSR (P §3.1.6.6 p.37)

| Bit | Effect when 1 | In M | In U | In S (validated by WP7) |
|---|---|---|---|---|
| TVM | `satp` accesses and SFENCE.VMA are illegal | none | none (already illegal by privilege) | illegal |
| TW | WFI illegal if not complete within bounded time | none (WFI is a NOP, [D23]) | WFI **always** illegal, regardless of TW, because S is implemented (p.37) | the time limit is zero: illegal when TW = 1 and no interrupt is pending and enabled in `mie` (`read_mip() && mie = 0`), else a NOP; NOP when TW = 0 ([S20], revising [D23]) |
| TSR | SRET illegal | none: **SRET in M is legal whatever TSR is** (p.37: "while executing in S-mode"; R11) | SRET always illegal | illegal |

#### 2.3.8 UXL, SXL (P §3.1.6.3 p.34; §12.1.1.1 p.114)

Both read-only `10`, explicitly permitted (p.34). XLEN = 64 in every mode; `in32BitMode()` is constant false; no narrow-XLEN rules (truncation, sign extension, address wrap) apply. sail: "We don't support dynamic changes to SXL and UXL".

#### 2.3.9 FS, XS, SD (P §3.1.6.7 p.37–41)

Encoding (P Table 13 p.38): `00` Off, `01` Initial, `10` Clean, `11` Dirty.

- **FS = Off traps** (p.38: "any instruction that attempts to read or write the corresponding state will cause an illegal-instruction exception"). Predicate `fpEnabled() := mstatus.FS ≠ 00`. Checked at execution before any other effect, for:
  1. every OP-FP instruction (.S and .D: FADD, FSUB, FMUL, FDIV, FSQRT, FMIN, FMAX, FSGNJ*, FCVT* both directions, FMV.X.W/FMV.W.X/FMV.X.D/FMV.D.X, FCLASS, FEQ, FLT, FLE);
  2. FMADD, FMSUB, FNMSUB, FNMADD;
  3. FLW, FLD, FSW, FSD (stores and compares *read* FP state);
  4. C.FLD, C.FLDSP, C.FSD, C.FSDSP (RV64 has no C.FLW/C.FSW);
  5. **any** CSR instruction naming `fflags` (0x001), `frm` (0x002), `fcsr` (0x003), including pure reads (sail: `is_CSR_accessible(0x001..0x003) = currentlyEnabled(Ext_F)`, which requires `FS ≠ 0`; `extensions/FD/fdext_control.sail:18,30-32`).
  The current spec has no FS check; all FP instruction definitions (≈L3 3170-4060) need it.
- **Transition to Dirty** (P Table 14 p.40). After passing the Off check, set `FS := 11` when an instruction:
  1. writes an f register (even with an unchanged value): FP loads, FMV.W.X/FMV.D.X, FCVT to FP, arithmetic (sail `wF` calls `dirty_fd_context()`; current `writeFPRS`/`writeFPRD`, L3 1642-1653, already do this);
  2. *writes* 0x001/0x002/0x003 by a CSR instruction (per Zicsr, CSRRS/CSRRC with `rs1 = x0` and CSRRSI/CSRRCI with `uimm = 0` do not write; §3.2);
  3. accrues IEEE flags into `fflags`, per [D17].
  p.39 makes it implementation-defined whether an unchanged write marks Dirty from Initial/Clean; rules 1–2 choose "always Dirty", as sail and the current L3 do.
- Instructions that only read FP state leave FS unchanged. Trap entry, MRET and SRET never change FS. Changing FS never changes f registers or `fcsr` (p.39). M and S share one FS (p.41).
- **XS** RO0; **VS** RO0 ([D18]); **SD** = `FS = 11` (p.40).

#### 2.3.10 Endianness, H, Zicfilp and double-trap fields

`MBE`, `SBE`, `UBE` RO0 (little-endian only, p.36; matches sail). `MPV`, `GVA`, `MPELP`, `SPELP`, `MDT`, `SDT` RO0. None needs state.

### 2.4 `sstatus` (0x100, SRW): view of `mstatus` (P §12.1.1 p.113–116)

`sstatus` is not stored ("reading or writing any field in sstatus is equivalent to reading or writing the homonymous field in mstatus", p.114). SXLEN = 64 fields visible (P Figure 50 p.113): SIE 1, SPIE 5, UBE 6, SPP 8, VS 10:9, FS 14:13, XS 16:15, SUM 18, MXR 19, SPELP 23, SDT 24, UXL 33:32, SD 63.

```
SSTATUS_RMASK = 0x8000_0003_018D_E762   -- full 1.13 sstatus view
SSTATUS_WMASK = 0x0000_0000_0008_6122   -- writable here: SIE SPIE SPP FS MXR  (= RMASK && MSTATUS_WMASK)
```

- **Read**: `read_mstatus() && SSTATUS_RMASK` (here: SD, UXL = 2, MXR, FS, SPP, SPIE, SIE).
- **Write** of `v` (sail `legalize_mstatus(m, lift_sstatus(m, s))`):
  1. `m' := (stored && ~SSTATUS_RMASK) || (v && SSTATUS_RMASK)`;
  2. `mstatus := legalize_mstatus(m', misa)`.
  Closed form: `mstatus := (stored && ~0x86122) || (v && 0x86122)`. (The CSR analysis gave mask `0xC6122` including SUM; SUM is RO0 here, so `0x86122` is correct and the stored result is identical, R8.) *WP7 amendment ([S19]):* with SUM writable the closed form is `(stored && ~0xC6122) || (v && 0xC6122)`; the L3 code, which masks with `SSTATUS_RMASK` and then legalises, is unchanged.
- **Access**: `csr<9:8> = 01`: accessible from S and M; illegal from U.

**Replaces** `register sstatus` (L3 460-468), `lift_mstatus_sstatus`/`lower_sstatus_mstatus` (L3 574-603), and the 0x100 arms of `CSRMap` (L3 944, 1053).

---

## 3. CSR map and access

Parameters: XLEN fixed 64; `misa` = I M A F D C S U, only C writable; 16 PMP entries, G = 0; PABITS = 56; ASIDLEN = 16 (sail RV64 defaults).

### 3.1 Address conventions (P §2.1 p.13–15)

- `csr[11:10]`: `00`/`01`/`10` read/write; `11` read-only.
- `csr[9:8]`: lowest privilege allowed: `00` U, `01` S, `10` H/VS, `11` M. Accessible iff `privLevel(cur) ≥ csr[9:8]` (unsigned; sail `check_CSR_priv`, `sys/sys_control.sail:41`). `10` CSRs never exist here.
- Ranges used (P Table 3 p.14–15): 0x000–0x0FF U RW; 0xC00–0xC7F U RO; 0x100–0x1FF S RW; 0x300–0x3FF M RW; 0xB00–0xBBF M RW; 0xF00–0xFBF M RO. 0x7B0–0x7BF are debug-mode only and "should" be illegal in M. No custom CSRs exist.

Rules:
- **R1** access to a non-existent CSR is reserved; this model raises illegal ([D24]).
- **R2** insufficient privilege: illegal (no virtual-instruction exception, no H).
- **R3** writing a read-only CSR (`csr[11:10] = 11`): illegal.
- **R4** read-only bits inside RW CSRs: writes ignored, no trap.
- **R5** standard CSRs have no read side effects (P ch.2 p.13; U §4.2.1 p.64).
- **R6** CSRs of a level are accessible at all higher levels (P §3.1 p.27).
- **R7** CSRRS/CSRRC with `rs1 = x0`, CSRRSI/CSRRCI with `uimm = 0` do not write and do not trap on read-only CSRs. The test is on the **field index**, not the register value: CSRRS with `rs1 ≠ x0` holding 0 *is* a write (U §4.2.1 p.62–63).
- **R8** CSRRW/CSRRWI always write, even with `x0`/0; with `rd = x0` they need not read (U p.62, Table 21 p.63).

### 3.2 Execution of the six Zicsr instructions

Inputs: `op ∈ {RW, RS, RC}`, register or immediate form, `csr`, `rd`, 5-bit field `f` (bits 19:15), and state including `cur = curPrivilege()` (not the MPRV-effective privilege). This is sail `doCSR`/`csr_access_type` (`extensions/Zicsr/zicsr_insts.sail:34-98`) and U Table 21 p.63; it replaces `checkCSROp` and the six `System > CSRR*` bodies (L3 4130-4206) with one shared body.

1. **Source**: register form `src ← GPR(f)`; immediate form `src ← ZeroExtend64(f)`. Read before any write (`rd` may equal `rs1`).
2. **Access type**: `isWrite ← (op = RW) ∨ (f ≠ 0)`; `isRead ← (op ≠ RW) ∨ (rd ≠ 0)`.
3. **Checks**, each failing with `signalException(Illegal_Instr)` (cause 2, `mtval` = instruction bits, §4.2; no retire). All give the same exception and nothing changes before them, so their order is unobservable.
   - a. **Existence**: `is_CSR_defined(csr)` — whitelist of §3.6.1 (static, 12-bit address only).
   - b. **Privilege**: `privLevel(cur) ≥ csr[9:8]`.
   - c. **Read-only**: `¬(isWrite ∧ csr[11:10] = 11)`.
   - d. **Dynamic conditions** (one helper inside `checkCSROp`, [D9]):
     - 0x001–0x003: `misa.F = 1 ∧ mstatus.FS ≠ 00` (§2.3.9).
     - 0xC00–0xC02: `counterReadAllowed(csr, cur)` (§6.4).
     - 0x180 (`satp`): `cur = M`, or `cur = S ∧ mstatus.TVM = 0` (P §3.1.6.6 p.37; sail `is_satp_accessible`, `sys/vmem.sail:285`).
     - all other present CSRs: none.
4. **Read**: `old ← readCSR(csr)` (§3.7); counters return the pre-instruction value (U p.64). `oldRMW ← readCSR_rmw(csr)`, equal to `old` except for `mip`/`sip`, where `old` (returned in `rd`) includes the external SEIP line and `oldRMW` does not (P §3.1.9 p.45; sail `zicsr_insts.sail:67-71`; §4.1.3). Because of R5 the read may be unconditional; `isRead` only gates the `rd` write ([D36]).
5. **Write**, iff `isWrite`: `new ← src` (RW), `oldRMW || src` (RS), `oldRMW && ~src` (RC); then `writeCSR(csr, new)`, which applies the legaliser (§3.7), never traps, and performs the write side effects. The only side effects in this model: `FS := Dirty` on writes to 0x001–0x003; suppression of this instruction's `minstret` increment on a write to `minstret` (U p.64; §6.5); the `misa` IALIGN suppression (§2.2.3).
6. `rd ← old` (no-op if `rd = 0`).
7. `PC ← PC + 4`. A write that makes an interrupt pending and enabled is taken at the next step boundary (§4.5).
8. Log the value read back after legalisation (as current `writeCSR` does via `Delta.data2 <- Some(CSR(csr))`).

Bugs this fixes in L3 4130-4200: (i) `CSRRWI` with `uimm = 0` neither writes nor checks write access; (ii) `#UNDEFINED`/`#INTERNAL_ERROR` on unknown CSRs; (iii) missing FS check for 0x001–0x003; (iv) `csrName(0x144)` = "mip".

### 3.3 Field specifications (P §2.3 p.24–25)

- **WPRI** (p.24): unimplemented ⇒ RO0. Every WPRI bit of every present CSR reads 0 and ignores writes.
- **WLRL** (p.25): a write of an unsupported value may raise illegal; a later read returns a deterministic function of written and previous values. This model never traps and keeps the previous value ([D33]). Only `mcause.ExceptionCode`/`scause.ExceptionCode` are WLRL here.
- **WARL** (p.25): any write, no exception; the read returns a legal value that is a deterministic function of the written value and state. Every WARL CSR has a pure legaliser; the stored value is always legal, so a read is a projection (plus the derived bits of `mstatus`, `mip`).

### 3.4 Modulation, implicit reads, width (P §2.4–2.7 p.25–26)

- **Field modulation** (P §2.4 p.25): no stored field changes its legal set as a result of another CSR write here (`misa` writable only in C; C changes only the read view of `xepc`, specified explicitly by P §3.1.14 p.48; `sstatus`/`sie`/`sip` are views; STCE, PBMTE, ADUE, SSE are RO0). Nothing to implement. WP7 must revisit if `misa.S/U` or `satp` modes become writable. *WP7 amendment:* `satp` accepts Sv39, Sv48 and Sv57 from WP7 stage 2, which makes SUM writable for good, since it depends on which modes the hart supports, not on the value of `satp`; so there is still no field modulation.
- **Implicit reads** (P §2.5 p.26) return what an explicit read would: trap entry reads the legalised `xtvec`; MRET/SRET read `xepc` through `read_xepc`; PMP matching reads `pmpaddr` through the G-aware view (= stored value at G = 0).
- **Width modulation** (P §2.6 p.26): moot (UXL, SXL, MXL read-only 2). Delete the `in32BitMode()` branches in CSR code.
- **CSRs wider than XLEN** (P §2.7 p.26): none on RV64. All RV32 high halves are reserved on RV64 and illegal: 0xC80–0xC9F, 0x310, 0x312, 0x31A, 0x757, 0xB80–0xB9F, 0x721–0x73F, 0x15D, and odd `pmpcfg1..15` (P §3.7.1 p.70). 32-bit CSRs (`fcsr`, `mcounteren`, `scounteren`, `mcountinhibit`, `mvendorid`) read zero-extended; writes ignore bits 63:32.

### 3.5 Zicsr notes (U §4.2 p.61–65)

- Immediate forms zero-extend `uimm`. CSRRS/CSRRC set/clear only writable bits (p.62); bits that read differently from storage are written back with the read value (only the SEIP case here, handled by `oldRMW`).
- Traps caused by the new CSR value are indirect effects, not side effects (p.63–64).
- A hart sees its own CSR accesses in program order and a side effect is visible to the next instruction (U §4.2.1.1 p.64): automatic in sequential L3.
- Pseudo-instructions: `csrr` = `csrrs rd,csr,x0`; `csrw` = `csrrw x0,csr,rs1`; `csrwi` = `csrrwi x0,csr,uimm`; `rdcycle/rdtime/rdinstret` = `csrrs rd,{cycle,time,instret},x0`.
- S3K's `_start` and trap code use `csrwi scounteren,15`, `csrwi mcounteren,15`, `csrwi mcountinhibit,0`, `csrw pmpcfg0`, `csrw pmpaddr0..7`, `csrrw tp,mscratch,tp`, `csrr a5,mip`, `csrr *,mhartid`, `csrr a1,mtval` (`examples/riscv/s3k/s3k_full.da.txt`). All must be legal in M-mode, which requires the S CSRs to exist.

### 3.6 CSR table

#### 3.6.1 Present CSRs

"Reset" is the model's value ([D70], [D71]); only values cited to P §3.4 p.63 are mandated. "Legaliser" points to the section that defines it.

**Unprivileged**

| Addr | Name | Priv | Acc | Reset | Read | Legaliser / write | Dyn. cond. | Cite |
|---|---|---|---|---|---|---|---|---|
| 0x001 | fflags | U | RW | 0 | `zext(fcsr[4:0])` | §3.7 L-FCSR | FS ≠ Off | U §6.1.2 p.130 |
| 0x002 | frm | U | RW | 0 | `zext(fcsr[7:5])` | L-FCSR | FS ≠ Off | U p.130–131 |
| 0x003 | fcsr | U | RW | 0 | `zext(fcsr[7:0])` | L-FCSR | FS ≠ Off | U p.130 |
| 0xC00 | cycle | U | RO | = mcycle | `mcycle` | — | §6.4 (CY) | U §4.3 p.64–66 |
| 0xC01 | time | U | RO | = mtime | `mtime()` (§6.6) | — | §6.4 (TM) | P §3.1.11 p.47, §3.2.1 p.59 |
| 0xC02 | instret | U | RO | = minstret | `minstret` | — | §6.4 (IR) | U §4.3 |

**Supervisor** (present because `misa.S = 1`)

| Addr | Name | Priv | Acc | Reset | Read | Legaliser | Cite |
|---|---|---|---|---|---|---|---|
| 0x100 | sstatus | S | RW | view | §2.4 | §2.4 | P §12.1.1 p.113–114 |
| 0x104 | sie | S | RW | view | `mie && mideleg` | §4.1.3 | P §12.1.3 p.117–118 |
| 0x105 | stvec | S | RW | 0 (Direct) | stored | §4.1.1 L-TVEC | P §12.1.2 p.116 |
| 0x106 | scounteren | S | RW | 0 | `zext32` | §6.3 | P §12.1.5 p.119 |
| 0x10A | senvcfg | S | RW | 0 | stored | §6.8 (FIOM only) | P §12.1.10 p.122–124 |
| 0x140 | sscratch | S | RW | 0 | stored | none (64 bits) | P §12.1.6 p.119 |
| 0x141 | sepc | S | RW | 0 | `read_xepc` | §4.1.5 | P §12.1.7 p.119–120 |
| 0x142 | scause | S | RW | 0 | stored | §4.1.6 L-SCAUSE | P §12.1.8 p.120 |
| 0x143 | stval | S | RW | 0 | stored | none (64 bits) | P §12.1.9 p.121–122 |
| 0x144 | sip | S | RW | view | `mip && mideleg` (+ ext. SEIP in `rd`) | §4.1.3 | P §12.1.3 p.117–118 |
| 0x180 | satp | S | RW | 0 | stored | §3.7 L-SATP; S-mode needs TVM = 0 | P §12.1.11 p.124–126 |

**Machine**

| Addr | Name | Acc | Reset | Read | Legaliser | Cite |
|---|---|---|---|---|---|---|
| 0xF11 | mvendorid | RO | — | 0 | — | P §3.1.2 p.29 |
| 0xF12 | marchid | RO | — | 0 | — | §3.1.3 p.30 |
| 0xF13 | mimpid | RO | — | 0 | — | §3.1.4 p.31 |
| 0xF14 | mhartid | RO | hart id | stored | — | §3.1.5 p.31 |
| 0xF15 | mconfigptr | RO | — | 0 | — | §3.1.17 p.53 (must be implemented) |
| 0x300 | mstatus | RW | §2.3.1 | §2.3.4 | §2.3.3 | §3.1.6 p.31ff |
| 0x301 | misa | RW | `0x8000_0000_0014_112D` (M) | stored | §2.2.3 | §3.1.1 p.27–29 |
| 0x302 | medeleg | RW | 0 | stored | §4.1.2 | §3.1.8 p.42–43 (must exist with S) |
| 0x303 | mideleg | RW | 0 | stored | §4.1.2 | §3.1.8 |
| 0x304 | mie | RW | 0 | stored | §4.1.3 | §3.1.9 p.43–46 |
| 0x305 | mtvec | RW | 0 (Direct) | stored | §4.1.1 | §3.1.7 p.41–42 |
| 0x306 | mcounteren | RW | 0 | `zext32` | §6.3 | §3.1.11 p.46–47 (must exist with U) |
| 0x30A | menvcfg | RW | 0 | stored | §6.8 | §3.1.18 p.54–56 (exists iff U) |
| 0x320 | mcountinhibit | RW | 0 | `zext32` | §6.3 | §3.1.12 p.47–48 |
| 0x323–0x33F | mhpmevent3–31 | RW | — | 0 | writes ignored | §3.1.10 p.46 ([D26]) |
| 0x340 | mscratch | RW | 0 | stored | none | §3.1.13 p.48 |
| 0x341 | mepc | RW | 0 | `read_xepc` | §4.1.5 | §3.1.14 p.48–49 |
| 0x342 | mcause | RW | **0 (M)** | stored | §4.1.6 L-MCAUSE | §3.1.15 p.49–50 |
| 0x343 | mtval | RW | 0 | stored | none | §3.1.16 p.52 |
| 0x344 | mip | RW | 0 + platform | §4.1.3 | §4.1.3 | §3.1.9 p.43–46 |
| 0x3A0 | pmpcfg0 | RW | 0 (A = L = 0 mandated) | packed bytes 0–7 | §5.2 | §3.7.1 p.70–72 |
| 0x3A2 | pmpcfg2 | RW | 0 | packed bytes 8–15 | §5.2 | §3.7.1 |
| 0x3B0–0x3BF | pmpaddr0–15 | RW | 0 | stored (G = 0) | §5.2.3 | §3.7.1 p.71 |
| 0xB00 | mcycle | RW | 0 | stored | none | §3.1.10 p.46 |
| 0xB02 | minstret | RW | 0 | stored | none; sets `minstret_written` | §3.1.10 p.46; U p.64 |
| 0xB03–0xB1F | mhpmcounter3–31 | RW | — | 0 | writes ignored | §3.1.10 p.46 ([D26]) |

Count: 6 U + 11 S + 97 M = **114 present addresses** (R10).

#### 3.6.2 Allocated in 1.13 but absent (illegal in every mode)

| Addr | Name | Why |
|---|---|---|
| 0x008–0x00A, 0x00F, 0xC20–0xC22 | vstart, vxsat, vxrm, vcsr, vl, vtype, vlenb | no V |
| 0x011, 0x015, 0x017 | ssp, seed, jvt | no Zicfiss, Zkr, Zcmt |
| 0xC03–0xC1F | hpmcounter3–31 | no Zihpm ([D25]) |
| 0xC80–0xC9F, 0x310, 0x312, 0x31A, 0x757, 0xB80–0xB9F, 0x15D | RV32 high halves | reserved on RV64 (P §2.7 p.26) |
| 0x10C–0x10F, 0x30C–0x30F, 0x31C–0x31F | sstateen*, mstateen* | no Smstateen/Ssstateen |
| 0x120 | scountinhibit | no Smcdeleg ([D34]) |
| 0x14D | stimecmp | no Sstc ([D34]) |
| 0x14E, 0x14F, 0x15F, 0x34E | sctrctl, sctrstatus, sctrdepth, mctrctl | no Smctr/Ssctr |
| 0x150–0x157, 0x350–0x357 | siselect/sireg*, miselect/mireg* | no Sscsrind/Smcsrind |
| 0x181 | srmcfg | no Ssqosid |
| 0x5A8, 0x7A0–0x7A3, 0x7A8 | scontext, tselect, tdata1–3, mcontext | no Sdtrig ([D35]) |
| 0x7B0–0x7B3 | dcsr, dpc, dscratch0/1 | debug mode only (P §2.1 p.13) |
| 0xDA0 | scountovf | no Sscofpmf |
| 0x200–0x2FF, 0x600–0x6FF, 0xA00–0xAFF, 0xE00–0xEFF | all H/VS CSRs | no H |
| 0x321, 0x322, 0x721–0x73F | mcyclecfg, minstretcfg, …h | no Smcntrpmf |
| 0x34A, 0x34B | mtinst, mtval2 | H only |
| odd 0x3A1–0x3AF | pmpcfg1, 3, …, 15 | **mandated illegal on RV64** (P §3.7.1 p.70) |
| even 0x3A4–0x3AE, 0x3C0–0x3EF | pmpcfg4–14, pmpaddr16–63 | 16 entries ([D47], [D61]) |
| 0x740–0x742, 0x744 | mnscratch, mnepc, mncause, mnstatus | no Smrnmi |
| 0x747 | mseccfg | reserved: no extension adds a field (P §3.1.19 p.56; [D30]) |

Every other address is also illegal. Implement `is_CSR_defined` as an explicit whitelist of §3.6.1 with the dense ranges 0x323–0x33F, 0x3B0–0x3BF, 0xB03–0xB1F.

### 3.7 Legalisers owned by this chapter; index of the others

| CSR(s) | Legaliser | Defined in |
|---|---|---|
| misa | L-MISA | §2.2.3 |
| mstatus, sstatus | `legalize_mstatus`, sstatus view | §2.3.3, §2.4 |
| mtvec, stvec | L-TVEC | §4.1.1 |
| medeleg, mideleg | masks 0xB3FF, 0x222 | §4.1.2 |
| mie, mip, sie, sip | masks and views | §4.1.3 |
| mepc, sepc | `write_xepc` / `read_xepc` | §4.1.5 |
| mcause, scause | L-MCAUSE, L-SCAUSE | §4.1.6 |
| mtval, stval, mscratch, sscratch | store all 64 bits | §4.1.4, §4.1.7 |
| pmpcfg0/2, pmpaddr0–15 | `legalize_pmpcfg_byte`, `legalize_pmpaddr` | §5.2 |
| mcounteren, scounteren, mcountinhibit, menvcfg, senvcfg, mcycle, minstret, mhpm* | masks | §6.3, §6.8 |

**L-FCSR** (U §6.1.2 p.130; sail `write_fcsr`, `extensions/FD/fdext_regs.sail:440`): `fflags`: `fcsr[4:0] ← v[4:0]`; `frm`: `fcsr[7:5] ← v[2:0]`; `fcsr`: `fcsr[7:0] ← v[7:0]`; `fcsr[31:8]` stays 0. Reserved rounding modes 101–111 are **stored as written** ([D37]); using them with a DYN-rm instruction is illegal (FP area; sail `Fcsr_RM_Illegal`). Every write sets `FS := 11`.

**L-SATP** (P §12.1.11 p.124–126; sail `legalize_satp`, `core/sys_regs.sail:1192`). RV64 fields: MODE 63:60, ASID 59:44, PPN 43:0.
1. If `v[63:60] ≠ 0`: return `old` ("the entire write has no effect", p.126).
2. Else return `v`, with ASID limited to ASIDLEN = 16 and PPN to PABITS − 12 = 44 bits, i.e. `v` unchanged ([D32]).
Translation is never performed; `translateAddr` is the identity ([D5]).

*WP7 amendment ([S10], [S7], `design-smode.md` §3.2.3).* From WP7 stage 2 step 1 returns `old` only if `v[63:60] ∉ {0, 8, 9, 10}` (Bare, Sv39, Sv48, Sv57), tested as a mask comparison on `v && 0xF000…0`, and `translateAddr` translates whenever the privilege is S or U and MODE is not Bare (`design-smode.md` §3.5). The "entire write has no effect" quote is on p.125.

### 3.8 1.7-era CSRs removed from `is_CSR_defined`, `CSRMap`, `csrName` (L3 895–1240) and the records (L3 344–520)

Several 1.7 addresses are reused with a different meaning in 1.13 (marked ⚠): a stale entry would be silently wrong.

| 1.7 addr | 1.7 name | 1.13 meaning | Action |
|---|---|---|---|
| 0xF00 | mcpuid | unallocated | remove; ISA info in `misa` |
| 0xF01, 0xF10 | mimpid, mhartid | unallocated | move to 0xF13, 0xF14 |
| ⚠0x301 | mtvec | **misa** | mtvec moves to 0x305 |
| ⚠0x302 | mtdeleg | **medeleg** | replace by medeleg 0x302 + mideleg 0x303 |
| ⚠0x321 | mtimecmp | mcyclecfg (absent) | remove; mtimecmp is memory-mapped (§6.6) |
| 0x701, 0x741 | mtime, mtimeh | unallocated / Smrnmi space | remove; `time` reads `mtime()` |
| 0x343 | mbadaddr | mtval | rename |
| 0x380–0x385 | mbase … mdbound | unallocated | remove (PMP replaces them) |
| 0x780, 0x781, 0x783 | mtohost, mfromhost, send_ipi | unallocated | remove (HTIF is harness, [D13]) |
| ⚠0xB01, 0xB81 | htime shadows | reserved hole | remove |
| 0x101 | stvec | unallocated | stvec moves to 0x105 |
| 0x121 | stimecmp | unallocated | remove |
| 0xD01, 0xD81, 0xD42, 0xD43 | stime, stimeh, scause, sbadaddr (SRO) | unallocated | scause → 0x142, stval → 0x143 (SRW) |
| 0x180 | sptbr | satp | replace (L-SATP) |
| ⚠0x181 | sasid | srmcfg (absent) | remove; ASID in `satp[59:44]` |
| 0x900–0x902, 0x980–0x982 | S counter shadows | unallocated | remove; delete `*_delta` |
| ⚠0x200–0x202, 0x221, ⚠0x240–0x243 | hstatus, htvec, htdeleg, htimecmp, hscratch, hepc, hcause, hbadaddr | VS CSRs (absent) / unallocated | remove with `HypervisorCSR` |
| 0xE01, 0xE81, 0xA01, 0xA81 | htime, stime H-shadows | unallocated | remove |
| 0xC80–0xC82 | cycleh/timeh/instreth | RV32 only | illegal (drop `in32BitMode` branch) |
| 0x144 | "mip" (name bug) | sip | keep address, fix name |

`mip.HTIP`/`HSIP` and `mie.HTIE`/`HSIE` positions (6, 2) become VS positions: RO0. `mcause.EC` widens from 3:0 to 62:0.

### 3.9 Where this lands in L3

- L3 883–922: `csrRW`, `csrPR`, `check_CSR_access`, `is_CSR_defined` — keep names; whitelist §3.6.1; `privLevel` returns 0/1/3.
- L3 926–1132: `CSRMap` value/assign — per-CSR clauses applying §3.7; `case _` unreachable.
- L3 1134–1240: `csrName` — 1.13 names; print the 12-bit hex for absent addresses (sail `csr_name_map` falls back to `hex_bits_12`).
- L3 1595–1610: `CSR`, `writeCSR` — keep, including the read-back log.
- L3 4130–4206: one shared body implementing §3.2.
- L3 344–520: records per §1.4.2–1.4.3.

---

## 4. Traps and interrupts

Conventions: `y` = privilege when the trap occurs; `d` = privilege the trap is taken into; `pc` = address of the current instruction; VA = PA; ILEN = 32; IALIGN = 16 iff `misa.C`.

### 4.1 Trap CSRs

#### 4.1.1 `mtvec` (0x305) and `stvec` (0x105) (P §3.1.7 p.41–42, Table 15; §12.1.2 p.116–117, Table 36)

Layout: `BASE[63:2]` WARL, `MODE[1:0]` WARL (0 Direct, 1 Vectored, 2–3 reserved). Handler base = `BASE @ 00`.

```
legalize_xtvec(v, old) =                      -- L-TVEC, [D39]
  if v[1:0] ∈ {0, 1} then v                   -- BASE as written, 4-byte alignment in both modes
  else v[63:2] @ old[1:0]                     -- reserved MODE: keep old MODE, still write BASE

TrapVector(tvec, intr, code) =
  base = tvec[63:2] @ 00
  if tvec[1:0] = 1 ∧ intr then base + 4 * code else base
```
Examples: MTI (7) in Vectored mode goes to BASE + 0x1C; STI (5) via `stvec` to BASE + 0x14 (p.42, p.117). This replaces `PC <- MCSR.mtvec + privLevel(fromP)*0x40` and `PC <- SCSR.stvec` in `takeTrap`. sail: `legalize_tvec` with `xtvec_mode = Xtvec_Ignore`, `base_alignment = 2` (`core/sys_regs.sail:~655`). Reset 0 (Direct; sail `reset_tvecs`, `exceptions/sys_exceptions.sail:104-120`).

#### 4.1.2 `medeleg` (0x302), `mideleg` (0x303) (P §3.1.8 p.42–43)

Both must exist with S; one bit per exception code / `mip` bit. Spec constraints: no `medeleg` bit read-only one; `medeleg[11]` and `medeleg[16]` RO0 (p.43); bits for exceptions that cannot occur below M "should be" RO0; machine-level `mideleg` bits may not be read-only one (p.42).

```
legalize_medeleg(v) = v && 0xB3FF     -- codes 0-9, 12, 13, 15            [D40]
legalize_mideleg(v) = v && 0x222      -- SSI 1, STI 5, SEI 9              [D41]
```
sail effective defaults: `medeleg` `0xCB3FF` (mask `0x00fc_b7ff`, minus H codes; includes 18, 19), `mideleg` `0x222`. Codes 18, 19 cannot occur here, so cfg sets `base.medeleg.delegatable_bits = 0xB3FF`. Reset 0, so M/U software that never writes them never sees delegation. Replaces `mtdeleg` and `checkDelegation` (L3 375, 1482).

#### 4.1.3 `mie` (0x304), `mip` (0x344), and the `sie`/`sip` views (P §3.1.9 p.43–46; §12.1.3 p.117–118)

Bits 15:0 (`mie` uses the same positions, suffix IE); all other bits 0:

| bit | 13 | 11 | 9 | 7 | 5 | 3 | 1 |
|---|---|---|---|---|---|---|---|
| mip | LCOFIP (RO0, no Sscofpmf) | MEIP | SEIP | MTIP | STIP | MSIP | SSIP |

Bits 0, 2, 4, 6, 8, 10, 12, 14, 15 and 63:16 are RO0.

| Bit | Source | CSR write | Cite |
|---|---|---|---|
| MEIP 11 | `c_extMEIP(procID)` (platform input, [D42]) | read-only | p.44 |
| MTIP 7 | `mtimecmp(procID) ≤u mtime()` (§6.6) | read-only | p.44, §3.2.1 p.59 |
| MSIP 3 | bit 0 of the CLINT `msip(procID)` word (§6.6) | read-only | p.44 |
| SEIP 9 | stored software bit `SEIP_sw` OR `c_extSEIP(procID)` | writes `SEIP_sw` only | p.45 |
| STIP 5 | stored software bit (no Sstc) | writable | p.45 |
| SSIP 1 | stored software bit | writable | p.45, p.118 |

Stored state: `mie` (64-bit register type), `mip` holding only `SSIP`, `STIP`, `SEIP_sw`.

```
legalize_mie(v)        = v && 0xAAA                              -- 1,3,5,7,9,11
mip_eff                = mip_sw || MSIP<<3 || MTIP<<7 || c_extSEIP<<9 || c_extMEIP<<11
write_mip(v)           : mip_sw := v && 0x222
CSR read of mip (rd)   = mip_eff
read-modify-write base = mip_eff with bit 9 := SEIP_sw            -- excludes the external SEIP line
read sie               = mie && mideleg
write sie              : mie := (mie && ~mideleg) || (v && mideleg)
read sip               = mip_eff && mideleg      (RMW base: external SEIP excluded, as for mip)
write sip              : if mideleg[1] then SSIP := v[1]          -- STIP, SEIP read-only in sip
```
SEIP rule (required, p.45): for `csrrs t0, mip, t1`, `t0[9] := SEIP_sw ∨ ext_SEIP`, then `SEIP_sw := SEIP_sw ∨ t1[9]`; `SEIP_sw` never depends on the external line (sail `doCSR` special-cases 0x344/0x144). With `c_extSEIP` false (harness default) the difference is unobservable. Reset: `mie = 0`, `mip_sw = 0`. Replaces `lift_mip_sip`, `lift_mie_sie`, `lower_sip_mip`, `lower_sie_mie` (L3 521–548) and `checkTimers`.

#### 4.1.4 `mscratch` (0x340), `sscratch` (0x140)

64-bit, no legalisation, never written by hardware (P §3.1.13 p.48; §12.1.6 p.119). Reset 0.

#### 4.1.5 `mepc` (0x341), `sepc` (0x141) (P §3.1.14 p.48–49; §12.1.7 p.119)

`xepc[0]` always 0; with IALIGN = 32, `xepc[1]` stays writable but is masked on every read, including MRET/SRET's implicit read ([D44]).
```
write_xepc(v) : xepc := v && ~1
read_xepc()   = if misa.C then xepc else xepc && ~3
```
Trap entry writes an IALIGN-aligned address, on which `write_xepc` is the identity. sail: `legalize_xepc` clears bit 0 (Zca supported), `align_pc` masks bits 1:0 when Zca is not enabled. Replaces `legalizeEPC` and `curEPC` (L3 769–780); the current write-time masking by the current C is wrong (it destroys bit 1 across a C-off/C-on round trip). Reset 0.

#### 4.1.6 `mcause` (0x342), `scause` (0x142) (P §3.1.15 p.49–50; §12.1.8 p.120)

Layout: bit 63 Interrupt, bits 62:0 Exception Code (WLRL). `scause` must hold codes 0–31 (p.120).
```
legalize_mcause(v, old) =                                         -- L-MCAUSE, [D33]
  c = v[62:0]
  if v[63] = 1 then (if c ∈ {1,3,5,7,9,11} then v else old)
               else (if c ∈ {0,1,2,3,4,5,6,7,8,9,11,12,13,15,19} then v else old)
legalize_scause(v, old) = if v[62:0] ≤u 31 then v else legalize_mcause(v, old)
```
This reproduces sail `legalize_cause` (`core/sys_regs.sail:~700`), which accepts 19 and the page-fault codes. Reset `mcause = 0` (P §3.4 p.63, "should be 0"), `scause = 0`.

#### 4.1.7 `mtval` (0x343), `stval` (0x143) (P §3.1.16 p.52–53; §12.1.9 p.121)

64-bit, store all bits (not RO0; cfg `xtval_nonzero.*` true). **Every trap into M writes `mtval`**, with the value from §4.2 or 0 ("For other traps, mtval is set to zero", p.53). The current L3 leaves `mbadaddr` unchanged when `badaddr = None`: wrong. `SynchronousTrap.badaddr :: vAddr option` becomes `tval :: regType`.

### 4.2 Cause codes and trap values (P Table 16 p.50; Table 37 p.120–121)

**Exceptions (Interrupt = 0)**. "Deleg." = writable in `medeleg` (§4.1.2). epc = `pc` in every row.

| Code | Constructor ([D7]) | Raised by | `xtval` ([D43]) | Deleg. |
|---|---|---|---|---|
| 0 | `Fetch_Misaligned` | taken branch, JAL, JALR (after clearing bit 0), C.J, C.JAL, C.JR, C.JALR, C.B* with target bit 1 set while `misa.C = 0` (U §2.1.2 p.28, §2.5 p.34/36); raised by the jump; not-taken branches raise nothing; the `Fetch` check (L3 4249) stays as a backstop | target address | yes |
| 1 | `Fetch_Fault` | PMP failure of a fetch parcel (§5.6.3) | address of the failing **parcel** (`pc` or `pc+2`) (p.52) | yes |
| 2 | `Illegal_Instr` | undecodable or reserved encodings; CSR not present, insufficient privilege, write to read-only (§3.2); FP with FS = Off; reserved dynamic rounding mode; MRET/SRET/WFI/SFENCE.VMA in a disallowed mode (§4.7); 16-bit parcel with `misa.C = 0` | instruction bits zero-extended: 16-bit parcel (`bits[1:0] ≠ 11`) → `zext(h[15:0])`, else `zext(w[31:0])` (p.52–53); parcel `0x0000` gives 0 | yes |
| 3 | `Breakpoint` | EBREAK, C.EBREAK | `pc` | yes |
| 4 | `Load_Misaligned` *(new)* | misaligned load, FP load, **LR** | effective address | yes |
| 5 | `Load_Fault` | PMP failure of load, FP load, LR | effective address (whole access, never split) | yes |
| 6 | `Store_AMO_Misaligned` (was `AMO_Misaligned`) | misaligned store, FP store, SC, AMO (AMOs report store codes, p.49) | effective address | yes |
| 7 | `Store_AMO_Fault` | PMP failure of store, FP store, SC, AMO | effective address | yes |
| 8 | `UMode_Env_Call` | ECALL in U | 0 | yes |
| 9 | `SMode_Env_Call` | ECALL in S | 0 | yes |
| 10 | — (delete `HMode_Env_Call`) | reserved | — | RO0 |
| 11 | `MMode_Env_Call` | ECALL in M | 0 | **RO0** (p.43) |
| 12, 13, 15 | `Fetch_PageFault`, `Load_PageFault`, `Store_AMO_PageFault` *(new)* | **never raised** (Bare); present for WP7. *WP7 amendment:* raised by translation from its stage 2 (`design-smode.md` §3.7) | faulting address | yes |
| 14, 17, 20–23, 32–47, ≥ 64 | — | reserved | — | RO0 |
| 16 | — | double trap (Smdbltrp absent) | — | **RO0** (p.43) |
| 18, 19 | — | software check, hardware error (never raised) | — | RO0 |
| 24–31, 48–63 | — | custom | — | RO0 |

(Constructor names other than the four new ones and the code-6 rename are the current ones, L3 271-283, [D7]. `exc_code = bits(4)` (L3 38) already covers 0-15; `mcause` stores it zero-extended into bits 62:0.) `excType` is removed; `mcause` is never decoded back to `ExceptionType`.

**Interrupts (Interrupt = 1)**: `xtval := 0` for every interrupt (sail `trap_handler_inner`). Codes: 1 SSI (delegable), 3 MSI, 5 STI (delegable), 7 MTI, 9 SEI (delegable), 11 MEI; 13 LCOFI absent; others reserved. `Interrupt` becomes six constructors replacing `{Software, Timer}` (L3 260–269).

### 4.3 Synchronous exception priority within one instruction (P Table 17 p.51)

Restricted to what this model raises (no Sdtrig, no translation, misaligned accesses always trap):
1. Instruction access fault (1): lower parcel first; upper parcel only if the lower one indicates a 32-bit instruction.
2. Illegal instruction (2).
3. Instruction address misaligned (0): raised by the control-transfer instruction after it decoded as legal.
4. ECALL (8/9/11), EBREAK (3): do not combine with other exceptions.
5. Load/store/AMO address misaligned (4/6): **above** access faults, and the PMP check is not evaluated for a misaligned access ([D55]; p.51: "Implementations that never support misaligned accesses can unconditionally raise the misaligned-address exception without performing address translation or protection checks").
6. Load/store/AMO access fault (5/7).

A step that takes an interrupt raises no synchronous exception (§4.5).

### 4.4 Trap destination

```
ExcDest(code, y) = if y ≠ M ∧ medeleg[code] = 1 then S else M        (P §3.1.8 p.42-43; sail exception_delegatee)
```
- Traps never go to a less-privileged mode: from M everything goes to M even if delegated (p.42). Horizontal S→S traps are taken.
- `medeleg[11]` = `medeleg[16]` = 0, so ECALL from M and double trap always go to M.
- sail additionally requires `currentlyEnabled(Ext_S)`; always true here (`misa.S` read-only 1). If `misa.S` were ever writable and cleared, `medeleg`/`mideleg` must behave as 0.
- With `medeleg = 0` (reset; S3K never writes it), every exception goes to M. S is entered only via delegation set by software or MRET with `MPP = S`; both are implemented as specified, and validated by WP7 (`design-smode.md` §2.7, `sim/tests/smode.S`).
- Non-recursive, so `checkDelegation.sml` (HOL termination helper) goes.

### 4.5 Interrupt selection and its place in `Next`

When: the conditions must be evaluated "immediately" after an xRET or an explicit write of `mip`, `mie`, `mstatus`, `mideleg` (p.43–44, p.117), and within bounded time of a pending-bit change; interrupts are taken *between* instructions with `mepc` = the next unexecuted instruction (P §3.1.14 p.49). **Recommendation [D38]: evaluate at the start of every step, before fetch** (sail `try_step`: `update_mip()` then `dispatchInterrupt(cur_privilege)`).

`SelectInterrupt()`, with `p = curPrivilege()`:
1. `pend := mip_eff && mie` (only bits 1, 3, 5, 7, 9, 11 can be set).
2. `pend_m := pend && ~mideleg`; `pend_s := pend && mideleg`.
3. `m_enabled := (p = M ∧ mstatus.MIE) ∨ p ∈ {U, S}` (§2.3.5).
4. `s_enabled := (p = S ∧ mstatus.SIE) ∨ p = U`.
5. If `m_enabled ∧ pend_m ≠ 0`: return `(Highest(pend_m), M)` (M-level interrupts first, p.44).
6. Else if `s_enabled ∧ pend_s ≠ 0`: return `(Highest(pend_s), S)`.
7. Else `None`.

`Highest` takes the first set bit in the order **MEI 11, MSI 3, MTI 7, SEI 9, SSI 1, STI 5** (p.45; S-level order SEI, SSI, STI on p.118; sail `findPendingInterrupt`).

**Step order in `Next`** (replaces the post-execution `checkInterrupts()` at L3 5306–5341, which also skips steps that branch or return):
1. `c_minstret_written ← false`; sample `incIR := ¬mcountinhibit.IR` (§6.5).
2. If `SelectInterrupt() = Some(i, d)`: `TrapEntry(d, intr = true, code(i), epc = PC, tval = 0)`; no fetch, no execution, no `minstret` increment; go to 5.
3. Else fetch and execute. On a synchronous exception: `TrapEntry(ExcDest(code, cur), false, code, epc = PC, tval)`; no `minstret` increment (a trapping instruction does not retire, P §3.3.1 p.61).
4. Else retire: PC update; `minstret` increment per §6.5.
5. Tick `mcycle` per §6.5. (The harness then advances `mtime`, §6.6.3.)

Consequences: in U, M-level interrupts and undelegated S-level interrupts that are pending and enabled trap to M regardless of MIE. `NextRISCV` (F1) must carry "no takeable interrupt": in M-mode H6 (`¬MIE`) suffices, because S-level interrupts are never enabled in M.

WFI wake-up rules (p.62) are irrelevant while WFI is a NOP; they would be "resume iff `mip_eff && mie ≠ 0`" (sail `shouldWakeForInterrupt`).

### 4.6 Trap entry `TrapEntry(d, intr, code, epc, tval)`, `y := curPrivilege()`

Replaces `takeTrap` (L3 1557–1593) and `pushPrivilegeStack` (L3 617).

**Into M** (P §3.1.6.1 p.32, §3.1.14–3.1.16 p.48–53, §3.1.7 p.41; sail `trap_handler_inner`):
1. `mcause := (intr ? 1 : 0) << 63 || ZeroExtend(code)`.
2. `mepc := epc`.
3. `mtval := tval` (§4.2; 0 if none).
4. `mstatus.MPIE := mstatus.MIE` (old MIE).
5. `mstatus.MIE := 0`.
6. `mstatus.MPP := privLevel(y)`.
7. `setPrivilege(Machine)`.
8. `PC := TrapVector(mtvec, intr, code)`.

**Into S** (validated by WP7, `design-smode.md` §2.9; `y ∈ {U, S}` by §4.4; P §3.1.8 p.42, §12.1.1 p.113–114):
1. `scause := (intr ? 1 : 0) << 63 || ZeroExtend(code)`.
2. `sepc := epc`.
3. `stval := tval`.
4. `mstatus.SPIE := mstatus.SIE`.
5. `mstatus.SIE := 0`.
6. `mstatus.SPP := (y = U ? 0 : 1)`.
7. `setPrivilege(Supervisor)`.
8. `PC := TrapVector(stvec, intr, code)`.

**Not changed by trap entry** (either destination): `mstatus.MPRV` (1.13 trap entry does not touch it — **remove** `MCSR.mstatus.MMPRV <- false`, L3 1563); FS; the other mode's cause/epc/tval and stack bits; the LR reservation ([D45] — **remove** `ReserveLoad <- None`). No double-trap check (Smdbltrp absent).

### 4.7 SYSTEM instructions

#### 4.7.1 Encodings

Opcode `1110011`, funct3 `000`, `rd = 0`, `rs1 = 0` unless noted. ECALL `0x00000073`; EBREAK `0x00100073`; SRET `0x10200073`; WFI `0x10500073`; MRET `0x30200073`; SFENCE.VMA `0001001 rs2 rs1 000 00000 1110011`; C.EBREAK `0x9002`. Encodings differing in `rs1`/`rd` from the fixed patterns are reserved and illegal (sail matches exactly). **Delete** the old decodes (L3 4473–4477): ERET `0x10000073`, MRTS `0x30500073`, SFENCE.VM `0x10100073 | rs1<<15`, and WFI at `0x10200073`, which is now **SRET**. MNRET, SINVAL.VMA, SFENCE.W.INVAL, SFENCE.INVAL.IR are not decoded (illegal).

#### 4.7.2 ECALL (P §3.3.1 p.60–61; U p.40)

Raise 8/9/11 for U/S/M; `tval = 0`; does not retire. Replaces `signalEnvCall`'s use of `privilege(MCSR.mstatus.MPRV)`.

#### 4.7.3 EBREAK, C.EBREAK (p.61)

Raise 3; `tval = pc` ([D43]); does not retire.

#### 4.7.4 MRET (P §3.3.2 p.61, §3.1.6.1 p.32–33, §3.1.6.4 p.35; sail `execute MRET`)

1. If `cur ≠ M`: illegal (`tval = 0x30200073`); nothing else.
2. `y := privilege(mstatus.MPP)` (decoded before MPP is overwritten; total, [D2]).
3. `mstatus.MIE := mstatus.MPIE`.
4. `mstatus.MPIE := 1`.
5. `mstatus.MPP := 00` (least-privileged supported mode, U).
6. If `y ≠ M`: `mstatus.MPRV := 0`.
7. `setPrivilege(y)`.
8. `PC := read_xepc(mepc)` (masked when `misa.C = 0`).
9. Retires. LR reservation kept ([D45]; "allowed to clear … but is not required to", p.61).

SIE, SPIE, SPP, `mcause` unchanged; no MDT/SDT/ELP handling.

#### 4.7.5 SRET (P §3.3.2 p.61, §3.1.6.6 p.37, §12.1.1 p.113–114; sail `execute SRET`)

1. Illegal (`tval = 0x10200073`) if `cur = U`, or `cur = S ∧ mstatus.TSR = 1`. **Legal in M whatever TSR is** (R11).
2. `y := (mstatus.SPP = 1 ? S : U)`.
3. `mstatus.SIE := mstatus.SPIE`.
4. `mstatus.SPIE := 1`.
5. `mstatus.SPP := 0`.
6. `mstatus.MPRV := 0` (`y ≠ M` always).
7. `setPrivilege(y)`.
8. `PC := read_xepc(sepc)`.
9. Retires.

Next-PC plumbing: keep `NextFetch`/`TransferControl`; `Ereturn` → `Mret`/`Sret` ([D8]); delete `Mrts` and `popPrivilegeStack` (L3 606).

#### 4.7.6 WFI (P §3.3.3 p.61–62, §3.1.6.6 p.37) ([D23], [S20])

| Mode | Result |
|---|---|
| M | NOP: retires, `PC := PC + 4`; a pending interrupt is taken at the next step with `mepc = pc + 4` |
| S | `TW = 1`: illegal iff no interrupt is pending and enabled in `mie` (`read_mip() && mie = 0`), else NOP; `TW = 0`: NOP |
| U | **always illegal** (S is implemented; the bounded time limit is chosen as 0) |

Illegal `tval = 0x10500073`. sail cfg: `platform.wfi_is_nop = false`, `platform.max_time_to_wait = 0`, `wfi_available_to_user_mode = false`.

*WP7 amendment ([S20], `design-smode.md` §2.11).* The S row was "illegal if `TW = 1`, else NOP", which p.37 also allows, but it differs from sail when an interrupt is pending and enabled in `mie` while the global enable (SIE) or `mideleg` keeps it from being taken. With a zero time limit, a WFI completes at once exactly when such a locally enabled interrupt is pending: "the hart must resume if a locally enabled interrupt becomes pending, even if it has been delegated" (p.62), whatever MIE, SIE and `mideleg` are. sail does the same with the cfg above: its first `try_step` enters the wait state, and the second retires the WFI or, in S with `TW = 1` and no locally enabled interrupt pending, raises the illegal instruction (`shouldWakeForInterrupt`). Both belong to one step of its trace, which advances `mtime` and `mcycle` once, as the model's one-step NOP does (checked on sail), and `compare.py` ignores the wait messages. With the earlier `wfi_is_nop = true`, sail retired S-mode WFI whatever TW was. M and U are unchanged.

#### 4.7.7 SFENCE.VMA (P §12.2.1 p.127–130, §3.1.6.6 p.37, §12.9 p.143) ([D46])

| Mode | Result |
|---|---|
| U | illegal (supervisor instruction; p.143) |
| S, TVM = 1 | illegal |
| S, TVM = 0 | no-op, retires |
| M | no-op, retires |

`rs1`/`rs2` are read and ignored; an invalid VA raises nothing (p.128); no translation caches. Replaces `SFENCE_VM` (L3 4209) and the TLB code. p.130 also permits illegal-everywhere when `satp.MODE` is read-only zero; sail's default `extensions.Svbare.sfence_vma_illegal_if_svbare_only = true` does that, so cfg sets it to `false`.

*WP7 amendment ([S4], `design-smode.md` §2.13).* WP7 keeps this legality; the S-mode rows are validated by `sim/tests/smode.S`. With Sv39, Sv48 and Sv57 (WP7 stage 2) the fence still has nothing to do, now because the hart has no address-translation cache: every access walks the page table as it then is in memory, and so uses a translation that the fence allows (P §12.2.1 p.128). The p.130 option of making SFENCE.VMA illegal no longer applies, since `satp.MODE` is not read-only zero, and the cfg knob is moot.

### 4.8 Absent features

No NMI/Smrnmi (P §3.5 p.63; §6.9); no Smdbltrp/Ssdbltrp (MDT, SDT RO0; `medeleg[16] = 0`); no Sstc (STIP software-writable, `menvcfg.STCE = 0`); no Sscofpmf (LCOFIP/LCOFIE RO0, code 13 rejected); no Zicfilp (no ELP save/restore); no H (`hedeleg`, `hideleg`, `mtval2`, `mtinst`, MPV, GVA absent).

### 4.9 Map of L3 code replaced

| Lines | Current | Change |
|---|---|---|
| 260–319 | `Interrupt`, `ExceptionType`, `excCode`, `excType`, `excName` | §4.2 |
| 375–410 | `mtdeleg`, `mip`, `mie`, `mcause` registers | §4.1.2, §4.1.3, §4.1.6 |
| 411–495 | `MachineCSR`, `SupervisorCSR`, `HypervisorCSR` | §1.4.2–1.4.3 |
| 521–548 | mip/mie lift/lower | §4.1.3 |
| 606–642 | push/pop privilege stack, `SynchronousTrap`, `TransferControl` | §4.6, §4.7 |
| 769–780 | `legalizeEPC`, `curEPC` | §4.1.5 |
| 1451–1478 | `setTrap`, `signalException`, `signalAddressException`, `signalEnvCall` | carry `tval`; `Next` must make the fetched `h`/`w` available for illegal-instruction `tval` |
| 1482–1555 | `checkDelegation`, `checkPrivInterrupt`, `checkInterrupts` | `ExcDest` §4.4, `SelectInterrupt` §4.5 |
| 1557–1593 | `takeTrap` | §4.6 |
| 4096–4126, 4209–4215, 4471–4477 | ECALL, EBREAK, ERET, MRTS, WFI, SFENCE_VM and decodes | §4.7 |
| 5275–5341 | `checkTimers`, post-execution interrupt match | §4.5, §6.6 |

---

## 5. PMP and memory access exceptions

Area: P §3.7 in full, plus the PMAs (P §3.6) a flat-memory model must fix. Notation: `ones(k) = 2^k − 1`; arithmetic unsigned 64-bit.

### 5.1 Fixed choices

| Item | Value | sail default |
|---|---|---|
| `PMP_COUNT` | 16, all usable, one spec constant ∈ {0, 16, 64} ([D47]) | `memory.pmp.count = 16`, `usable_count = 16` |
| Grain G | 0: 4-byte grain, NA4 available ([D48], R2) | `memory.pmp.grain = 0` |
| A modes | OFF, TOR, NA4, NAPOT ([D50]) | all supported |
| R = 0, W = 1 write | stored as R = W = X = 0 ([D49], R13) | `pmpcfg_write_only = PMP_ClearPermissions` |
| PABITS | 56: `pmpaddr[53:0]` writable ([D51]) | `physaddr_bits = 56` (RV64) |
| Main memory | all of `[0, 2^64)`, every access type ([D54]) | ROM/MMIO/RAM regions, faults elsewhere |
| Misaligned load/store/AMO/LR/SC | always 4/6, before PMP ([D55]–[D57]) | allowed/split; LR/SC access fault |
| MAG PMA | none ([D58]) | RAM MAG 2^4 |
| Smepmp, `mseccfg` | absent; 0x747 illegal ([D30]) | `mseccfg` exists if Zkr on |

### 5.2 Data layout and write legalisation

#### 5.2.1 Entry configuration byte `pmp<i>cfg` (P §3.7.1 Figure 34 p.72; Table 23 p.72)

| Bits | Field | Meaning |
|---|---|---|
| 7 | L | lock; also enforces R/W/X on M-mode |
| 6:5 | — | RO0 |
| 4:3 | A | 0 OFF (matches nothing), 1 TOR (`pmpaddr[i−1] ≤ y < pmpaddr[i]`), 2 NA4 (naturally aligned 4 bytes), 3 NAPOT (naturally aligned power of two, ≥ 8 bytes) |
| 2 | X | execute |
| 1 | W | write |
| 0 | R | read |

R/W/X is a collective WARL field with R = 0, W = 1 reserved (p.71; still reserved without Smepmp MML, P §3.1.19 item 4 p.58). **Invariant**: no stored entry has R = 0 ∧ W = 1, so W = 1 ⇒ R = 1.

#### 5.2.2 CSRs (P §3.7.1 Figure 31 p.71, p.70)

- RV64: only even `pmpcfg<n>` exist; `pmpcfg<n>` (CSR `0x3A0 + n`) holds entries `4n … 4n+7`, entry `4n+k` in bits `[8k+7:8k]`. With 16 entries: `pmpcfg0` (0x3A0) = entries 0–7, `pmpcfg2` (0x3A2) = entries 8–15; `pmpaddr0–15` = 0x3B0–0x3BF.
- Odd `pmpcfg1..15` "are illegal" (p.70, mandated). CSRs for entries ≥ 16 (`pmpcfg4..14`, `pmpaddr16..63`) are illegal ([D61]; sail `is_CSR_accessible` requires `count > index`, `pmp/pmp_regs.sail:258-270`).
- All are M-level RW (`csr[9:8] = 11`): illegal from S and U (p.70).
- Storage ([D52], R4): `MachineCSR.pmpcfg0`, `pmpcfg2`, `pmpaddr0..15 :: regType`, holding exactly the CSR images (bits 6:5 of every byte and `pmpaddr[63:54]` always 0 by legalisation). Read of `pmpcfg<n>` = stored image (sail `pmpReadCfgReg`).
- `pmpaddr<i>` (Figure 33 p.71): bits 63:54 RO0; bits 53:0 = physical address bits 55:2.

**Read view with grain G** (P §3.7.1.1 p.73; sail `pmpReadAddrReg`, `pmp_regs.sail:70`), for generality:
1. `G ≥ 2 ∧ cfg[i].A[1] = 1`: `view(i) = stored[i] || ones(G−1)`.
2. `G ≥ 1 ∧ cfg[i].A[1] = 0`: `view(i) = stored[i] && ~ones(G)`.
3. otherwise `view(i) = stored[i]`.
**With G = 0, `view(i) = stored[i]`.** Stored bits must survive A changes (p.73). Grain discovery (write 0 to `pmp0cfg`, all ones to `pmpaddr0`, read back) returns `0x003F_FFFF_FFFF_FFFF`.

#### 5.2.3 Legalisers

`legalize_pmpcfg_byte(old, b)` (P §3.7.1, §3.7.1.1, §3.7.1.2 p.71–73; sail `pmpWriteCfg`, `pmp_regs.sail:99-133`):
1. If `old.L = 1`: return `old` ("writes to pmpicfg and pmpaddri are ignored … remain locked until the hart is reset", p.73; L locks even with A = OFF).
2. `n := b && 0x9F` (clear bits 6:5).
3. If `n.R = 0 ∧ n.W = 1`: `n.R := n.W := n.X := 0`, keeping L and A ([D49]).
4. If `G ≥ 1 ∧ n.A = NA4`: `n.A := OFF` (never with G = 0; [D50]).
5. Return `n`.
The lock test uses the **old** byte, so a write that sets L takes full effect. Changing A never changes stored `pmpaddr`. Locking entry i does not protect `pmp<i−1>cfg`.

Writing `pmpcfg<n>` with final value `v` (after CSRRS/CSRRC): for k = 0..7, `i = 4n + k`: if `i < PMP_COUNT` then `cfg[i] ← legalize_pmpcfg_byte(cfg[i], v[8k+7:8k])` (sail `pmpWriteCfgReg`, `:136-152`).

`legalize_pmpaddr(i, v)`:
1. If `cfg[i].L = 1`: ignore.
2. If `i + 1 < PMP_COUNT ∧ cfg[i+1].L = 1 ∧ cfg[i+1].A = TOR`: ignore ("If PMP entry i is locked and pmpicfg.A is set to TOR, writes to pmpaddri-1 are ignored", p.73).
3. Else `stored[i] ← v && ones(54)` (= `zext(v[53:0])`; sail `pmpWriteAddr`, `pmpWriteAddrReg`, `:155-172`).

### 5.3 Address matching (P §3.7.1.1 p.72–73)

`region(i)` = byte interval `[lo, hi)` or ∅; `gmask = ~ones(G)` (all ones for G = 0):
- **OFF**: ∅.
- **TOR**: `top = (view(i) && gmask) << 2`; `bot = (i = 0) ? 0 : (view(i−1) && gmask) << 2`, irrespective of `cfg[i−1]` (p.72). If `bot ≥ top`: ∅ (p.72). Else `[bot, top)`.
- **NA4** (G = 0 only): `lo = stored[i] << 2`, `hi = lo + 4`.
- **NAPOT**: `y = view(i)`; `m = y ?? (y + 1)` (= `ones(t+1)` if `y` has `t` trailing ones); `lo = (y && ~m) << 2`; `hi = lo + ((m + 1) << 2)`, size `2^(t+3)` (Table 24 p.72; sail `pmpMatchAddr`, `pmp_control.sail:117-129`). `y < 2^54` keeps everything below `2^57`; `y = ones(54)` covers `[0, 2^57)`.

Bounds lemma: with G = 0 every bound is a multiple of 4; NAPOT bounds are multiples of 8.

Classifying access `[a, a+n)`, `n ∈ {1, 2, 4, 8}`, `last = a + (n − 1)` (never wraps for aligned accesses; do not compare `a + n`, which can overflow to 0):

| Result | Condition |
|---|---|
| NoMatch | region = ∅, or `last < lo`, or `a ≥ hi` |
| Match | `lo ≤ a ∧ last < hi` |
| Partial | otherwise |

(sail `pmpRangeMatch`, `pmp_control.sail:64-75`.) Corollary: with G = 0 and naturally aligned `n ≤ 4`, Partial is impossible; with `n = 8`, Partial needs an NA4 entry or a TOR bound with `pmpaddr` bit 0 = 1 inside the doubleword; NAPOT never partially matches an aligned access of ≤ 8 bytes.

### 5.4 `pmpCheck(a, n, kind, p) -> bool` ([D53], R3)

Inputs: physical address `a` (= effective address, `satp` Bare; *WP7 amendment:* the translated address, `design-smode.md` §3.5, and for the read of a PTE its physical address with `p` = S and `kind` = Read, [S14]); width `n` (1, 2, 4, 8 for data; 2 for a fetch parcel); `kind ∈ {Read, Write, ReadWrite, Execute}`; privilege `p ∈ {M, S, U}` (fetch: `curPrivilege()`; data: `effectivePrivilege()`, §2.3.6).

1. If `PMP_COUNT = 0`: return T (the no-match failure applies only "if at least one PMP entry is implemented", P §3.7.1.3 p.73).
2. For i = 0 .. PMP_COUNT − 1 in increasing order (fixed bound, no recursion; an L3 `for` loop or unrolled):
   - NoMatch: continue.
   - **Partial: return F**, also in M-mode ("The matching PMP entry must match all bytes of a memory operation, or the operation fails, irrespective of the L, R, W, and X bits", p.73).
   - Match: if `p = M ∧ cfg[i].L = 0` return T; else return `perm(cfg[i], kind)` (p.73).
3. No match: return `p = M` (p.73; with 16 entries all OFF every S/U access fails).

`perm(cfg, kind)` (P §3.7.1 p.72; sail `pmpCheckRWX`, `pmp_control.sail:12`):

| kind | Used by | Allowed iff |
|---|---|---|
| Execute | fetch parcels | X |
| Read | LB, LH, LW, LD, LBU, LHU, LWU, FLW, FLD, C.LW, C.LD, C.LWSP, C.LDSP, C.FLD, C.FLDSP, **LR.W, LR.D** | R |
| Write | SB, SH, SW, SD, FSW, FSD, C.SW, C.SD, C.SWSP, C.SDSP, C.FSD, C.FSDSP, **SC.W, SC.D** | W |
| ReadWrite | AMO*.W/.D | R ∧ W (= W by the §5.2.1 invariant, matching p.72's wording) |

#### 5.4.1 Facts for the step library

- **M-mode inertness** (corrects plan WP3, R12): `p = M ∧ (∀i. ¬cfg[i].L)` gives T for every aligned access with `n ≤ 4` and every fetch parcel; for `n = 8` it additionally needs no Partial, e.g. H4 "every entry OFF or NAPOT" (§1.5). Under [D22] and invariant §2.3.6, `p = M` for data needs H1 ∧ H2.
- **Fetch shortcut**: with PC 4-aligned, both parcels of a 32-bit instruction are in one 4-byte word and get the same verdict.

### 5.5 Where checks apply (P §3.7 p.70; §3.1.6.4 p.35; §3.7.2 p.74)

1. Fetch: `curPrivilege()`; MPRV never applies.
2. Explicit loads, stores, AMOs, LR/SC, F/D loads/stores: `effectivePrivilege()` (§2.3.6); MPP = S behaves as U.
3. MXR, SUM: no effect on PMP (p.35).
4. Not checked: CSR accesses, FENCE, FENCE.I, SFENCE.VMA.
5. Timing: PMP CSR changes take effect for the very next access, including the next fetch ("If page-based virtual memory is not implemented, memory accesses check the PMP settings synchronously, so no SFENCE.VMA is needed", p.74).
6. Precision: "PMP violations are always trapped precisely" (p.70): a faulting access has no architectural effect.

### 5.6 Memory access exceptions

#### 5.6.1 Codes and `mtval` (P Table 16 p.50; §3.1.16 p.52)

Codes 0, 1, 4, 5, 6, 7 with `mtval` as in §4.2. Because accesses are never split, "the portion of the access that caused the fault" (p.52) is the whole access, so `mtval` = effective address. **L3 bug**: `LR_W`/`LR_D` raise `AMO_Misaligned` (6) when misaligned; LR is a load, so the code is 4 ([D57]; sail `vmem_read_addr` "LR faults like a normal load", `sys/vmem_utils.sail:200-212`).

#### 5.6.2 Priority

See §4.3: misaligned (4/6) above access fault (5/7), without a PMP check. In sail the `memory.misaligned.exceptions` check is before translation and PMP (`sys/vmem_utils.sail:200-212, 316-326`; `extensions/A/zaamo_insts.sail:95-101`), so cfg §6.10 matches.

#### 5.6.3 Procedures

**Data access** (every explicit access):
1. Compute effective address `a` and width `n`.
2. If `a mod n ≠ 0`: raise 4 (load, FP load, LR) or 6 (store, FP store, SC, AMO), `tval = a`; stop.
3. `p := effectivePrivilege()`; `pa := a` (`translateAddr` identity; WP7 inserts translation here). *WP7 amendment (`design-smode.md` §3.8):* `pa` is the translation of `a` with privilege `p`, which may raise a page fault (13 or 15), or an access fault (5 or 7) if the PMP denies the read of a PTE; `tval = a` in every case.
4. SC only: do step 5 whether or not the reservation matches ([D60]). If step 5 passes and the reservation does not match, the SC fails: `rd := 1`, no memory write.
5. If `¬pmpCheck(pa, n, kind, p)`: raise 5 (Read) or 7 (Write, ReadWrite), `tval = a`; stop.
6. Perform the access.

**Instruction fetch** (P §3.7.1 p.72, §3.1.16 p.52, U §4.9 p.76; [D59]):
1. `PC[0] = 0` always holds (keep the defensive check in `Fetch()`).
2. If `¬pmpCheck(PC, 2, Execute, curPrivilege())`: raise 1, `tval = PC`.
3. Read the 16-bit parcel; if `parcel[1:0] ≠ 11` it is a complete 16-bit instruction.
4. Else if `¬pmpCheck(PC+2, 2, Execute, curPrivilege())`: raise 1, **`tval = PC+2`**, `mepc = PC`.
5. Read the second parcel.
This is the existing `Fetch()` structure (`FETCH_FAULT(vPC)`, `FETCH_FAULT(vPC + 2)`), and must be mirrored in `riscv_step$Fetch_def` (F1). sail with Ziccif does one 4-byte check at a 4-aligned PC (`postlude/fetch.sail:83-112`); since every bound is a multiple of 4, verdict and `mtval` are identical. A 16-bit instruction in the last 2 bytes of an executable region never faults.
*WP7 amendment (`design-smode.md` §3.8, [S16]):* each parcel is first translated with `curPrivilege()`, which may raise 12, or 1 if the PMP denies the read of a PTE, with the same `tval`; the PMP check of steps 2 and 4 is then of the physical address. `fetchAddr` gives the address or the code, `FETCH_FAULT(e, addr)` carries the code, and `riscv_step$Fetch_def` mirrors this with the patterns `TR_Address`/`TR_Fault` (WP7 stage 3).

#### 5.6.4 Misaligned behaviour by instruction class (U §2.1.6 p.37; §5.2 p.116; §5.6 p.120–121; P §3.6.4 p.67)

- Loads/stores incl. F/D and compressed: EEI may support them or raise misaligned/access fault; here 4/6 ([D55]).
- LR/SC: "an address-misaligned exception or an access-fault exception will be generated" (U p.116); a MAG never relaxes this; here 4/6 ([D57]).
- AMOs: misaligned or access fault (U p.120–121); outside a MAG an exception is mandatory (P p.67); here 6 ([D56]).
- No store is wider than XLEN, so the split-store and partially-visible-store rules (P §3.7.1.3 p.73) never arise.

### 5.7 PMAs of the flat-memory model (P §3.6)

| PMA | Value | Source |
|---|---|---|
| Region | main memory, all of `[0, 2^64)` ([D54]) | P §3.6.1 p.65 |
| Access widths | 1, 2, 4, 8 bytes; fetch everywhere | P §3.6.2 p.65 |
| Misaligned access | not supported (4/6) | P §3.6.2 p.65; U p.37 |
| MAG | none ([D58]) | P §3.6.4 p.67 |
| AMO | AMOArithmetic (no Zacas/Zabha) | P §3.6.3.1 p.66, Table 22 |
| Reservability | RsrvEventual | P §3.6.3.2 p.66 |
| Ordering | RVWMO (no effect with one hart) | P §3.6.5 p.67 |
| Coherence, cacheability | coherent, cacheable; not modelled | P §3.6.6 p.68 |
| Idempotency | idempotent | P §3.6.7 p.69 |

Consequences: every access fault comes from PMP. A MAG of any size would contradict the trap-everything policy ("will not raise an exception for reasons of address alignment", p.67). Do not advertise Zicclsm (U §4.14 p.79); Ziccamoa, Ziccrse, Ziccif are satisfied but irrelevant. The CLINT words are ordinary memory under [D67] (§6.6), so no I/O-region PMA exists.

### 5.8 PMP reset (P §3.4 p.63)

Mandated: A = L = 0 for every entry. Model: every `pmpcfg` byte 0 and every `pmpaddr` 0 ([D62]). After reset all entries are OFF: M-mode unaffected; every U-mode access faults until M programs an entry. sail `reset_pmp` (`pmp_control.sail:183`) clears only A and L; the other bits are expected zero in the C emulator (verify in WP0).

### 5.9 Interaction with page-table walks (WP7; design only)

1. `pmpCheck` takes physical addresses and returns a boolean; translation is inserted between §5.6.3 data steps 3 and 5 and before fetch step 2, each fetch parcel translated separately.
2. Every PTE read is `pmpCheck(pte_addr, 8, Read, S)` and A/D update `pmpCheck(pte_addr, 8, Write, S)`: "the effective privilege mode for implicit page-table accesses is S" (P §3.7 p.70, §3.7.2 p.74), even for U-mode or MPRV accesses.
3. A failing PTE access raises the access fault of the **original** access type: 1, 5 or 7 (P §12.3.2 steps 2 and 9 p.134). This is why the caller picks the code (R3).
4. With translation, `mtval` is the faulting virtual address "even for physical-memory access-fault exceptions" (P §3.1.16 p.52).
5. Misaligned data accesses still raise 4/6 before translation.
6. No TLB, so PMP stays synchronous; SFENCE.VMA after a PMP write is required of software but a no-op in the model.

### 5.10 Divergences to expect against sail

- M-mode accesses outside sail's configured RAM/ROM/MMIO regions or at addresses ≥ 2^56: sail faults (1/5/7), the model succeeds ([D54]). The corpus must avoid this; treat any occurrence as a harness issue.
- SC with no reservation to a PMP-denied address: both raise 7 only after the L3 SC is reordered per [D60] (today L3 returns `rd = 1`).
- Misaligned LR: both report 4 once the L3 bug (§5.6.1) is fixed and cfg sets `lrsc` to `AlignmentException`.
- CLINT accesses of odd width, AMO/LR/SC or fetch in the CLINT window: sail faults, the model treats them as memory (§6.6.2).

---

## 6. Counters, timers and reset

Scope: Zicntr, the M-mode HPM CSRs, `mcounteren`/`scounteren`/`mcountinhibit`, the CLINT timer and software interrupt (`mtime`, `mtimecmp`, `msip`), reset, NMI, and the ID/configuration CSRs.

### 6.1 Parameters

| Name | Value | Source |
|---|---|---|
| implemented `mhpmcounter`s | 0 (all 29 RO0) | P §3.1.10 p.46; cfg `writable_hpm_counters = 0` |
| `COUNTEREN_MASK` | `0x7` (CY, TM, IR) | cfg `{m,s}counteren_writable_bits = 0x7` |
| `COUNTINHIBIT_MASK` | `0x5` (CY, IR; bit 1 always 0) | P §3.1.12 p.47, Figure 19 ([D28]) |
| `ENVCFG_MASK` | `0x1` (FIOM) | P §3.1.18 p.54 ([D29]) |
| `CLINT_BASE` | `0x0200_0000` | sail `platform.clint.base`; S3K `__mtimecmp = 0x2004000`, `__mtime = 0x200bff8` |
| `MSIP_ADDR(h)` | `CLINT_BASE + 4·h` (32-bit, bit 0 = MSIP) | sail `sys/platform.sail:88-108`; P §3.1.9 p.44 |
| `MTIMECMP_ADDR(h)` | `CLINT_BASE + 0x4000 + 8·h` (64-bit) | sail `platform.sail:96-113` |
| `MTIME_ADDR` | `CLINT_BASE + 0xBFF8` (64-bit, shared) | sail `platform.sail:103-109` |
| ticks per step | 1 ([D63]); cfg `platform.instructions_per_tick = 1` | sail `c_emulator/riscv_sim.cpp:515, 592-596` |
| reset PC | ELF entry, set by the harness | sail `pc_reset_address` |

`pAddrIdx = bits(61)` (L3 71) and the HOL `component MEM(a::pAddrIdx) :: regType` over `MEM8` (L3 1661-1672): `mtime()` is `MEM(0x40_17FF)`, `mtimecmp(0)` is `MEM(0x40_0800)`, `msip(0)` is bit 0 and `msip(1)` bit 32 of `MEM(0x40_0000)`. All are naturally aligned, so each is exactly one `MEM` word.

### 6.2 Counter state

| Field | Storage | Layout / notes |
|---|---|---|
| `mcycle` | `c_cycles :: id -> regType` ([D68]) | 64-bit on all harts (P §3.1.10 p.46), wraps |
| `minstret` | `c_instret :: id -> regType` | same |
| `minstret_written` | `c_minstret_written :: id -> bool` (model-internal, never read by a CSR) | set by an explicit `minstret` write, cleared at the start of each step (sail `minstret_increment`, `core/counters.sail:26`) |
| `mcounteren` | `MCSR.mcounteren` | 32-bit: CY 0, TM 1, IR 2, HPM3–31 at bits 3–31 (P §3.1.11 Figure 18 p.46–47) |
| `scounteren` | `SCSR.scounteren` | same layout (P §12.1.5 Figure 56 p.119); must exist because `misa.S = 1` |
| `mcountinhibit` | `MCSR.mcountinhibit` | CY 0, bit 1 RO0, IR 2, HPM 3–31 (Figure 19 p.47) |

Constants (not stored): `mhpmcounter3..31` = `mhpmevent3..31` = 0; `mvendorid` = `marchid` = `mimpid` = `mconfigptr` = 0. `mhartid` stays a stored `MCSR` field set by `initMachine(hartid)`, now at 0xF14. Replaced: `c_cycles`/`c_instret` keep their names; `UserCSR.{cycle,time,instret}_delta`, `MCSR.mtime_delta`, `SCSR.stime_delta`, `HCSR.htime_delta` and `clock` (L3 407-425, 505-516, 653-656) go.

### 6.3 CSRs of this area (RV64)

| CSR | Addr | Exists | Read | Write |
|---|---|---|---|---|
| cycle / time / instret | 0xC00 / 0xC01 / 0xC02 | yes | `mcycle` / `mtime()` / `minstret` | illegal (read-only) |
| hpmcounter3–31 | 0xC03–0xC1F | **no** ([D25]) | illegal | illegal |
| mcycle | 0xB00 | yes | `mcycle` | `mcycle ← v` |
| (hole) | 0xB01 | no | illegal | illegal |
| minstret | 0xB02 | yes | `minstret` | `minstret ← v; minstret_written ← T` |
| mhpmcounter3–31 | 0xB03–0xB1F | yes, RO0 ([D26]) | 0 | ignored, no trap |
| mcountinhibit | 0x320 | yes ([D28]) | `zext(mcountinhibit)` | `v[31:0] && 0x5` |
| mhpmevent3–31 | 0x323–0x33F | yes, RO0 ([D26]) | 0 | ignored, no trap |
| mcounteren | 0x306 | yes | `zext(mcounteren)` | `v[31:0] && 0x7` ([D27]) |
| scounteren | 0x106 | yes | `zext(scounteren)` | `v[31:0] && 0x7` ([D27]) |
| menvcfg / senvcfg | 0x30A / 0x10A | yes | `zext(FIOM)` | `v && 0x1` ([D29]) |

Examples: S3K's `csrwi mcounteren,15` and `csrwi scounteren,15` read back 7; `csrwi mcountinhibit,0` reads back 0. The RV32 halves and the absent CSRs of this area are in §3.6.2.

### 6.4 Gating unprivileged counter reads

Rules: when a `mcounteren` bit is clear, reading the counter in S or U is illegal; when set, access is permitted "in the next implemented privilege mode (S-mode if implemented, otherwise U-mode)" (P §3.1.11 p.47). "U-mode may only access a counter if the corresponding bits in scounteren and mcounteren are both set" (P §12.1.5 p.119). Neither register affects counting.

`counterReadAllowed(csr, p)` for `csr ∈ 0xC00..0xC1F`, `i = csr<4:0>`:
1. If `i ≥ 3`: F (hpmcounters absent, even in M; [D25]).
2. If `p = M`: T.
3. If `p = S`: `mcounteren<i>`.
4. If `p = U`: `mcounteren<i> ∧ (¬misa.S ∨ scounteren<i>)`; here `misa.S` is constant 1, so `mcounteren<i> ∧ scounteren<i>`.
F raises illegal (2). This matches sail `feature_enabled_for_priv`/`counter_enabled` (`core/sys_regs.sail:1274-1292`; `extensions/Zicntr/zicntr_control.sail:18-20`). Do **not** copy l3riscv's U case (its `riscv.spec` 1346-1351 tests only `scounteren`). Step 3 is already the full S rule for WP7; Sstc would later add `stimecmp` gated by `mcounteren.TM` and `menvcfg.STCE`.

### 6.5 Counting rules

Source rules:
- C1: `mcycle` counts cycles, `minstret` retired instructions; both writable; arbitrary after reset (P §3.1.10 p.46).
- C2: "Any CSR write takes effect after the writing instruction has otherwise completed" (p.46).
- C3: `mcountinhibit.CY/IR` stop the increment; `mtime` cannot be inhibited (P §3.1.12 p.47–48).
- C4: a CSR read of a counter returns the value before the instruction; an explicit write is done *instead of* the increment (U §4.2 p.64).
- C5: "Instructions that cause synchronous exceptions, including ECALL and EBREAK, are not considered to retire" (U §4.3 p.67; P §3.3.1 p.61).
- C6: xRETs retire (P §7.3 p.90, consistent with sail `RETIRE_SUCCESS`).

What retires ([D64]):

| Event | Retires? |
|---|---|
| any instruction completing without exception (ALU, branch, load/store/AMO, LR, SC success or failure, FENCE, FENCE.I, CSR instructions, legal SFENCE.VMA) | yes |
| MRET, SRET (where legal) | yes |
| WFI completing as a NOP (M; S with TW = 0) | yes (sail `wait_is_nop` path, `postlude/step.sail:366-377`) |
| WFI in U (illegal) | no |
| ECALL, EBREAK, C.EBREAK | no |
| any synchronous exception | no |
| a step that takes an interrupt | no (sail `Step_Pending_Interrupt`) |

Per step (replaces `tickClock`, `incrInstret`, `checkTimers`, `CYCLES_PER_TIMER_TICK` and the `incrInstret()` calls in `Next`, L3 5261-5345):
1. `minstret_written ← F`.
2. `incIR ← ¬mcountinhibit.IR`, sampled **before** execution (C2; sail `should_inc_minstret` at step start, `step.sail:281`).
3. Run the step (§4.5). `retired` per the table. CSR reads see pre-step values (C4); writes to `mcycle`/`minstret` store `v` (the latter also sets `minstret_written`).
4. If `retired ∧ incIR ∧ ¬minstret_written`: `minstret ← minstret + 1` ([D65]).
5. If `¬mcountinhibit.CY` (value **after** the step, [D66]): `mcycle ← mcycle + 1`, in **every** step, including trap and interrupt steps ([D63]; sail `clint_tick_clock`, `platform.sail:225-236`).
6. Harness: `mtime ← mtime + 1` (§6.6.3).

Tests to include: after `csrw minstret, v` the next instruction reads `v`; after `csrw mcycle, v` it reads `v+1` ([D65]); `csrr x, instret` with `minstret = n` returns `n` and leaves `n+1`; `ecall` leaves `minstret` unchanged and advances `mcycle`. `hpmcounter`s never change.

HOL: step theorems gain `mcycle := mcycle + (if CY then 0 else 1)` and the `minstret` update, replacing today's `c_cycles`/`c_instret`/`clock` updates (no regression); the step library may assume `¬CY ∧ ¬IR` to fold both to `+1`. `log_instruction` (L3 5253) prints `c_instret`; the harness should print its own step number instead (sail prints `step_no`), because `minstret` is writable and inhibitable. `NextRISCV` does not model counters (open question 4).

### 6.6 Platform timer and software interrupt (`mtime`, `mtimecmp`, `msip`)

#### 6.6.1 Rules

- `mtime`: memory-mapped M-mode RW 64-bit real-time counter, constant frequency, wraps (P §3.2.1 p.59). `mtimecmp`: memory-mapped 64-bit, one per hart (p.59).
- "A machine timer interrupt becomes pending whenever mtime contains a value greater than or equal to mtimecmp, treating the values as unsigned integers" (p.59): **`MTIP = mtimecmp ≤u mtime`**. Changes need only be reflected "eventually" (p.60).
- Naturally aligned 64-bit accesses on RV64 are atomic (p.60).
- `mip.MTIP` is read-only, cleared by writing `mtimecmp`; `mip.MSIP` is read-only in `mip`, driven by the memory-mapped 32-bit `msip` (bits 31:1 RO0) (P §3.1.9 p.44).
- `time` is a read-only shadow of `mtime`; reads may be converted to loads of `mtime` (P §3.1.11 p.47; §3.2.1 p.60).

#### 6.6.2 Representation: memory-backed CLINT ([D67], R5)

No new declared state. Define:
```
mtime()     = MEM(MTIME_ADDR >> 3)                           -- shared by all harts
mtimecmp(h) = MEM(MTIMECMP_ADDR(h) >> 3)
msip(h)     = MEM(MSIP_ADDR(h) >> 3)<32 * (h mod 2)>          -- bit 0 of the 32-bit msip word
MTIP(h)     = mtimecmp(h) <=+ mtime()                         -- unsigned
MSIP(h)     = msip(h)
```
- `mip_eff` (§4.1.3) uses `MTIP(procID)`, `MSIP(procID)`, `c_extSEIP(procID)`, `c_extMEIP(procID)`. Computing MTIP on demand equals sail's sample at step start (`core/interrupt_regs.sail:246-270`), because within one instruction a store to `mtimecmp` and a read of `mip` never both happen.
- `time` CSR read = `mtime()`.
- Loads, stores, AMOs to CLINT addresses are ordinary memory accesses (same PMP and alignment rules); `sw` to one half of `mtimecmp` updates that half, as sail's 4-byte CLINT store does.
- Known deviations from sail's CLINT (not exercised by the corpus or S3K): sail access-faults (5/7) on accesses that are not exactly 4 or 8 bytes at a register address, on AMO/LR/SC in the IO region, and on fetch from it (1); the harness's `mtime` writes do not invalidate a load reservation.
- Why not declared state (the plan's wording, and the compatibility analysis's `c_mtimecmp`): P §3.2.1 p.59 requires the registers to be memory-mapped, so declared state needs an MMIO dispatch after the PMP check in `rawReadData`/`rawWriteData`/fetch (sail `clint_load`/`clint_store`, `platform.sail:111-222`), and every load/store step theorem then splits on `inCLINT(pa)` with HolBA asserting `¬inCLINT` on every access. The helpers above isolate the addresses, so that option can be swapped in later.

#### 6.6.3 What the harness drives

1. After every completed `Next` step (including trap and interrupt steps): `MEM(MTIME_ADDR>>3) ← MEM(MTIME_ADDR>>3) + 1` (sail's tick moment with one tick per step). A program store of `v` to `mtime` reads back `v+1` in the next step, as in sail.
2. `c_extMEIP`, `c_extSEIP` stay false (no PLIC); cfg disables sail's `simple_interrupt_generator` ([D73]).
3. Reset and boot values (§6.7).
4. HTIF `tohost` handling (outside the spec, [D13]).
In HOL nothing drives `mtime`; HolBA sees `rdtime` and CLINT loads as ordinary memory reads (open question 13).

### 6.7 Reset (P §3.4 p.63)

`initMachine(hartid)` establishes exactly this table; the harness sets `pc`, `x10`, `x11` and the CLINT memory. Replaces `initIdent`/`initMachine` (L3 5354-5385) and part of `initRegs`; remove the `mstatus.VM`, `mcpuid`, `MFS ← Initial` lines; `initIdent` rejects anything but RV64I.

| State | Value | Mandated? |
|---|---|---|
| privilege | M (`c_privilege := 3w`) | yes |
| `mstatus` | read value `0x0000_000A_0000_0000`: MIE = MPRV = 0 (mandated), MBE = 0 (mandated, RO0), UXL = SXL = 2, and FS = Off, MPP = U, MPIE = SIE = SPIE = SPP = MXR = TVM = TW = TSR = 0 ([D70]) | partly |
| `misa` | `0x8000_0000_0014_112D` (maximal set; sail `reset_misa`, `sys_control.sail:505-527`) | yes |
| load reservation | none | yes |
| `pc` | ELF entry (harness) | impl.-defined |
| `mcause` | 0 | "should" |
| `pmpcfg*` | all bytes 0 (A = L = 0 mandated; R/W/X = 0 chosen, [D62]); `pmpaddr0..15 = 0` | partly |
| every WARL field | legal value | yes |
| `mtvec`, `stvec` | 0 (Direct) ([D71]); replaces today's `0x100` | no |
| `mepc`, `mtval`, `mscratch`, `sepc`, `stval`, `sscratch`, `scause` | 0 | no |
| `mie`, stored `mip` bits, `medeleg`, `mideleg` | 0 | no |
| `mcounteren`, `scounteren`, `mcountinhibit` | 0 | no |
| `mcycle`, `minstret` | 0 (arbitrary allowed, P §3.1.10 p.46); `minstret_written = F` | no |
| `menvcfg`, `senvcfg`, `satp` | 0 (`satp` Bare) | no |
| `c_extMEIP`, `c_extSEIP` | F | no |
| `x1..x31`, `f0..f31`, `fcsr` | 0; then harness sets `x10 = mhartid`, `x11 = 0x1000` ([D72]; sail `init_boot_requirements`, `postlude/model.sail:35-39`) | no |
| CLINT memory | `mtime = 0`, `mtimecmp(h) = 0`, `msip(h) = 0` (harness-initialised `MEM8`); hence **MTIP = 1 from the first step**, as in sail ([D69]) | no |
| model-internal | `NextFetch = None`, `ExitCode = 0` | — |
| `hgatp`, `vsatp`, `mnstatus`, `mseccfg` fields | n/a (no H, Smrnmi, Smepmp, Zkr, Zicfilp) | — |

The unspecified values match sail's C++ emulator, whose uninitialised registers are 0 (`UNDEFINED(fbits)` returns 0, `sail/lib/sail.c:650-655`; confirm in WP0).

### 6.8 Identification and configuration CSRs (P §3.1.2–3.1.5, §3.1.17–3.1.19)

| CSR | Spec rule | Model ([D31]) |
|---|---|---|
| `mvendorid` 0xF11 | 32-bit RO; Bank 31:7, Offset 6:0; 0 = non-commercial (p.29–30) | 0 |
| `marchid` 0xF12 | RO; 0 = not implemented (p.30) | 0 |
| `mimpid` 0xF13 | RO; 0 = not implemented (p.31) | 0 (today's `RVSource = 0x8000` dropped) |
| `mhartid` 0xF14 | RO, unique, one hart is 0 (p.31) | `initMachine(hartid)`; 0 for the single hart |
| `mconfigptr` 0xF15 | RO, must be implemented, may be 0; bits 2:0 = 0 on RV64 (p.53) | 0 |
| `menvcfg` 0x30A | exists iff U (p.56). Fields FIOM 0, LPE 2, SSE 3, CBIE 5:4, CBCFE 6, CBZE 7, PMM 33:32, DTE 59, CDE 60, ADUE 61, PBMTE 62, STCE 63 (Figure 25 p.54); all but FIOM RO0 without their extensions (p.54–56); FIOM may be RO0 only while `satp.MODE` is always Bare (p.54) | FIOM writable storage (no effect: L3 FENCE is a no-op); all else RO0 ([D29]) |
| `senvcfg` 0x10A | FIOM 0, LPE 2, SSE 3, CBIE 5:4, CBCFE 6, CBZE 7, PMM 33:32 (P §12.1.10 p.122–124) | FIOM writable; all else RO0 |
| `mseccfg` 0x747 | "exists if any extension that adds a field to mseccfg is implemented. Otherwise, it is reserved" (p.56): Zkr, Smepmp, Smmpm, Zicfilp | absent, illegal; PMP behaves as MML = MMWP = RLB = 0 ([D30]) |

### 6.9 NMI (P §3.5 p.63–64)

No NMI input, vector or `mcause` values; Smrnmi CSRs absent (illegal); MNRET not decoded. Nothing in `Next` jumps to an NMI vector. Safe because NMIs are "only used for hardware error conditions" (p.63).

### 6.10 Consolidated sail oracle configuration (`rv64gc_mu_pmp.json`)

Settings this design requires, from all chapters. "Change" marks a difference from sail's default; settings the CSR analysis found already present in cfg are marked "present".

| Key | Value | Why | Status |
|---|---|---|---|
| `base.misa_implemented` | true | §2.2 | default |
| `extensions.{M,A,F,D,S,U}.mutable_misa` | false | [D14] | present (change from default) |
| `extensions.C.mutable_misa` | true | [D14] | default |
| `extensions.B`, `Zba`, `Zbb`, `Zbs`, `.supported` | false | `misa.B = 0` | change |
| `extensions.H.supported` | false | | |
| `extensions.V.support_level` | `"Disabled"` | | |
| `base.mstatus.fs_legal_states` | `ExtContext_FourState` | [D16] | default |
| `base.mstatus.vs_legal_states` | `ExtContext_Off` | [D18]; default keeps VS writable when S is present | **change** |
| `extensions.F.fflags_dirty_policy` | `Fflags_Dirty_Flag` | [D17] | **change** (default `Precise`) |
| `extensions.Zicfilp`, `Zicfiss`, `Smdbltrp`, `Ssdbltrp`, `Sstc`, `Sscofpmf`, `Smcntrpmf`, `Sdtrig`, `Zkr`, `Zihpm` `.supported` | false | absent extensions; Zkr off removes `mseccfg` ([D30]) | present / change |
| `extensions.Zicntr.supported` | true | | |
| `extensions.Sv39/Sv48/Sv57.supported` | false; `Svbare` true. *WP7 stage 2:* all three true, with `Ssccptr` and `Svade` true, `Svadu`, `Svvptc`, `Svnapot`, `Svpbmt`, `Svrsw60t59b`, `Svinval`, `Svukte` false, and `memory.physaddr_bits` 56, `memory.asidlen` 16 (`design-smode.md` §4.2) | Bare only (SUM RO0); WP7: [S3], [S7]-[S9], [S12], [S13] | present; WP7: Sv39/Sv48/Sv57 true are sail's defaults, the extensions set false are **changes** |
| `extensions.Svbare.sfence_vma_illegal_if_svbare_only` | false | [D46] | present (change from default) |
| `platform.wfi_is_nop` | false | [D23], [S20] | default (WP7; `true` before) |
| `platform.max_time_to_wait` | 0 | [S20] | **change** (WP7; default 10) |
| `platform.wfi_available_to_user_mode` | false | [D23] | default |
| `platform.instructions_per_tick` | 1 | [D63] | **change** (default 2) |
| `platform.simple_interrupt_generator.supported` | false | [D73] | **change** |
| `platform.vendorid/archid/impid/hartid` | 0 | [D31] | present |
| `platform.clint.base` | `0x2000000` | §6.1 | default |
| `base.medeleg.delegatable_bits` | `0xB3FF` | [D40] | present |
| `base.mcounteren_writable_bits`, `scounteren_writable_bits` | `0x7` | [D27] | present |
| `base.mcountinhibit` | `{supported: true, writable_bits: {len: 32, value: "0x5"}}` | [D28]; default `0xFFFF_FFFD` | **change** |
| `writable_hpm_counters` | `0x0` | [D26] | present |
| `base.writable_fiom` | true | [D29] | default |
| `base.reserved_behavior.xtvec_mode` | `Xtvec_Ignore` | [D39] | default |
| `base.mtvec`/`stvec` base alignment | 2 for both modes | [D39] | default |
| `base.xtval_nonzero.*` | true | [D43] | default |
| `memory.pmp` | `{grain: 0, count: 16, usable_count: 16, tor/na4/napot_supported: true}` | [D47], [D48], [D50] | present |
| `base.reserved_behavior.pmpcfg_write_only` | `PMP_ClearPermissions` | [D49] | default |
| `memory.physaddr_bits` | 56 | [D51] | default (RV64) |
| `memory.misaligned.exceptions` | `load_store`, `amo`, `lrsc` all `{"Some":"AlignmentException"}` | [D55]–[D57] | **change** |
| `memory.regions[RAM].attributes.misaligned_atomicity_granule_size_exp` | 0 | [D58] | **change** (default 4) |
| `memory.regions[RAM]` base/size | cover every address the corpus touches | [D54] | harness |

Whether the JSON overlay mechanism merges partial `base`/`platform`/`memory` objects with the defaults must be confirmed (open question 15).

---

## 7. Decisions

Each row merges the decision items of the source analyses that cover the same choice. "Spec" citations are printed pages. Rows marked † resolve a contradiction (see §0).

| # | Topic (§) | Options | Recommendation | Rationale | sail default |
|---|---|---|---|---|---|
| D1 † | Type of current-privilege state (§1.4.1) | (a) `id -> Privilege`; (b) `id -> priv_level` (bits(2)) read via `privilege()` | (b) | HolBA lifts only word-valued state (F5); keeps every `= 3w` hypothesis and `riscv_privilege_cases` shape; `10` unreachable because `privLevel(constructor)` is the only writer | enum `cur_privilege` (`core/sys_regs.sail:13`) |
| D2 | `privilege(0b10)` (§2.1) | (a) `#UNDEFINED`; (b) total, `10`→U; (c) fourth constructor | (b) | `#UNDEFINED` makes it state-passing (F2) and adds an `MPP ≠ 2` hypothesis to every MRET theorem; U agrees with `legalize_mstatus`; (c) keeps a non-spec mode | internal_error; unreachable since MPP legalised to U |
| D3 | Privilege accessor (§1.4.1) | (a) unit function `curPrivilege()` + `setPrivilege(p)`; (b) `component curPrivilege` | (a) | HolBA evaluates ``privLevel (curPrivilege () s)`` (`riscv_stepScript.sml:815`) | direct register |
| D4 | `misa.MXL`, `in32BitMode()` (§2.2) | (a) MXL stored read-only 2, `in32BitMode() = (misa.MXL == 1)`; (b) constant false; (c) keep `curArch()`/`architecture()` | (a) | consumer conjuncts survive as renames; pure (no `not1`, `architecture_def`); MXL encoding P Table 11 p.27 | xlen fixed at build; MXL read-only |
| D5 | `translateAddr` body in WP2 (§3.7) | (a) identity, reads no state; (b) read `satp.MODE` as WP7 will | (a), keeping name and signature as the WP7 hook. **Revised by WP7 [S1], [S2]**: `translateAddr(va, ft, ac, p) -> TransResult` translates with Sv39/Sv48/Sv57 below M and is the identity at M, tested first, and with Bare | `satp` is in hidden `c_SCSR` (F3); unsupported-MODE writes have no effect (P §12.1.11 p.125), so identity is exact | translation with Bare = identity |
| D6 | `mstatus`/`sstatus` field naming (§1.4.2) | (a) spec's unprefixed names; (b) l3riscv `M_`/`S_` prefixes | (a) | L3 allows duplicate field names across types (F6); reusing `MPRV` for bit 17 turns stale `MPRV = 3w` uses into type errors | unprefixed |
| D7 † | `ExceptionType`/`Interrupt` names (§4.2) | (a) keep HOL names, add `Load_Misaligned`, `Fetch_PageFault`, `Load_PageFault`, `Store_AMO_PageFault`, drop `HMode_Env_Call`, rename `AMO_Misaligned`→`Store_AMO_Misaligned`; (b) sail `E_*` names | (a) | no consumer names a constructor; small diff; code 6 is "Store/AMO address misaligned" (P Table 16 p.50) | `E_*` |
| D8 | `TransferControl` trap-return arms (§4.7.5) | (a) `Mret`, `Sret`; (b) `Xret(Privilege)` | (a) | plan WP2.4; consumers match with a wildcard | n/a |
| D9 | Extra CSR access conditions: counteren, TVM, FS (§3.2) | (a) one helper inside `checkCSROp`, signatures unchanged; (b) change `check_CSR_access`'s signature | (a) | HolBA evaluates `checkCSROp_def`, `is_CSR_defined_def`, `check_CSR_access_def` by name; (a) adds one def | `is_CSR_accessible` plus priv and RO checks |
| D10 † | Form of M-mode step-theorem hypotheses (§1.5) | (a) word conjuncts H1–H6 plus one `pmpCheck = T` lemma; (b) one HOL predicate; (c) `pmpCheck(...) = T` as hypothesis | (a), with H4 "every entry OFF or NAPOT" because G = 0 | word conjuncts lift to BIR asserts and drop into `riscv_ok`/`riscv_ID`; (c) is address-dependent; H4 needed by P §3.7.1.3 p.73 | n/a |
| D11 | How prog fixes the privilege (§1.3) | (a) `riscv_ID id mcsr` includes `riscv_c_privilege id 3w`; (b) extra argument | (a) | `riscv_progLib` (`:35`, `:300`) depends on two arguments | n/a |
| D12 | HolBA BIR name for the privilege (§1.3) | (a) keep `"MPRV"`; (b) `"priv"` | (b) | expression changes anyway; `"MPRV"` would collide with the real `mstatus.MPRV` once lifted; about 12 string edits and a selftest log regeneration | n/a |
| D13 | HTIF remnants (§1.2) | (a) drop `mtohost`/`mfromhost` CSRs and HTIF in `Next`, keep `c_ExitCode`/`done` for the harness; (b) remove everything | (a) | harness needs an exit path; no step theorem reads them | HTIF memory-mapped in the platform |
| D14 | Writable `misa` bits (§2.2) | (a) only C; (b) all as sail default; (c) none | (a) | plan pins C writable (commit 116d411e1); writable F/D/A/M add guards to every step theorem; writable S/U bring P §2.4 field modulation (sail: "not currently supported"); with S/U fixed `legalize_mstatus` is independent of `misa` | all `mutable_misa = true` |
| D15 | Illegal `MPP` write (`10`) (§2.3.3) | (a) store `00` (U); (b) keep old; (c) store `11` | (a) | matches sail bit for bit; legaliser independent of old value; equals what MRET leaves | (a) `lowest_supported_privLevel()` |
| D16 | Legal FS states (§2.3.9) | (a) four-state; (b) Off/Dirty only (p.39); (c) RO0 (forbidden with F, p.38) | (a) | identity legaliser; matches current L3 and sail; test suites read back Initial/Clean | `ExtContext_FourState` |
| D17 | When fflags accrual marks FS Dirty (§2.3.9) | (a) `Fflags_Dirty_Flag`: whenever a flag is raised; (b) `Precise`: only if fflags changes; (c) `Instruction`: every instruction that could raise | (a), cfg `fflags_dirty_policy = Fflags_Dirty_Flag` | current `fcsr` component assign already marks Dirty; (b) needs an old/new comparison in every FP theorem; implementation-defined (p.39); revisit in WP1 | `Fflags_Dirty_Precise` |
| D18 | `mstatus.VS` with S, no V (§2.3.1) | (a) RO0; (b) writable four-state storage | (a), cfg `vs_legal_states = ExtContext_Off` | permitted (p.38); no state; SD depends only on FS | `ExtContext_FourState` (writable) |
| D19 | UXL/SXL (§2.3.8) | (a) read-only 2; (b) WARL allowing RV32 | (a) | permitted (p.34); keeps all XLEN-truncation rules dead | read-only 2 |
| D20 † | `mstatus` storage of SD and constants (§2.3.4) | (a) store writable fields only, build constants and SD on read; (b) store the full image, keep SD consistent by invariant | (a) | arbitrary HOL states could otherwise read illegal `mstatus` values; Dirty update becomes the single assignment `FS := 3`; SD is read-only derived (p.40) | (b) |
| D21 | S-related `mstatus` fields; SUM (§2.3.1) | (a) SIE, SPIE, SPP, MXR, TVM, TSR writable storage, SUM RO0; (b) all RO0 | (a). **Revised by WP7 [S19]**: SUM writable, `MSTATUS_WMASK = 0x7E79AA` | with `misa.S = 1` RO0 is forbidden for these (p.32, p.35, p.37); SUM RO0 because `satp.MODE` is read-only 0 (p.35, p.114, p.125); WP7 adds one mask bit | (a) |
| D22 | Scope of the MPRV rule (§2.3.6) | (a) literal: every explicit data access, any mode; (b) only when `cur = M` | (a), with invariant `cur ≠ M ⇒ MPRV = 0` documented | spec wording (p.35) and sail `effectivePrivilege`; equal on reachable states; H2 discharges it in M-mode theorems | (a) |
| D23 | WFI per mode (§4.7.6) | M: NOP or wait; U: always illegal (forced, p.37) or NOP; S: illegal iff TW = 1, or wait then trap | M NOP; U always illegal; S illegal iff TW = 1, else NOP; cfg `wfi_is_nop = true`. **Revised by WP7 [S20]**: S with TW = 1 is illegal iff `read_mip() && mie = 0`, else NOP; cfg `wfi_is_nop = false`, `max_time_to_wait = 0` (§4.7.6) | NOP is legal (p.62); deterministic; p.37 allows immediate trap with TW = 1 | `wfi_is_nop = false`, `wfi_available_to_user_mode = false`; with `wfi_is_nop = true` sail retires S-mode WFI even with TW = 1 (open question 12) |
| D24 | Access to a non-existent CSR (§3.1) | (a) illegal instruction; (b) `#UNDEFINED` | (a), from a whitelist checked before any read | always valid for reserved encodings (P §2.1 p.13); plan §2.2(4) forbids `#UNDEFINED` on reachable states | illegal (`postlude/csr_end.sail:12`) |
| D25 † | `hpmcounter3–31` (§6.3) | (a) Zihpm absent: illegal in all modes; (b) RO0 counters, readable in M | (a) | U-mode behaviour identical (counteren HPM bits RO0); U §4.4 p.68 allows trap; smaller CSR map; matches cfg; corrects plan Appendix A | default Zihpm on; cfg off |
| D26 | `mhpmcounter3–31`, `mhpmevent3–31` (§6.3) | (a) present, RO0, writes ignored; (b) illegal; (c) real counters | (a) | "a legal implementation is to make both … read-only 0" (P §3.1.10 p.46); standard M CSRs must not trap | always accessible; writes dropped with `writable_hpm_counters = 0` |
| D27 | `mcounteren`/`scounteren` writable bits (§6.3) | (a) `0x7`; (b) all 32; (c) none | (a) | both mandatory (p.47, p.119); HPM bits have no counter; S3K writes 15 to both | default `0xFFFFFFFF`; cfg `0x7` |
| D28 | `mcountinhibit` (§6.3) | (a) present, mask `0x5`; (b) mask `0xFFFFFFFD`; (c) absent | (a), cfg `writable_bits = 0x5` | S3K executes `csrwi mcountinhibit,0` at boot, so (c) traps; HPM inhibit bits meaningless | `0xFFFF_FFFD` |
| D29 † | `menvcfg`/`senvcfg` FIOM (§6.8) | (a) FIOM writable, rest RO0; (b) all RO0 (allowed while Bare-only, p.54, p.123) | (a) | FIOM must become writable with Sv39 (WP7), so (a) avoids rework; matches sail default; corrects plan Appendix A | `writable_fiom = true` |
| D30 | `mseccfg` (§6.8) | (a) absent, illegal; (b) present, RO0 | (a) | reserved unless an extension adds a field (P §3.1.19 p.56); classic PMP rules | exists only with Zkr/Zicfilp/Smmpm; cfg `Zkr = false` |
| D31 | ID CSR values (§6.8) | `mvendorid`/`marchid`/`mimpid`/`mconfigptr`: 0 or real values; `mhartid`: 0 or `procID` | all 0; `mhartid = procID` (0 for one hart) | 0 permitted (p.29–31, p.53); trace equality | all 0 |
| D32 | `satp` with Bare only (§3.7) | (a) MODE ≠ 0 ignored, MODE = 0 stores `v`; (b) MODE = 0 stores 0; (c) RO0. Accessibility: M always, S iff TVM = 0, U never (mandated) | (a). **Revised by WP7 [S10]**: MODE ∉ {0, 8, 9, 10} ignored, otherwise `v` stored; accessibility unchanged | unsupported-MODE write has no effect (p.126); Bare with nonzero fields UNSPECIFIED; matches sail; keeps ASID/PPN storage for WP7 | (a); ASIDLEN 16, PABITS 56 |
| D33 | `mcause`/`scause` WLRL (§4.1.6) | (a) keep old unless code supported (sail set incl. 12, 13, 15, 19); `scause` keeps any code ≤ 31; (b) store anything; (c) trap | (a) | deterministic (P §2.3.2 p.25); `scause` must hold 0–31 (p.120); trace equality | `legalize_cause` = (a) |
| D34 | Optional S-level CSRs (§3.6) | `senvcfg`, `scountinhibit`, `stimecmp`: present or absent | `senvcfg` present (FIOM only); `scountinhibit` absent; `stimecmp` absent | `senvcfg` is defined with S; Smcdeleg and Sstc are outside the ISA string; Sstc can be added later without restructuring | `senvcfg` with S; Sstc on by default, off in cfg |
| D35 | Debug/trigger CSRs (§3.6.2) | (a) absent; (b) `tselect` with no triggers | (a) | out of scope; 0x7B0–0x7BF "should" be illegal in M (p.13) | Sdtrig on by default, off in cfg |
| D36 | CSRRW/CSRRWI with `rd = x0`: read? (§3.2) | (a) skip; (b) read and discard | (b) if it simplifies HOL theorems; indistinguishable | no read side effects (P p.13; U p.64); write determination stays on the field index | skips the read |
| D37 | Reserved `frm` values written (§3.7) | (a) store; (b) legalise; (c) trap | (a) | `fcsr` is a plain RW register (U §6.1.2 p.130); reserved only when used by a DYN instruction | stored; `Fcsr_RM_Illegal` on use |
| D38 | When interrupts are taken (§4.5) | (a) start of each step, before fetch, consuming the step; (b) after execution (current L3); (c) lazily | (a) | satisfies "immediately after xRET or CSR write" (p.43–44, p.117); `mepc` = next unexecuted instruction (p.49); per-step trace equality; current (b) skips branch/return steps | (a) (`try_step`) |
| D39 | `mtvec`/`stvec` WARL (§4.1.1) | MODE: Direct, Vectored or both; reserved MODE write: keep old, force Direct, or trap (forbidden); BASE alignment 4 or coarser; `mtvec` writable or fixed | both modes; reserved write keeps old MODE (BASE still written); 4-byte alignment in both; writable; reset 0 | WARL needs only a deterministic legal value (p.25); S3K and tests install handlers; matches sail | `Xtvec_Ignore`, alignment 2, writable |
| D40 | `medeleg` writable mask (§4.1.2) | (a) `0xB3FF`; (b) `0xCB3FF` (adds 18, 19); (c) 0 | (a), reset 0, cfg `delegatable_bits = 0xB3FF` | bits for impossible exceptions "should" be RO0 (p.43); 11 and 16 must be; plan §2.3 wants real S storage; (c) is a constant change later if HOL theorems suffer (open question 8) | effectively `0xCB3FF` |
| D41 | `mideleg` writable mask (§4.1.2) | (a) `0x222`; (b) also M bits 3, 7, 11; (c) 0 | (a), reset 0 | standard; keeps M interrupts in M | effectively `0x222` |
| D42 † | Platform interrupt sources (§4.1.3, §6.6) | (a) all of MSIP, MEIP, SEIP_ext as harness-set state; (b) MSIP from CLINT memory, MEIP/SEIP_ext hidden declared booleans never written by the spec; (c) MEIP/SEIP constant 0; (d) full CLINT/PLIC MMIO | (b), reset false | MSIP is memory-mapped (P §3.1.9 p.44), consistent with [D67]; keeps external interrupts expressible for kernel-trap/S3K while trace-equal with sail (SIG disabled) | CLINT feeds MSI/MTI; SIG feeds MEI/SEI |
| D43 | `mtval`/`stval` contents (§4.2) | illegal instruction: instruction bits or 0; EBREAK: `pc` or 0; misaligned/access fault: address or 0 | instruction bits (16 or 32, zero-extended); `pc`; faulting address (fetch: parcel) | matches sail defaults; useful to handlers; all permitted (p.52–53) | all `xtval_nonzero.*` true |
| D44 | `mepc`/`sepc` storage and IALIGN masking (§4.1.5) | (a) store 63:1, mask bit 1 on read when `misa.C = 0`; (b) mask at write with current C (current L3); (c) truncate to PABITS | (a) | p.48 requires bit 1 to stay writable while masked; (b) violates it | (a) (`legalize_xepc`, `align_pc`) |
| D45 | LR reservation on trap entry/xRET (§4.6) | (a) keep; (b) clear on trap (current L3); (c) clear on xRET too | (a) | not required (p.61; U p.118); trace equality | no cancel on trap or xRET |
| D46 | SFENCE.VMA with Bare only (§4.7.7) | (a) decoded; NOP in M and S (TVM = 0); illegal in U and S (TVM = 1); (b) illegal everywhere (p.130) | (a), cfg `sfence_vma_illegal_if_svbare_only = false`. Kept by WP7 [S4], validated in S-mode; the reason becomes "no address-translation cache" (§4.7.7) | WP7 adds Sv39 without changing legality; plan WP2.4 | (b) |
| D47 | Number of PMP entries (§5.1) | 0, 16, 64, or 64 with 16 usable; spec constant or runtime parameter | 16, all usable, as one spec constant `PMP_COUNT ∈ {0,16,64}`; HOL instantiates 16 | sail default; S3K uses 8; fixed bound keeps the loop unrollable; 64 quadruples state; only 0/16/64 allowed (p.70) | 16 / 16 |
| D48 † | PMP grain G (§5.2.2) | (a) G = 0; (b) G = 1 (no partial matches for aligned ≤ 8-byte accesses); (c) larger | (a), with H4 in the M-mode contract | sail default, plan WP0.2, arch tests probe G and use NA4; no read-view masking; the HOL cost of (a) is one word conjunct (§1.5) | `grain = 0` |
| D49 † | `pmpcfg` write with R = 0, W = 1 (§5.2.3) | (a) R = W = X = 0, keep L and A; (b) R = W = 0 keep X (plan text); (c) ignore the byte; (d) R = W = 1; (e) fatal | (a); amend plan WP2.5 | matches sail exactly; least privilege; keeps W ⇒ R; only a legal value is required (p.71, p.58) | `PMP_ClearPermissions` |
| D50 | Supported A modes; NA4 with G ≥ 1 (§5.2.3) | each of TOR/NA4/NAPOT supported or not; NA4 with G ≥ 1 → OFF, keep old, or NAPOT | all four modes; NA4 with G ≥ 1 → OFF (never fires at G = 0) | S3K uses NAPOT; arch tests use all; NA4 "not selectable" with G ≥ 1 (p.73) | all supported; unsupported → OFF |
| D51 | Implemented physical address bits (§5.2.2) | 13 to 56 | 56: `pmpaddr[53:0]` writable | RV64 maximum of the PMP format (Figure 33 p.71); grain discovery reads `0x003F_FFFF_FFFF_FFFF` as in sail | 56 |
| D52 † | PMP storage (§5.2.2) | (a) raw images `pmpcfg0`, `pmpcfg2`, `pmpaddr0..15 :: regType` in `MachineCSR`; (b) 16 register-typed per-entry fields; (c) top-level maps | (a) | no new prog/CakeML component; lifts as `Imm64`; "no entry locked" is two word conjuncts; no function-typed record field (F7) | vectors of 64 entries |
| D53 † | `pmpCheck` interface (§5.4) | (a) `pmpCheck(pa, n, kind, p) -> bool`, caller picks 1/5/7; (b) returns `ExceptionType option` | (a) | PTE accesses (WP7) report the fault of the original access (P §12.3.2 p.134); simple side condition `pmpCheck(...) = T` | (b) |
| D54 | PMA map (§5.7) | (a) all 2^64 addresses main memory; (b) fault at ≥ 2^56; (c) sail-like regions | (a) | keeps `rawReadData`/`rawWriteData` and the lifter unchanged; PMP is the only fault source; divergence only outside sail's regions (open question 21) | regions; faults elsewhere |
| D55 | Misaligned loads/stores incl. F/D and compressed (§5.6) | (a) always 4/6 before translation and PMP; (b) 5/7; (c) support (Zicclsm); (d) support within a MAG | (a) | plan pins it; lifter asserts alignment; no splitting or partially visible stores; permitted (U p.37; P Table 17 p.51) | allowed (split); cfg must set `AlignmentException` |
| D56 | Misaligned AMO code (§5.6.4) | (a) 6; (b) 7 | (a) | both permitted (U p.120–121); exception mandatory without MAG (P p.67); current L3 raises 6 | AccessFault outside 16-byte MAG; cfg `amo = AlignmentException` |
| D57 | Misaligned LR/SC code (§5.6.4) | (a) 4 (LR) / 6 (SC); (b) 5 / 7 | (a); fix L3 LR raising 6 | one uniform rule; both permitted (U p.116); LR is a load | `lrsc = AccessFault`; cfg changed |
| D58 | Misaligned atomicity granule (§5.7) | (a) none; (b) MAGn | (a) | any MAG forbids misaligned exceptions within it (P §3.6.4 p.67), contradicting D55–D57 | RAM MAG 2^4; cfg sets 0 |
| D59 | Fetch PMP granularity (§5.6.3) | (a) per 16-bit parcel; (b) one 4-byte check at 4-aligned PC (sail Ziccif) | (a) | existing `Fetch()` structure; precise `mtval` (p.52); identical verdicts because bounds are multiples of 4; must be mirrored in `riscv_step$Fetch_def` | (b) |
| D60 | SC with failing reservation: PMP checked? (§5.6.3) | (a) check alignment and PMP first; (b) fail without checks (current L3) | (a) | p.72: SC to a non-writable PMP region raises a store access fault; matches sail | (a) (`sys/vmem_utils.sail:358-371`) |
| D61 | CSRs of unimplemented PMP entries (§5.2.2) | (a) illegal; (b) RO0 | (a) (odd `pmpcfg` illegal regardless) | entries ≥ 16 are not part of the hart; matches sail and plan Appendix A | (a) |
| D62 | PMP reset of unspecified fields (§5.8) | (a) all 0; (b) only A, L cleared | (a) | legal and deterministic; step library needs only L = 0 | clears A, L only (others expected 0) |
| D63 | Tick rate of `mcycle` and `mtime` (§6.5) | (a) one per step incl. trap/interrupt steps; (b) sail default 2 with a hidden phase counter; (c) other ratio (today 200) | (a), cfg `instructions_per_tick = 1` | rate is implementation-defined (U §4.3 p.66); simplest theorems; `mtime` = step count | 2 |
| D64 | What increments `minstret` (§6.5) | mandated: exceptions, ECALL, EBREAK do not; xRET does; choices: WFI, interrupt steps | NOP WFI counts; interrupt steps do not; SC failure counts | sail's `retired` definition; requires interrupt entry as its own step ([D38]) | same |
| D65 | Explicit counter write vs increment (§6.5) | `minstret`: write wins (mandated, U p.64); `mcycle`: (a) write then tick (next read `v+1`); (b) suppress tick | `minstret_written` flag; `mcycle` (a) | (a) reproduces sail at one tick per step without a second flag | no `mcycle` suppression |
| D66 | When `mcountinhibit` takes effect (§6.5) | (a) IR sampled before, CY after execution; (b) both before; (c) both after | (a) | IR per P §3.1.10 p.46; CY as sail; only observable via traces | (a) |
| D67 † | `mtime`/`mtimecmp`/`msip` representation (§6.6) | (A) declared state plus MMIO dispatch reproducing sail CLINT faults; (B) memory-backed words of `MEM8` at the CLINT addresses, MTIP/MSIP computed from memory, harness increments `mtime` | (B), through `mtime()`/`mtimecmp(h)`/`msip(h)` helpers so (A) can be swapped in | registers must be memory-mapped (P §3.2.1 p.59); (B) changes no load/store semantics and adds no `inCLINT` split; S3K uses plain `ld`/`sd`; `time` reads may become loads (p.47) | (A)-style CLINT at `0x2000000`, exact widths, IO PMA |
| D68 † | `mcycle`/`minstret` storage (§6.2) | (a) top-level `c_cycles`/`c_instret`; (b) `MachineCSR` fields | (a) | already hidden in prog; `Next` need not write `c_MCSR` every step | registers |
| D69 | `mtime`/`mtimecmp` reset (§6.7) | (a) 0, so MTIP = 1 from reset; (b) `mtimecmp` all ones | (a), harness zeroes the CLINT memory | matches sail so `csrr mip` traces agree; harmless until MTIE and enables are set | 0 (MTI pending at first step) |
| D70 | `mstatus` reset of unspecified fields (§6.7) | (a) all 0 except UXL = SXL = 2 (FS = Off, MPP = U); (b) FS = Initial (current L3); (c) unspecified | (a): read value `0x0000_000A_0000_0000` | identical to sail's initialiser; tests and S3K set FS before FP use; no illegal WARL value (P §3.4 p.63) | (a) |
| D71 | Other unspecified reset values (§6.7) | (a) 0 for everything not mandated; (b) free variables | (a), incl. `mtvec = stvec = 0` Direct, `medeleg = mideleg = 0`, all scratch/epc/tval/cause/counteren/envcfg/`satp` 0 | deterministic trace comparison; `medeleg = mideleg = 0` ensures M/U software never sees delegation | zero-initialised; `reset_tvecs` Direct |
| D72 | Boot GPRs (§6.7) | (a) harness sets `x10 = mhartid`, `x11 = 0x1000`; (b) leave 0 | (a), in the harness, not the spec | sail always runs `init_boot_requirements`; a boot convention, not architectural reset | `a0 = 0`, `a1 = 0x1000` |
| D73 | sail `simple_interrupt_generator` (§6.6.3) | (a) disable; (b) model it | (a) | no interrupt controller modelled; a stray store to `0x0C000000` would otherwise raise interrupts in sail only | enabled at `0x0C000000` |

**Count: 73 decision items.**

---

## 8. Open questions

1. **PMP entry count as a parameter.** The design fixes `PMP_COUNT = 16` as one named spec constant ([D47]) with the HOL theory instantiated at 16, and G = 0 likewise. Should either be exported to HOL as a parameter instead (plan §5's first question)?
2. **S3K's PMP configuration.** The H4 conjunct (every entry OFF or NAPOT) must hold whenever S3K's M-mode kernel performs 8-byte accesses, i.e. after `trap_resume` loads per-process `pmpcfg0` values from memory. Confirm that S3K never configures NA4 or TOR entries. If it does, H4 must be replaced by a 16-entry "coarse regions" predicate, or G = 1 reconsidered ([D48]), with sail `memory.pmp.grain` and the arch-test PMP YAML matching.
3. **HolBA asserts per instruction.** Every lifted step theorem carries H1, H3, H4 as BIR asserts, because MRET and `csrw pmpcfg0` change them and `bmr_extra` must be preserved (F4). Is one assert per instruction acceptable, or does the lifter need hoisting/merging of repeated asserts or a per-program case condition?
4. **Counters in `NextRISCV`.** `NextRISCV` does not update `mcycle`/`minstret`/`mtime`, so CSR reads of `cycle`/`instret` in lifted or CakeML code see values that differ from `Next`. Unchanged by this rewrite, but more visible once counteren-gated counters are lifted. Model them in WP3, or exclude counter reads from verified code?
5. **CakeML contract.** Is requiring `c_privilege = 3w`, `¬mstatus.MPRV`, no locked PMP entry, every entry OFF or NAPOT, and `¬mstatus.MIE` in `riscv_ok`/`riscv_proj` acceptable to CakeML, whose RISC-V target was never tied to a privilege mode?
6. **FS = Off at reset.** With FS = Off ([D70]) and the new FS check, any consumer (CakeML backend, HOL step selftests, HolBA examples) that runs F/D instructions or touches `fflags`/`frm`/`fcsr` from a state where software has not set FS needs an `FS ≠ 0` hypothesis or harness setup. Does any consumer do so?
7. **MPRV in U-mode theorems.** [D22] adds an `MPRV = 0` hypothesis (or case split) to U-mode load/store step theorems. Acceptable for HolBA's S3K lifting, or should the spec use the M-mode-only form, which equals the literal rule only under the reachable-state invariant?
8. **Delegation writable now?** `medeleg`/`mideleg` writable with masks `0xB3FF`/`0x222` ([D40], [D41]) makes the S trap path reachable but unvalidated. If the `medeleg` case split costs too much in U-mode exception theorems (S3K `ecall`), make both RO0 until WP7 (a constant change).
9. **No-interrupt hypothesis in U mode.** Every U-mode step theorem needs `SelectInterrupt() = None` (M-level interrupts are enabled in U regardless of MIE). Can HolBA take this as a global assumption (e.g. `mie = 0` or platform inputs false in lifted code), or must interrupt steps be lifted?
10. **fflags dirty policy.** [D17] depends on WP1: L3 currently accrues only NV on compares, and `setFP_Underflow`/`setFP_Inexact` set OF. When WP1 adds flag accrual as a single OR, decide whether to keep `Fflags_Dirty_Flag` or move both L3 and sail to `Precise`.
11. **Writable `misa.C`.** Is dynamic C needed by HolBA/S3K, or would a build-time choice suffice? Read-only C removes the `pc<1>` suppression and the read-side `xepc` masking.
12. **Leaving validated scope; S-mode WFI.** Should the harness flag any entry into S (MRET with `MPP = S`, SRET from M, delegated traps) so later trace differences are not counted as regressions? Before WP7 validates S, settle WFI in S with TW = 1: this design traps, sail with `wfi_is_nop = true` retires it. *Closed by WP7*: there is no such flag ([S26]): S-mode is validated, so a divergence after an entry into S is a regression or an expected outcome recorded in `sim/tests/corpus.expected`. WFI in S with TW = 1 traps iff no interrupt is pending and enabled in `mie`, which sail reproduces with `wfi_is_nop = false` and `max_time_to_wait = 0` ([S20], §4.7.6).
13. **HolBA and the timer.** Under [D67] `mtime` at `0x200bff8` and `rdtime` are ordinary memory reads that the lifter treats as constant within a fragment, while real `mtime` advances. Should HolBA mark the CLINT addresses volatile, or exclude S3K's timer functions from the verified set? Is "unconstrained memory read" the intended treatment of `time` (plan open question)?
14. **Illegal-instruction `mtval` plumbing.** `setTrap` needs the faulting instruction bits ([D43]). Take them from `Delta.rinstr` (in hidden `c_update`) or a new field? This affects which definitions the `NextRISCV_Half_noC` proof needs.
15. **sail config overlay.** Does the JSON overlay merge partial `base`, `platform` and `memory` objects with the defaults? §6.10 assumes so.
16. **sail zero-initialisation.** Confirm on the first WP0 trace that the C emulator zero-initialises registers without an initialiser (`mcounteren`, `scounteren`, `satp`, `mscratch`, `mtval`, PMP R/W/X and `pmpaddr`, CLINT `mtimecmp`). [D62], [D69]–[D71] assume it.
17. **L3 function-typed record fields.** Does L3-2018-02-09 accept a field such as `pmpaddr :: bits(4) -> regType` inside a record? Not needed for 16 named fields ([D52]), but relevant if 64 entries are ever wanted.
18. **WP4 base branch.** Port the new model onto HolBA `riscv_lifter` (C, fences, atomics) first, or onto `master`?
19. **`mcause` legal set.** [D33] mirrors sail (accepting 19 and the page-fault codes) for trace equality. Confirm this is preferred over the minimal set of codes the hart raises.
20. **Trace format.** Confirm `csrName` prints the 12-bit hex for absent CSRs (sail's fallback) and that the harness's step counter replaces `c_instret` in `log_instruction`.
21. **Physical addresses ≥ 2^56.** Should the model access-fault there (the RV64 PMP address width) to narrow the gap to sail, or keep all 2^64 addresses as main memory ([D54])?
22. **SUM read-only zero.** Confirm that no S3K or HolBA code expects to read back `mstatus.SUM = 1` (plan Appendix A lists `satp` as WARL storage, which forces SUM RO0). *Closed by WP7* ([S19], `design-smode.md` §2.1): SUM must be read-only zero exactly while `satp.MODE` is (p.35, p.114), so it becomes writable in WP7 stage 2, in the commit that makes Sv39 legal, and stays read-only zero until then. S3K does not depend on it: its only `mstatus` access is `csrw mstatus, zero` at `_start`, and it runs no code in S-mode. HolBA gets the SUM field theorems in WP7 stage 4 (`design-smode.md` §1.6).
23. **Plan amendments.** Approve the corrections this design makes to the plan: WP2.4 (SRET legal in M whatever TSR, R11); WP2.5 (R = W = X = 0, R13; effective-privilege wording [D22]); WP3 (M-mode PMP hypothesis, R12 and §1.5); WP2.2 and Appendix A (`hpmcounter3–31` illegal, `menvcfg.FIOM` writable, `mconfigptr` present, `pmpcfg4..14`/`pmpaddr16..63` illegal, `mtime`/`mtimecmp` memory-backed rather than harness-set state, R5, R14).
