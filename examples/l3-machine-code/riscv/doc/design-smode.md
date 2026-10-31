# S-mode and virtual-memory design for the L3 RISC-V model (WP7: priv 1.13 S-mode, Sv39/Sv48/Sv57)

## 0. Scope and conventions

**Scope.** This document is the WP7 design for the L3 RISC-V model `src/riscv.spec`. The baseline is
branch `riscv-l3` at `37a5d7e9a` (tag `riscv-l3-before-smode`): priv 1.13 M+U with PMP and RV64GC. In
the baseline, S-mode CSRs exist as storage, S-mode trap entry and SRET exist but are unvalidated, and
`satp` accepts only Bare, so `translateAddr` is the identity. WP7 does two things:

- **Validates S-mode as an executing mode**: the S-level CSR views, delegation, S-level interrupts,
  trap entry, SRET, WFI, ECALL, SFENCE.VMA, counter gating, and MPRV with MPP = S/U.
- **Adds supervisor address translation**: `satp` with Sv39, Sv48 and Sv57, the 1.13 PTE format, the
  page-table walk, page faults 12/13/15, and PMP on PTE reads.

The validation oracle is sail-riscv together with the riscv-tests paging suites. The target hart is
RV64 only, with M/S/U, no H, and 16 PMP entries with G = 0. It has no TLB, uses the Svade A/D scheme,
and has none of Svnapot, Svpbmt, Svinval, Svrsw60t59b or Svukte.

Every function on the step-theorem path must be total and must only read state. Translation must be
the identity, with **no new hypothesis**, for code that runs at M with `MPRV = 0`; that is the
existing contract H1 ∧ H2. Out of scope:

- two-stage (VS/G) translation;
- Zicfiss shadow stacks (step 7 of §12.3.2);
- pointer masking;
- a TLB;
- lifting S-mode or U-mode code in HolBA.

This document extends `design-privileged.md` and keeps its conventions (§0 there).

- **P §x p.N**: privileged spec 20260120, `~/Documents/RISC-V specs/riscv-privileged.pdf`, by
  **printed** page (PDF page = printed + 7).
- **sail**: `~/Documents/riscv-tools/sail-riscv/model/…` at tag `2026-10-26-6f886e6`.
- **cfg**: the oracle override `~/Documents/riscv-tools/rv64gc_mu_pmp.json`.
- **L3 n**: line n of `riscv.spec` at `37a5d7e9a`.
- **[Dn]**: a decision of `design-privileged.md` §7.
- **[Sn]**: a decision of this document (§5).
- **F1–F3**: the consumer rules of `design-privileged.md` §1.3. F1: mirror definitions in
  `riscv_stepScript` follow the spec. F2: total functions with no `#UNDEFINED` on the step path.
  F3: hidden components in `prog`.
- **H1–H6**: the step-theorem contract (`design-privileged.md` §1.5).
  - H1: `c_privilege = 3w`.
  - H2: `¬mstatus.MPRV`.
  - H3: PMP unlocked.
  - H4: PMP off or NAPOT.
  - H6: interrupts quiet.

Four area reports are merged here: translation, S-mode execution, sail and corpus, and consumers.
Their scratch files are under `~/Documents/riscv-tools/work/design-smode/` (`translation/`,
`smode-exec/`, `sail-oracle/`). Where the reports disagreed, the text below states the resolution and
names the section that decides it. §5.1 collects these resolutions.

---

## 1. Consumer constraints and the M-mode identity lemma

### 1.1 Spec basis: there is no translation in M-mode under H1 ∧ H2

| Rule | Source |
|---|---|
| "The satp CSR is considered *active* when the effective privilege mode is S-mode or U-mode. Executions of the address-translation algorithm may only begin using a given value of satp when satp is active." | P §12.1.11 p.126 |
| Walk step 1: "The satp register must be active, i.e., the effective privilege mode must be S-mode or U-mode." | P §12.3.2 p.134 |
| "When MPRV=1, load and store memory addresses are translated and protected … as though the current privilege mode were set to MPP. Instruction address-translation and protection are unaffected by the setting of MPRV." | P §3.1.6.4 p.35 |
| Page-table accesses are implicit, have effective privilege S, and happen only inside a walk | P §3.7.1 p.70, §3.7.2 p.74 |
| sail: `satp_mode(priv)` returns Bare when `priv == Machine` (`sys/vmem.sail:315-317`); `translateAddr(gva, access, p)` takes the privilege as a parameter (`vmem.sail:697`); `effectivePrivilege` (`sys/sys_control.sail:11-15`) | sail |

Consequences:

- **Fetch** uses `curPrivilege()`. Under H1 this is M, so fetches are never translated, whatever
  `satp` and MPRV hold.
- **Explicit data accesses** use `effectivePrivilege() = MPRV ? privilege(MPP) : curPrivilege()`
  ([D22]). Under H1 ∧ H2 this is M.
- **PTE reads** never happen at M. `pmpCheck_Machine` is therefore unchanged.

**M-mode step theorems gain no `satp` hypothesis.** In particular there is no hypothesis "H7"
`satp.MODE = 0` on the M-mode path.

### 1.2 Interface contract of `translateAddr` (decisions [S1], [S2], [S3], [S5], [S6])

1. **The privilege is an explicit parameter and is tested first** [S1]:
   `TransResult translateAddr(va::vAddr, ft::fetchType, ac::accessType, p::Privilege)`.
   - The body begins `if p == Machine then TR_Address(va) else …`, before any read of `SCSR.satp`,
     `MCSR.mstatus` or `MEM`.
   - With Bare it also returns `TR_Address(va)`.
   - `fetchAddr` computes `p = curPrivilege()` and `dataAddr` computes `p = effectivePrivilege()`.
     Each computes it once and passes the same value to `translateAddr` and to `pmpCheck`, so the
     two can never disagree.
2. **One result type carries the fault code** [S2]:
   `construct TransResult { TR_Address :: pAddr, TR_Fault :: ExceptionType }`.
   It is used by `translateAddr`, `fetchAddr` and `dataAddr`. The constructors `Fetch_PageFault`,
   `Load_PageFault` and `Store_AMO_PageFault` already exist (L3 226-228). The walk keeps the
   distinction between page faults and access faults internally (§3.11), and `translateAddr` maps it
   to a code (Table 16 p.50):

   | Access (`ft`, `ac`) | PMP failure, on a PTE or on the final PA | Page fault |
   |---|---|---|
   | fetch (`Instruction`, `Read`) | 1 `Fetch_Fault` | 12 `Fetch_PageFault` |
   | load, LR, FP load (`Data`, `Read`) | 5 `Load_Fault` | 13 `Load_PageFault` |
   | store, SC, AMO, FP store (`Data`, `Write`) | 7 `Store_AMO_Fault` | 15 `Store_AMO_PageFault` |

3. **Only reads state in the HOL export** [S3], [S6] (F2). `translateAddr` and everything it calls
   make no assignment, call no `mark_log`, and contain no `#UNDEFINED`. The HOL definition is then
   `translateAddr (a,ft,ac,p) s = r`, the same shape as today's `fetchAddr a s` and
   `dataAddr (a,n,k) s` (`riscv_stepScript.sml:375-398`). Concretely:
   - PTEs are read through the `MEM` component, not `rawReadData` (which logs, L3 1687);
   - A/D bits follow Svade, so the walk never writes;
   - the walk is unrolled ([S5]), so it needs no `measure` recursion.

   If any of these rules is broken, `fetchAddr` and `dataAddr` return `(r, s')`, and then
   `Fetch_def`, the M-mode lemmas and about 37 instruction evaluations all have to thread state.

### 1.3 Lemmas (`step/riscv_stepScript.sml`)

| Lemma | Statement | Proof |
|---|---|---|
| `translateAddr_Machine` (new) | `translateAddr (a, ft, ac, Machine) s = TR_Address a`, **no hypotheses** | `rw [translateAddr_def]` |
| `effectivePrivilege_Machine` (new) | H1 ∧ H2 ⇒ `effectivePrivilege () s = Machine` | `rw [effectivePrivilege_def, curPrivilege_def, privilege_def]` |
| `fetchAddr_Machine` (`:375-383`) | the existing hypotheses (H1, H3, alignment) ⇒ `fetchAddr a s = TR_Address a` | `rw [fetchAddr_def, translateAddr_Machine, curPrivilege_def, privilege_def]` plus `pmpCheck_Machine` |
| `dataAddr_Machine` (`:387-398`) | the existing hypotheses (H1, H2, H3, plus H4 for n = 8) ⇒ `dataAddr (a,n,kind) s = TR_Address a` | the same, plus `effectivePrivilege_Machine` |
| `translateAddr_Bare` (new, not used by `prog` in WP7) | `(63 >< 60) (s.c_SCSR s.procID).satp = (0w:word4) ⇒ translateAddr (a, ft, ac, p) s = TR_Address a` | `rw [translateAddr_def]`, then a case split on `p` |

`translateAddr_Bare` is the lemma that a future U-mode or S-mode step theorem would use (§1.9). WP7
proves it to show that the Bare case is cheap. It does **not** add H7 to `contract_hyps`.

*Stage 3 notes.* The five statements are as above. Three proofs differ from the last column:

- `fetchAddr_Machine` and `dataAddr_Machine` first prove `pmpCheck (a, n, kind, Machine) s` with
  `pmpCheck_Machine` (and, for `dataAddr`, `effectivePrivilege () s = Machine` with
  `effectivePrivilege_Machine`), and then simplify. `rw` as written splits the conditional
  `if pmpCheck … then TR_Address a else TR_Fault …` into cases and leaves a goal that
  `pmpCheck_Machine` does not match. The old proof had no such split, because the simplifier turns
  `(if b then SOME x else NONE) = SOME y` into `b ∧ x = y`, and `TransResult` has no such rewrite.
- `effectivePrivilege_Machine` also needs `MCSR_def`, since `effectivePrivilege` reads
  `(MCSR state).mstatus.MPRV`.
- `translateAddr_Bare` is `rw [translateAddr_def, SCSR_def]`; `rw` splits on `p = Machine` itself.

### 1.4 Step-library changes

| Location | Today | WP7 |
|---|---|---|
| `riscv_stepScript.sml:71-89` `Fetch_def` | `case fetchAddr pc s of NONE => raise'exception (UNDEFINED "fetch fault") s \| SOME ppc => …`, twice | Same structure; only the patterns change, to `TR_Fault _` and `TR_Address ppc`. It still mirrors the two-parcel fetch ([D59]); F1 |
| `:121-141` `NextRISCV_def` | `SOME Sret => NONE` | unchanged: S-mode stays outside the step theorems |
| `:146-151` H1-H6 comment | | add: "translation is off at M (P §12.1.11 p.126, §3.1.6.4 p.35), so H1 (fetch) and H1 ∧ H2 (data) make it the identity" |
| `:375-398` `fetchAddr_Machine`, `dataAddr_Machine` | proved from `translateAddr_def` | proved as in §1.3; `SOME a` becomes `TR_Address a`; hypotheses unchanged |
| `:1235-1237` ``EV [translateAddr_def] … ``translateAddr (vPC, ft, ac)`` `` | evaluates the identity | **delete** (wrong arity; symbolic evaluation of the walk); add `translateAddr_Machine` to the list `l` at `:1704-1707` |
| `:1276-1283` `fetchAddr` uprove, `:1437-1459` `dataAddr1/2/4/8` | `… ==> (fetchAddr a s = SOME a)` | `SOME a` becomes `TR_Address a`; hypotheses `h1`-`h4` unchanged |
| `:1191-1192` `datatype_rwts` | `["riscv_state","Architecture","Privilege","pmpAccess","ExtStatus"]` | add `"TransResult"` |
| `:1735-1738` `bad` | `signalAddressException … dataAddr fetchAddr …` | add `translateAddr`, `effectivePrivilege`, `ptwLevel`, `ptwStep`, `ptePermits` |
| `:488`, `:556`, `:600`, `:413` (`mret_eval`, `NextRISCV_mret`, `NextRISCV_trap`, `checkInterrupts_Machine`) | | `mstatus` gains a field `SUM` ([S19]); these proofs use `with` updates and should still go through |
| `:2047-2051` `SFENCE_VMA` | a no-op at M | unchanged ([S4]) |
| `riscv_stepLib.sml:422-431` `contract_hyps` | H1, H2, H6, H3, H4 | **unchanged** |
| `riscv_stepLib.sml:661-675` `csr_defs` | includes `legalize_satp_def` | unchanged as a list; the `csrw satp` theorem picks up the new legaliser (§3.2.3). `check_CSR_conditions` for 0x180 is `T` under H1 |
| `riscv_stepLib.sml:766-783` trap/`excDest` | H1 decides "not delegated" | unchanged |

*Stage 3 notes.*

1. Besides the five names added to `bad`, the step script's `check` also rejects an instruction
   theorem that has a hypothesis mentioning `c_SCSR`, by its selector or its update. So the
   hypothesis check of §1.8 also holds at build time, for every theorem stored in
   `riscv_stepTheory`.
2. Comments are reworded where WP7 made them wrong:
   - `Fetch_def`: a parcel can also fail in translation.
   - `NextRISCV_def`: SRET gives `NONE` because S-mode and U-mode code are outside the step theorems
     by design, no longer because S-mode is unvalidated.
   - The H1-H6 block.
   - The comments "translateAddr is the identity" (`:374`) and "satp.MODE is Bare" (`:1235`) are
     gone with the lemma and the EV they described.
3. Printed under `trindemossen-2`, every theorem of `riscv_stepTheory` is textually identical to
   stage 1's, except `Fetch_def` (the patterns), `fetchAddr_Machine` and `dataAddr_Machine`
   (`TR_Address a`), and the three new lemmas. So the new `SUM` field of `mstatus` changes no proof
   and no theorem, as the row for `mret_eval` and the others expected. `contract_hyps` and the rest
   of `riscv_stepLib.sml` are unchanged.

### 1.5 `prog` (`prog/riscv_progScript.sml`, `riscv_progLib.sml`)

- **`c_SCSR` stays hidden** (hide list `riscv_progScript.sml:22-26`), and `riscv_ID` (`:79-85`) is
  unchanged [S28]. This is sound because no M-mode step theorem mentions `c_SCSR`. The `p == Machine`
  test comes first, and the M-mode lemmas rewrite `fetchAddr`/`dataAddr` before `translateAddr` is
  unfolded. The selftest enforces this (§1.8).
- `riscv_progLib` gives no specs for CSR instructions (`:482-487`), so `csrw satp` never reaches
  `prog`.
- Any new top-level `declare` added in WP7 must go into the hide list (F3). The design adds none,
  because there is no TLB and no PTE log.

*Stage 3 note.* The hide list and `riscv_ID` are unchanged. One change was needed in
`riscv_progLib.sml`, unrelated to translation. It did not build under `trindemossen-2`, which §7
requires: `riscv_spec` recognised the step library's error for a CSR instruction with
`Feedback.message_of`, which only HOL develop has (since commit `8f8ab4f20`, WP4). It now looks for
the message in `Feedback.exn_to_string` of the exception, which both versions have. Under both,
`riscv_spec_hex` gives every CSR instruction tried, `csrw satp,t0`, `csrwi satp,0` and
`csrw sstatus,t0` among them, the error "CSR instructions, ECALL, EBREAK and MRET are not
supported". For the other instructions tried (loads, stores, an AMO, ADDI, WFI and SFENCE.VMA) the
two versions give the same specs.

### 1.6 HolBA (`~/Documents/HolBA-priv113`, branch `riscv_priv113`)

- **`riscv_state_is_OK`** (`src/theory/tools/lifter/bir_lifting_machinesScript.sml:938-960`):
  **nothing new**. In particular it gets no `satp.MODE = Bare` conjunct, because a lifted
  `csrw satp` could falsify it [S29].
- **Lift `satp` as a plain 64-bit variable with no assertion** [S29]. Add one `BMLI` entry after
  `scounteren` in `riscv_sysregs_lifted_imms_LIST` (`:1005-1043`):
  `BMLI (BVar "satp" (BType_Imm Bit64)) (\ms. Imm64 ((ms.c_SCSR ms.procID).satp))`.
  - Why: an M-mode kernel's PMP-isolation argument (S3K; `examples/riscv/kernel/kernel.da:25`
    `csrwi satp,0`) needs "satp is Bare at `mret` to U" once U code can run translated. Lifting
    `satp` lets that be stated as a BIR postcondition.
  - Cost:
    - `csrw satp, rs` lifts to `satp := legalize(rs, satp)`. This is why `legalize_satp` is written
      as a mask comparison (§3.2.3), which `riscv_csr_conv`
      (`src/tools/lifter/bir_lifting_machinesLib_instances.sml:700-916`) can translate.
    - The `SupervisorCSR` field updates are already in `value_convs` (`:717-723`).
    - `riscv_bmr_rel_EVAL` (`bir_riscv_backlifterScript.sml`) gains one conjunct; its proofs
      (`:88-104`) are unaffected.
- **`mstatus.SUM`**: add `(!w. (rec'mstatus w).SUM = word_bit 18 w)` and
  `(!r. r.SUM = word_bit 18 (reg'mstatus r))` to `riscv_csr_rec_fields`/`riscv_csr_reg_fields`
  (`src/theory/tools/lifter/bir_riscv_extrasScript.sml:893-905`, `:929-941`). S3K writes `mstatus`.
- `src/tools/lifter/selftest_riscv.sml`: add `csrw satp,t0` and `csrwi satp,0`.
- `examples/riscv/README.md`:
  - `:39`: "S-mode and Sv39/Sv48/Sv57 in the model; the lifter lifts M-mode code, where translation
    is off".
  - Move `satp` into the list of lifted CSRs (`:60-63` → `:72-78`).
  - The assertion table (`:99-107`) is unchanged.
- Re-vendor `src/shared/l3-machine-code/riscv` (`VENDORING.md`).

### 1.7 CakeML

`riscv_ok` (`compiler/encoders/riscv/riscv_targetScript.sml:19-25`) is still on the 1.7 state. WP6
replaces it with `misa.MXL = 2w`, H1, H2, H3, H4, H6 and the fetch conjuncts, and `riscv_proj`
(`:287-296`) then projects `c_privilege` and the `c_MCSR` fields those read.

**WP7 adds nothing to either**: no `satp` conjunct, and `c_SCSR` stays out of `riscv_proj`. The only
knock-on effect is the `mstatus` record gaining `SUM`, which the `UPDATE_APPLY` closure in
`proofs/riscv_targetProofScript.sml` handles. Coordinate the timing with WP6 (§6, Q14).

### 1.8 Selftest (`step/selftest.sml`) as the regression guard

- **The `exact` hypothesis table (`:131-145`) stays unchanged.** The categorisation is exhaustive, so
  any hypothesis on `c_SCSR` or `satp` shows up as `UNEXPECTED`. Say so in the header comment
  (`:11-25`).
- `bad_consts` (`:412-425`): add `translateAddr`, `effectivePrivilege`, `ptwLevel`, `ptwStep` and
  `ptePermits`.
- Edge cases (`:518-`):
  - `csrrs ra,mstatus,zero` (`:585-587`): the mask becomes `0x7E79AAw`.
  - New `"18029073"` `csrw satp,t0`:
    `satp' = if (t0 && 0xF000000000000000w) ∈ {0w, 0x8…w, 0x9…w, 0xA…w} then t0 else satp`.
  - New `"18005073"` `csrwi satp,0` gives `satp' = 0w`.
  - New `"12000073"` `sfence.vma`: `next_pc 4`, `same_mcsr`, `same_regs`.
  - New `csrw sstatus,t0`, which writes SUM.
  - `"10200073"` `sret` must still fail.
- New check: `find_term (same_const ``riscv_state_c_SCSR``)` over the hypotheses of every theorem
  must find nothing. Conclusions may mention `c_SCSR` only for S-mode CSR writes.

*Stage 3 notes.*

1. **The constant.** In HOL develop the selector of `c_SCSR` is the constant
   `recordtype.riscv_state.seldef.c_SCSR`, which only prints as `riscv_state_c_SCSR`. So the
   test takes the constants from the terms ``s.c_SCSR`` and ``s with c_SCSR := f``. That way it
   also catches an update of `c_SCSR`, and it works under both HOL versions.
2. **Reads too.** The conclusion rule has to allow S-mode CSR reads as well as writes: a read
   such as `csrr a0,satp` puts the stored value, a field of `c_SCSR`, into `rd`. The test allows
   `c_SCSR` in a conclusion only for a CSR instruction on one of the eight CSRs stored there:
   `stvec`, `scounteren`, `senvcfg`, `sscratch`, `sepc`, `scause`, `stval` and `satp`.
   `sstatus`, `sie` and `sip` are views of `c_MCSR`.
3. **Edge cases beyond the list.**
   - `csrr a0,satp`: the value stored.
   - `csrr a0,sstatus`: the read through `SSTATUS_MASK`, which shows SUM.
   - A SUM check in `csrw mstatus,t0`.
   - `csrw sstatus,t0` checks all thirteen fields: SIE, SPIE, SPP, FS, SUM and MXR are taken from
     `t0`; MIE, MPIE, MPRV, TVM, TW and TSR keep their bits of the stored word; MPP keeps its
     bits, with 2 stored as 0.
   - `sfence.vma` also checks that `c_SCSR` and the privilege are unchanged.
4. **More programs.** The selftest's list of `sim/tests` encodings now also has those of
   `smode.S`, `sv39.S`, `sv48.S` and `sv57.S`: 971 more, 1952 in all. They are regenerated by the
   procedure that its comment gives, and that procedure also reproduces the old list exactly. So
   the header's claim that the list holds every instruction of those programs is true again.
5. **Result.** Under develop and under `trindemossen-2`:
   - every check passes, with no `UNEXPECTED` hypothesis;
   - SRET has no theorem;
   - 58 theorems have `c_SCSR` in the conclusion, and none in a hypothesis;
   - each class of instruction has the same set of hypothesis shapes as in stage 1, so the new
     theorems only add to the counts;
   - the selftest takes 422 s under develop and 456 s under `trindemossen-2`, against 315 s in
     stage 1.

### 1.9 Outside WP7: what S/U-mode lifting would need

1. Step theorems for S/U code. The cheap route is the class H7 = `translateAddr_Bare`'s hypothesis
   over a lifted `satp`. Full paging needs the walk as three to five dependent `MEM8` loads plus the
   permission checks in BIR, or an abstract translation map with assertions.
2. PMP as a BIR assertion over `pmpcfg*`/`pmpaddr*`, or a single-region hypothesis.
3. `NextRISCV` support for SRET, traps delegated to S, and S-level interrupts. This lifts `stvec`,
   `sepc`, `scause`, `stval`, `sscratch`, `medeleg` and `mideleg`.
4. Page faults: assert that none occurs, or lift them as jumps to `stvec` or `mtvec`.
5. Page-table writes need disjointness assertions, because there is no TLB.

---

## 2. S-mode execution

Almost all of WP2's S-mode code already matches 1.13 and sail. §4.7 lists that code; the changes are
E1–E4 below.

| Change | Where (L3 n) | What | Stage |
|---|---|---|---|
| E1 | `register mstatus` 296-309; `MSTATUS_WMASK` 440; comment 459-463 | add `18 : SUM`; mask `0x7A79AA` becomes `0x7E79AA` ([S19]) | **2**, together with `legalize_satp` (§2.1) |
| E2 | WFI 4305-4311 | S-mode TW = 1 traps only if no locally enabled interrupt is pending ([S20]) | 1 |
| E3 | SFENCE.VMA comment 4385-4389 | "no address-translation cache, so the fence has nothing to do (P §12.2.1 p.128)" | 1 |
| E4 | `translateAddr`/`fetchAddr`/`dataAddr`, the 37 call sites, `Fetch` | §1.2, §3.11 ([S1], [S2]) | 2 |

### 2.1 `sstatus` (0x100, SRW) (P §12.1.1 p.113-116, Figure 50; P §3.1.6 p.31-37)

`sstatus` is not stored separately. "Reading or writing any field in sstatus is equivalent to reading
or writing the homonymous field in mstatus" (p.114).

| Bits | Field | WP7 | Writable via `sstatus` | Cite |
|---|---|---|---|---|
| 1 | SIE | RW | yes | p.113 |
| 5 | SPIE | RW | yes | p.114 |
| 6 | UBE | RO0 (little-endian only) | no | p.115, p.36 |
| 8 | SPP | RW (0 = U, 1 = S) | yes | p.113 |
| 10:9 | VS | RO0 ([D18]) | no | p.38 |
| 14:13 | FS | WARL, four states ([D16]) | yes | p.38 |
| 16:15 | XS | RO0 | no | p.38 |
| 18 | **SUM** | **RW from stage 2** | **yes** | p.114, p.35 |
| 19 | MXR | RW (already) | yes | p.114, p.35 |
| 23 | SPELP | RO0 (no Zicfilp) | no | p.115 |
| 24 | SDT | RO0 (no Ssdbltrp) | no | p.115 |
| 33:32 | UXL | read-only 2 | no | p.114, p.34 |
| 63 | SD | read-only: `FS = 11` (XS = VS = 0) | no | p.40 |
| other | WPRI | RO0 | no | p.113 |

**SUM timing (resolution R15).** "SUM is read-only 0 if S-mode is not supported or if satp.MODE is
read-only 0" (P §3.1.6.4 p.35; again in §12.1.1.2 p.114). This is a mandate in both directions:

- SUM must stay RO0 while `legalize_satp` accepts only Bare;
- SUM must become writable in the **same commit** that makes Sv39 legal.

The cfg must flip `Sv39.supported` in that same stage, because sail derives
`SUM = if virtual_memory_supported() then v[SUM] else 0` (`core/sys_regs.sail:268`). E1 therefore
belongs to stage 2, not stage 1.

Constants (RV64):
```
MSTATUS_WMASK = 0x0000_0000_007E_79AA  -- SIE MIE SPIE MPIE SPP MPP FS MPRV SUM MXR TVM TW TSR
SSTATUS_RMASK = 0x8000_0003_018D_E762  -- unchanged (L3 SSTATUS_MASK, 464)
SSTATUS_WMASK = SSTATUS_RMASK && MSTATUS_WMASK = 0x0000_0000_000C_6122   -- SIE SPIE SPP FS SUM MXR
```

- **Read**: `read_sstatus(m) = read_mstatus(m) && SSTATUS_RMASK` (L3 467).
- **Write** of `v`: `mstatus := legalize_mstatus((stored && ~SSTATUS_RMASK) || (v && SSTATUS_RMASK))`,
  or in closed form `(stored && ~0xC6122) || (v && 0xC6122)` (L3 469-470, unchanged; sail
  `legalize_sstatus`, `core/sys_regs.sail:995-1019`).
- **Access**: S and M; U gets illegal instruction (2).
- **Timing**: an SIE write is seen at the next step boundary ([D38]). SUM and MXR changes apply to the
  next access with no SFENCE.VMA (p.129); this holds automatically with no cache.

### 2.2 `stvec` (0x105) (P §12.1.2 p.116-117, Table 36)

- **Layout**: BASE[63:2] (WARL, 4-byte aligned) and MODE[1:0]: 0 Direct, 1 Vectored, ≥ 2 reserved.
- **Legaliser** ([D39]; L3 475-476):
  `legalize_xtvec(v, old) = if v[1] then v[63:2] @ old[1:0] else v`.
- **Trap vector** (L3 1536-1541):
  `trapVector = BASE@00 + (MODE = 1 ∧ intr ? 4·code : 0)`.
- Vectored targets: SSI +0x04, STI +0x14, SEI +0x24. Reset value 0 (Direct). Matches sail.

### 2.3 `sie` (0x104), `sip` (0x144) (P §12.1.3 p.117-118; §3.1.9 p.43-46)

The standard bits are SSI 1, STI 5, SEI 9 and LCOFI 13 (RO0, no Sscofpmf). A bit is visible iff it is
set in `mideleg` (p.46). The mask is `0x222`, so bits 3, 7 and 11 are never visible.
```
read  sie   = mie && mideleg                                   -- L3 1022
write sie v : mie := (mie && ~mideleg) || (v && mideleg)        -- L3 1110-1111
read  sip   = mip_eff && mideleg   (mip_eff = read_mip(), L3 750-758, includes external SEIP)  -- L3 1032
write sip v : if mideleg[1] then mip.SSIP := v[1]               -- L3 1124-1125
```
- **Writable bits.** In `sip` only SSIP is writable. STIP is read-only in `sip` without Sstc (p.118);
  M sets it through `mip`, p.45. SEIP is read-only in `sip`.
- **Priority within S**: SEI, SSI, STI (p.118).
- **RMW base** [S21]. L3 `accessCSR` (4328-4345) special-cases 0x344 to use the software-only SEIP as
  the base. For 0x144 the base is the full read. Bit 9 of that base never reaches storage, so the
  difference cannot be observed. sail special-cases both (`extensions/Zicsr/zicsr_insts.sail:42-92`,
  `core/interrupt_regs.sail:507-516`). Add a comment.

### 2.4 Counter gating (P §3.1.11 p.46-47; §12.1.4-12.1.5 p.118-119)

`mcounteren` and `scounteren` are 32 bits wide, with writable mask `0x7` (CY TM IR) ([D27]).

| Mode | Read of 0xC00/0xC01/0xC02 (bit i = csr[4:0]) allowed iff |
|---|---|
| M | always |
| S | `mcounteren[i]` (p.47) |
| U | `mcounteren[i] ∧ scounteren[i]` (p.119) |

`hpmcounter3-31` are illegal everywhere ([D25]). Writes to 0xC00-0xC02 are illegal. `stimecmp` is
absent (no Sstc). A failure raises illegal instruction (2) with `xtval` = the instruction bits. L3
`counterReadAllowed` (762-771) already matches this table, as does sail `feature_enabled_for_priv`
(`core/sys_regs.sail:1274-1292`).

### 2.5 `sscratch`, `sepc`, `scause`, `stval` (P §12.1.6-12.1.9 p.119-122)

- **`sscratch`** (0x140): 64 bits, never written by hardware.
- **`sepc`** (0x141) ([D44]):
  - write `v && ~1` (L3 481);
  - read `misa.C ? sepc : sepc && ~3` (L3 729-730), including SRET's implicit read.
- **`scause`** (0x142) ([D33], [S24]): bit 63 Interrupt, bits 62:0 code, WLRL.
  - `legalize_scause(v, old) = if v[62:0] ≤u 31 then v else legalize_mcause(v, old)` (L3 494-495;
    sail `legalize_cause(_, _, true)`, `core/sys_regs.sail:694-731`).
  - Codes this hart writes: interrupts 1, 5, 9; exceptions 0-9, 12, 13, 15.
- **`stval`** (0x143): written on every trap into S with the same value `mtval` would get. `tval` is
  computed before the destination (L3 `Next` 5315-5319).

| Cause | `stval` / `mtval` (P §12.1.9 p.121-122; §3.1.16 p.52) |
|---|---|
| interrupt | 0 |
| 0 instruction address misaligned | target VA |
| 1 instruction access fault, 12 instruction page fault | VA of the failing **parcel** (`pc`, or `pc + 2` for the upper half of a 32-bit instruction); `xepc = pc` |
| 2 illegal instruction | instruction bits, zero-extended (16 or 32) |
| 3 breakpoint | VA of the instruction ([D43]) |
| 4/6 misaligned | effective VA (raised before translation, [D55]) |
| 5/7 access fault, 13/15 page fault | the faulting **virtual** address, "even for physical-memory access-fault exceptions" (p.52): this covers PMP on the final PA and on a PTE |
| 8, 9 ECALL | 0 |

### 2.6 `senvcfg` (0x10A) (P §12.1.10 p.122-124)

FIOM (bit 0) stays writable: `senvcfg := v && 0x1` (L3 1116, [D29], [S25]). All other fields are
RO0. FIOM may be RO0 only "if satp.MODE is read-only zero" (p.123), which is no longer true. It has
no behavioural effect, because FENCE is a no-op in a sequential model. The same holds for
`menvcfg.FIOM` (L3 1142). `menvcfg.ADUE` and `menvcfg.PBMTE` stay RO0 ([S3], [S12]).

### 2.7 Delegation (P §3.1.8 p.42-43)

```
legalize_medeleg(v) = v && 0x0000_B3FF   -- 0-9, 12, 13, 15 ([D40]); 11 and 16 RO0 (p.43)
legalize_mideleg(v) = v && 0x0000_0222   -- SSI, STI, SEI ([D41])
ExcDest(code, y)    = if y ≠ M ∧ medeleg[code] then S else M   -- L3 excDest 1500-1502
```

1. "Traps never transition from a more-privileged mode to a less-privileged mode" (p.42). From M,
   every exception goes to M. This includes page faults from M-mode accesses under MPRV.
2. Horizontal traps happen: an exception in S that is delegated goes to S.
3. From U: a delegated exception goes to S, an undelegated one to M.
4. sail `exception_delegatee` (`sys/sys_control.sail:61-76`) is identical on {M, S, U}.
5. A delegated interrupt is never taken in M. An undelegated one goes to M "in any mode" (p.43).

Reset value of both registers: 0 ([D71]). cfg keeps `medeleg.delegatable_bits = 0xB3FF` [S22].
riscv-tests' vm.c delegates exactly 8, 12, 13 and 15.

### 2.8 Interrupt selection (P §3.1.6.1 p.32; §3.1.9 p.43-45; §12.1.3 p.117-118)

Interrupts are evaluated at the start of every step, before fetch ([D38], L3 `Next` 5281-5290;
[S23]). With `p = curPrivilege()`:

1. `pend := mip_eff && mie`.
2. `pend_m := pend && ~mideleg`; `pend_s := pend && mideleg`.
3. `m_enabled := (p = M ∧ MIE) ∨ p ∈ {S, U}` (p.32: higher modes always enabled).
4. `s_enabled := (p = S ∧ SIE) ∨ p = U` (never enabled in M; SIE is ignored in U, p.113).
5. If `m_enabled ∧ pend_m ≠ 0`, take `(Highest(pend_m), M)`. M interrupts have priority (p.44).
6. Else, if `s_enabled ∧ pend_s ≠ 0`, take `(Highest(pend_s), S)`.
7. Else, take no interrupt.

`Highest` uses the order MEI 11, MSI 3, MTI 7, SEI 9, SSI 1, STI 5 (p.45). This is already what L3
`highestInterrupt` (1505-1515) and `checkInterrupts` (1520-1534) compute, and what sail
`getPendingSet`/`findPendingInterrupt` (`sys/sys_control.sail:84-150`) compute. An interrupt step
does `TrapEntry(d, true, code, epc = PC, tval = 0)` and does not retire.

| Mode | Takeable |
|---|---|
| M, MIE = 1 | undelegated only |
| M, MIE = 0 | none |
| S, SIE = 1 | undelegated (to M), then delegated (to S) |
| S, SIE = 0 | undelegated only |
| U | undelegated (to M), then delegated (to S) |

### 2.9 Trap entry into S (P §3.1.6.1 p.32; §12.1.1 p.113-114; L3 `takeTrap` 1545-1563)

Let `y` be the current privilege before the trap, with `y ∈ {U, S}`.

1. `scause := intr << 63 || zext(code)`.
2. `sepc := epc`.
3. `stval := tval` (§2.5).
4. `SPIE := SIE`.
5. `SIE := 0`.
6. `SPP := (y = U ? 0 : 1)`.
7. `privilege := S`.
8. `PC := trapVector(stvec, intr, code)`.

The trap writes none of `mcause`, `mepc`, `mtval`, MPP, MPIE, MIE, MPRV or FS, and leaves the LR
reservation alone ([D45]). Trap entry into M from S is as in `design-privileged.md` §4.6, with
`MPP := 01`. This matches sail `trap_handler_inner` (`sys/sys_control.sail:267-340`).

### 2.10 SRET and MRET to S (P §3.3.2 p.61; §3.1.6.1 p.32-33; §3.1.6.6 p.37)

SRET is the encoding `0x10200073` (L3 4291-4298, `sret()` 1592-1601):

1. Illegal instruction (2, `tval = 0x10200073`) if `cur = U`, or if `cur = S ∧ TSR`. It is **legal
   in M whatever TSR is** (p.37, p.61).
2. `y := SPP ? S : U`.
3. `SIE := SPIE`.
4. `SPIE := 1`.
5. `SPP := 0`.
6. `MPRV := 0`. This is unconditional, because `y ≠ M` (p.33, p.35).
7. `privilege := y`.
8. `PC := read_xepc(sepc)`.
9. Retire. The reservation is kept.

SRET leaves MIE, MPIE, MPP and `scause` unchanged and has no SDT step. MRET with MPP = 01 enters S and
clears MPRV (L3 `mret()` 1581-1590). Both match sail (`extensions/I/base_insts.sail:664-727`).
vm.c runs **SRET from M** (`pop_tf`) to enter U, which the legality rule above allows.

### 2.11 WFI (P §3.3.3 p.61-62; §3.1.6.6 p.37) [S20], revising [D23]

| Mode | Behaviour |
|---|---|
| M | NOP: retires with `pc += 4`; an enabled pending interrupt is taken at the next step with `mepc = pc + 4` |
| S, TW = 0 | NOP |
| S, TW = 1 | illegal (2, `tval = 0x10500073`) **iff `(read_mip() && mie) = 0`**, else NOP |
| U | always illegal (cfg `wfi_available_to_user_mode = false`) |

The rule follows from two passages, given a zero time limit:

- "the hart must resume if a locally enabled interrupt becomes pending, even if it has been
  delegated" (p.62);
- the TW trap applies only if WFI "does not complete within an implementation-specific, bounded time
  limit" (p.37).

With a zero limit, WFI completes exactly when `mip_eff && mie ≠ 0` (ignoring MIE, SIE and
`mideleg`). L3 change E2:
```
case Supervisor => when MCSR.mstatus.TW and (read_mip() && MCSR.&mie) == 0 do signalException(Illegal_Instr)
```
The M and U arms are unchanged, so M-mode step theorems are unaffected.

sail matches this exactly with cfg `platform.wfi_is_nop = false` and `platform.max_time_to_wait = 0`.
With those settings:

- the first `try_step` enters the wait state;
- the second retires, or raises illegal in S with TW = 1, according to `shouldWakeForInterrupt`
  (`postlude/step.sail:51-73`, `sys/sys_control.sail:170-172`);
- `mtime`/`mcycle` advance once per WFI (`c_emulator/riscv_sim.cpp:538-596`), the same as the
  one-step L3 NOP;
- `compare.py` already folds the wait lines into the step (`S_IGNORE`, `sim/compare.py:185-189`).

With the current `wfi_is_nop = true`, sail retires S-mode WFI whatever TW is. Old [D23] trapped
whenever TW = 1. That is also legal (p.37 allows a trap even with globally disabled interrupts
pending), but it differs from sail when a delegated, `sie`-enabled interrupt is pending while
`SIE = 0`.

### 2.12 ECALL from S (P §3.3.1 p.60-61)

ECALL from S raises exception 9 with `tval = 0` and `epc = pc`, and does not retire. It goes to S if
`medeleg[9]`, else to M. L3 `signalEnvCall` (1488-1496) already matches.

### 2.13 SFENCE.VMA (P §12.2.1 p.127-130; §3.1.6.6 p.37) [S4]

Encoding `0001001 rs2 rs1 000 00000 1110011` (decode L3 4663).

| Mode | Result |
|---|---|
| U | illegal (2) |
| S, TVM = 1 | illegal (2) |
| S, TVM = 0 | retires, `pc += 4` |
| M | retires |

Operand meaning (p.128):

| rs1 | rs2 | Effect |
|---|---|---|
| x0 | x0 | everything |
| x0 | ≠ x0 | ASID `X[rs2]`, not global |
| ≠ x0 | x0 | leaf PTEs for VA `X[rs1]`, all ASIDs |
| ≠ x0 | ≠ x0 | leaf PTEs for VA `X[rs1]` in ASID `X[rs2]`, not global |

A non-canonical `X[rs1]` does nothing and raises no exception.

**In this model SFENCE.VMA is a no-op that retires.** Over-fencing is always legal, and an implicit
read "may return any translation for an address that was valid at any time since the most recent
SFENCE.VMA" (p.128). A cache-free hart always uses the current translation, which is in that allowed
set. The same reasoning covers `satp`, SUM/MXR and PMP writes (p.129, §3.7.2 p.74). The body
(L3 4390-4396) is unchanged; only the comment changes (E3).

sail has the same legality (`base_insts.sail:772-791`) but flushes its TLB. Its encdec guard
`virtual_memory_supported() | not(sfence_vma_illegal_if_svbare_only)` is true once Sv39 is on, so
[D46]'s cfg knob becomes moot.

### 2.14 TVM, TW, TSR (P §3.1.6.6 p.37)

| Bit | M | S | U |
|---|---|---|---|
| TVM | no effect | `satp` access and SFENCE.VMA are illegal | — (already illegal) |
| TW | WFI is a NOP | §2.11 | WFI is always illegal |
| TSR | SRET is legal | SRET is illegal | SRET is always illegal |

All three are stored RW bits in `MSTATUS_WMASK` and are not visible in `sstatus`.

### 2.15 MPRV with MPP = S or U

Effective privilege and SUM/MXR under MPRV are specified in §3.3. Faults raised under MPRV have
`y = M` and so trap to M (§2.7 rule 1). `mtval` holds the VA.

The invariant `curPrivilege() ≠ M ⇒ MPRV = 0` still holds on reachable states ([D22]), for these
reasons:
- reset clears MPRV;
- `sstatus` does not expose it;
- MRET to S/U and every SRET clear it;
- traps never lower the privilege.

---

## 3. Address translation

### 3.1 Fixed parameters

| Item | Value | Source |
|---|---|---|
| SXLEN = UXLEN | 64 (SXL = UXL = 2 read-only, [D19]) | P §3.1.6.3 p.34 |
| `satp.MODE` legal values | 0 Bare, 8 Sv39, 9 Sv48, 10 Sv57 ([S7]) | P Table 40 p.126 |
| PAGESIZE, PTESIZE | 4096, 8 | P §12.3.2 p.134, §12.4.1 p.137 |
| LEVELS | 3 (Sv39), 4 (Sv48), 5 (Sv57) | P §12.4.1 p.137, §12.5.1 p.138, §12.6.1 p.139 |
| VALEN | 12 + 9·LEVELS = 39 / 48 / 57 | Figures 68, 71, 74 |
| PABITS | 56; PPN 44 bits ([S9]) | Figures 69, 72, 75 |
| ASIDLEN | 16 ([S8]) | P §12.1.11 p.125 |
| A/D scheme | Svade: page fault, no hardware update ([S3]) | P §12.3.1 p.132, §12.10 p.144 |
| Address-translation cache | none; SFENCE.VMA is a no-op ([S4]) | P §12.3.2 p.135 |
| Svnapot, Svpbmt, Svrsw60t59b, Svinval, Svukte | absent; their PTE bits are reserved and give page faults ([S12]) | P §12.4.1 p.137, §12.12 p.145 |
| Ssccptr, Svvptc | satisfied trivially (flat memory, no cache); Ssccptr advertised in the cfg, Svvptc not ([S13]) | P §12.11 p.144 |
| PMA on PTE accesses | none: flat memory ([D54], [S14]) | |

### 3.2 `satp` (0x180, SRW) (P §12.1.11 p.124-126)

#### 3.2.1 Layout for SXLEN = 64 (Figure 64 p.125)

| Bits | Field | Here |
|---|---|---|
| 63:60 | MODE (WARL) | legal values {0, 8, 9, 10} |
| 59:44 | ASID (WARL) | all 16 bits writable |
| 43:0 | PPN (WARL) | all 44 bits writable; root table at `PPN << 12` |

#### 3.2.2 MODE encodings (Table 40 p.126)

| Value | Meaning | Here |
|---|---|---|
| 0 | Bare | supported |
| 1-7 | reserved | ignored |
| 8 | Sv39 | supported |
| 9 | Sv48 | supported (needs Sv39, p.137) |
| 10 | Sv57 | supported (needs Sv48, p.138) |
| 11 | Sv64 (reserved) | ignored |
| 12-13 | reserved | ignored |
| 14-15 | custom | ignored |

#### 3.2.3 `legalize_satp(v, old)` (replaces [D32]; sail `core/sys_regs.sail:1192-1250`) [S10]

1. If `v[63:60] ∉ {0, 8, 9, 10}`, return `old`. This is mandated: "the entire write has no effect;
   no fields in satp are modified" (p.125).
2. ASID bits `59:44+ASIDLEN` are forced to 0. This is vacuous with ASIDLEN = 16.
3. PPN bits `43:PABITS−12` are forced to 0. This is vacuous with PABITS = 56.
4. Return `v`. MODE = 0 with a nonzero ASID or PPN is UNSPECIFIED (p.125); the value is stored as
   written and translated as the identity, as sail does.

L3 form. Use a mask comparison, not a `<63:60>` extract, so that HolBA's `riscv_csr_conv` lifts it
(resolution R9):
```
regType legalize_satp(v::regType, old::regType) =
{ m = v && 0xF000_0000_0000_0000
; if m == 0 or m == 0x8000_0000_0000_0000 or m == 0x9000_0000_0000_0000
       or m == 0xA000_0000_0000_0000
  then v else old
}
```

- **Reset**: 0 ([D71]).
- **Read**: the stored value. vm.c checks `read_csr(satp) == satp_value`.
- **Write timing**: a write takes effect for the next access, including Bare↔Sv changes (p.129).
- **Access** (unchanged, [D32], L3 994-1001): M always; S iff `TVM = 0`; U never. A denied access
  raises illegal instruction (2). sail: `is_satp_accessible`, `sys/vmem.sail:246-256`.
- **Location** [S27]: `satp :: regType` stays in `SupervisorCSR` (`c_SCSR`). MODE is read as
  `satp<63:60>` in `translateAddr`.

#### 3.2.4 When `satp` is active

Translation happens **iff** `p ∈ {S, U} ∧ satp.MODE ≠ 0` (p.126). Here `p` is the privilege of §3.3,
and MODE values that legalisation makes unreachable (1-7, 11-15) are treated as Bare ([S11]).

### 3.3 Privilege used for translation (P §3.1.6.4 p.35; [D22])

| Access | Privilege `p` for translation and for PMP on the final PA |
|---|---|
| Instruction fetch (both parcels) | `curPrivilege()`: "unaffected by the setting of MPRV" (p.35) |
| Explicit load, store, AMO, LR, SC, FP load/store | `effectivePrivilege() = MPRV ? privilege(MPP) : curPrivilege()` (sail `sys/sys_control.sail:11`) |
| Implicit PTE read | no translation (the address is physical); PMP privilege **S** (P §3.7.2 p.74; sail `read_pte` passes `Supervisor`, `sys/vmem.sail:67`) |

- With `MPRV ∧ MPP = S`, M-mode loads and stores are translated with S rules and **SUM applies**
  (p.35: "it is in effect when MPRV=1 and MPP=S"). MXR applies to loads.
- `rv64si-p-dirty` and the arch tests `sv39_mstatus_mprv_*` and `sv39_exceptions_mprv_*` exercise
  this.
- P §12.3.2 step 6 says "current privilege mode". It is read as the effective privilege, per p.35,
  as sail does.

### 3.4 Address and PTE formats

#### 3.4.1 Virtual addresses (Figures 68, 71, 74)

`VPN[i] = va[20+9i : 12+9i]`, and the page offset is `va[11:0]`.

| Scheme | Top VPN | Canonical rule (else page fault) |
|---|---|---|
| Sv39 | VPN[2] = va[38:30] | va[63:39] all equal to va[38] (p.136) |
| Sv48 | VPN[3] = va[47:39] | va[63:48] all equal to va[47] (p.138) |
| Sv57 | VPN[4] = va[56:48] | va[63:57] all equal to va[56] (p.139) |

The canonical check is `((va << (64−VALEN)) >> (64−VALEN)) == va`, where `>>` is arithmetic. It
applies to fetch addresses and load/store effective addresses, comes **before** any PTE read, and
gives a page fault of the access type (sail `translate_validate_address`, `sys/vmem.sail:503-510`).
sail reports `tval` as the full 64-bit VA (checked on `sv39_canonical_Smode`).

#### 3.4.2 Physical addresses (Figures 69, 72, 75)

A translated PA is 56 bits: PPN[43:0] and offset[11:0], so `pa[63:56] = 0`. The split of the PPN
into fields (for example Sv39: PPN[2] = pa[55:30] of 26 bits, then two fields of 9 bits) matters
only for the superpage alignment check, which §3.5 states on the 44-bit `pte.PPN`. Under Bare, or
when `p = M`, the PA is the full 64-bit address, as today ([D54]).

#### 3.4.3 PTE (Sv39 Figure 70 p.136; Sv48 Figure 73 p.138; Sv57 Figure 76 p.138: the same 64-bit layout)

| Bits | Field | Rule here |
|---|---|---|
| 63 | N (Svnapot) | must be 0, else page fault |
| 62:61 | PBMT (Svpbmt) | must be 0, else page fault |
| 60:54 | reserved (60:59 also because Svrsw60t59b is absent, p.145) | must be 0, else page fault |
| 53:10 | PPN (44 bits) | |
| 9:8 | RSW | ignored (p.132) |
| 7 | D | dirty; reserved in a non-leaf PTE (p.133) |
| 6 | A | accessed; reserved in a non-leaf PTE |
| 5 | G | global; **no effect** (no TLB) |
| 4 | U | user; reserved in a non-leaf PTE |
| 3, 2, 1 | X, W, R | |
| 0 | V | valid; if 0, all other bits are don't-care (p.131) |

Masks: `PTE_RSV = 0xFFC0_0000_0000_0000` (bits 63:54); non-leaf reserved bits `0xD0` (D, A, U).

XWR (Table 41 p.131):

| XWR | Meaning |
|---|---|
| 000 | pointer to the next level |
| 001 | read-only |
| 011 | read-write |
| 100 | execute-only |
| 101 | read-execute |
| 111 | read-write-execute |
| 010, 110 | reserved, page fault (010 is Zicfiss with `menvcfg.SSE`, absent) |

So after step 6, W = 1 implies R = 1.

Superpages: a leaf at level i > 0 maps 2^(12+9i) bytes. Level 1 is 2 MiB, level 2 is 1 GiB, level 3
is 512 GiB (Sv48 and Sv57), level 4 is 256 TiB (Sv57). A superpage must be aligned:
`pte.PPN[9i−1:0] ≠ 0` gives a page fault (p.134 step 5, p.137).

### 3.5 The translation algorithm (P §12.3.2 p.134, RV64, PTESIZE = 8)

**Inputs**:
- `va`;
- the access class: Fetch `(Instruction, Read)`; Load `(Data, Read)`, which covers loads, LR and FP
  loads; Store `(Data, Write)`, which covers stores, SC, AMOs and FP stores ("AMOs never raise load
  page-fault exceptions", p.132);
- `p` as in §3.3.

**Output**: an address, a page fault or an access fault. §1.2 maps the faults to codes.

0. **Active check.** If `p = M`, or `MODE ∉ {8, 9, 10}`, return `va` (p.125-126).
1. `L := 3 / 4 / 5` for MODE `8 / 9 / 10`, and `VALEN := 12 + 9L`. If `va` is not canonical
   (§3.4.1), return a **page fault**.
2. `a := satp.PPN << 12`, `i := L − 1` (spec step 1).
3. `pteAddr := a + (VPN[i] << 3)`, with `VPN[i] = (va >>+ (12+9i)) && 0x1FF`. The sum has no carry
   (spec step 2).
4. **PMP on the PTE read**: if `¬pmpCheck(pteAddr, 8, PMP_Read, Supervisor)`, return an **access
   fault**. It is reported as the fault "corresponding to the original access type" (spec step 2;
   §3.7.2 p.74; [D53], [S14]). There is no PMA check.
5. `pte := MEM(pteAddr<63:3>)`: one aligned 8-byte little-endian read, with no log entry ([S6]).
6. **Validity** (spec step 3): return a **page fault** if any of these holds:
   - (a) `V = 0`;
   - (b) `R = 0 ∧ W = 1`;
   - (c) `pte[63:54] ≠ 0`;
   - (d) the PTE is non-leaf (`R = W = X = 0`) and `D ∨ A ∨ U` ([S12]).

   sail: `pte_is_invalid`, `sys/vmem_pte.sail:91-115`; (d) because `pte_reserved_bits_must_be_zero`
   holds for priv ≥ 1.12.
7. **Pointer** (spec step 4): if `R = 0 ∧ X = 0`:
   - if `i = 0`, return a **page fault**;
   - else set `a := pte.PPN << 12`, `i := i − 1`, and go to step 3.
8. **Misaligned superpage** (spec step 5): if `i > 0 ∧ pte.PPN[9i−1:0] ≠ 0`, return a **page fault**.
   sail checks this before the permission checks, in the spec's order.
9. **U bit** (spec step 6; p.132; p.35). If the access is not allowed, return a **page fault**:
   - `p = U`: allowed iff `U = 1`;
   - `p = S ∧ U = 0`: allowed;
   - `p = S ∧ U = 1`: allowed iff the access is not a fetch and `SUM = 1`. "Irrespective of SUM, the
     supervisor may not execute code on pages with U=1" (p.132).
10. (Spec step 7, Zicfiss, does not apply.)
11. **R/W/X** (spec step 8). If the check fails, return a **page fault**:
    - a fetch needs `X`;
    - a load needs `R ∨ (MXR ∧ X)`;
    - a store needs `W`.

    sail requires `W ∧ (R ∨ MXR∧X)` for an AMO. After step 6(b) this equals `W`, so the two are not
    in conflict (R12).
12. **A/D under Svade** (spec step 9, first bullet; p.132): if `A = 0`, or the access is a store and
    `D = 0`, return a **page fault**. Loads and fetches never need D. The PTE is never written.
13. **Success** (spec step 10): `pa := (pte.PPN << 12) || (va && (2^(12+9i) − 1))`. The OR is exact
    because step 8 forced the low PPN bits to 0. Return `pa`.

After a successful translation, the **caller** checks PMP on `pa` at privilege `p`. A failure there is
an access fault (1/5/7) ([D53]; p.131).

**Svadu alternative to step 12** (not chosen, [S3]; spec step 9, bullets 2-3; sail
`update_and_write_pte`, `sys/vmem.sail:98-123`). If `A = 0 ∨ (store ∧ D = 0)`:
- (i) a PMP write check of `pteAddr` at S, giving an access fault on failure;
- (ii) `pte' := pte || A || (store ? D : 0)`;
- (iii) write `pte'` before the explicit access becomes visible (p.133).

This makes `translateAddr` write state. Notes on sail's version:
- sail writes back without the compare step;
- sail sets D also for an SC that later fails, and for every AMO;
- on a TLB hit, sail writes back the cached PTE, although p.135 says the cache cannot be used in
  step 9.

### 3.6 Facts that follow from the algorithm

- **Order.** Within one walk, every page-fault condition gives the same code and the same `tval`.
  Two orders are observable:
  - a PTE-read access fault at level i comes after page faults from levels above i and before
    everything below;
  - the canonical check comes before any PTE read.
- **Reads.** At most L PTE reads, all 8-aligned, and no PTE writes.
- **No effect** from G, RSW or the ASID. MXR and SUM never affect PMP (p.35).
- **Page crossing.** No data access crosses a page: misaligned accesses trap first ([D55], [S15]),
  fetch parcels are 2 bytes, and PTE reads are 8-aligned. The only case with two translations is a
  32-bit instruction whose upper parcel lies on the next page (§3.8).
- **Timing.** Changes to SUM, MXR, `satp` and the PTEs take effect on the next access with no fence.

### 3.7 Fault table (codes from Table 16 p.50; `tval` = the faulting VA, P §3.1.16 p.52, §12.1.9 p.121)

| Failure | Fetch parcel | Load, LR, FP load | Store, SC, AMO, FP store |
|---|---|---|---|
| misaligned (before translation, [D55]) | — (code 0 is raised by the jump) | 4 | 6 |
| non-canonical VA (step 1) | 12 | 13 | 15 |
| PMP denies the PTE read (step 4) | 1 | 5 | 7 |
| invalid or reserved PTE (step 6) | 12 | 13 | 15 |
| pointer PTE at level 0 (step 7) | 12 | 13 | 15 |
| misaligned superpage (step 8) | 12 | 13 | 15 |
| U / SUM (step 9) | 12 | 13 | 15 |
| R/W/X / MXR (step 11) | 12 | 13 | 15 |
| A = 0, or a store with D = 0 (step 12) | 12 | 13 | 15 |
| PMP denies the final PA (caller) | 1 | 5 | 7 |

Every code is delegable (`medeleg` mask `0xB3FF`). `xepc = pc`. For a fetch, `tval` is the address
of the failing parcel (`pc` or `pc + 2`). For a data access, sail's `tval` is the VA of the access
(`vmem_utils.sail:exception_vaddr`). sail maps errors to codes in `translationException`
(`sys/vmem_ptw.sail:73-140`):
- `PTW_No_Access` gives 1/5/7;
- `Invalid_Addr`, `Invalid_PTE`, `No_Permission`, `Misaligned` and `PTE_Needs_Update` give 12/13/15.

### 3.8 Priority (P Table 17 p.51)

**Fetch** (there is no Sdtrig):
1. Lower parcel at `pc`: the first fault met during translation (12, or 1 for a PTE), with
   `tval = pc`.
2. Lower parcel: PMP on its PA (1), with `tval = pc`.
3. Only if `parcel[1:0] = 11`:
   - (3a) upper parcel at `pc + 2`, translation fault 12 or 1;
   - (3b) upper parcel, PMP fault 1.

   Both have `tval = pc + 2` and `epc = pc`.

   The lower-then-upper order is forced, because the length is known only after the lower parcel
   is read. It is today's `Fetch()` ([D59], [S16]). Notes:
   - With `pc ≡ 0xFFE (mod 4096)`, the upper parcel is on the next page.
   - The cfg leaves Ziccif off, so sail also translates per parcel (`postlude/fetch.sail:96-111`).
     With Ziccif on, a 4-aligned `pc` would give the same verdicts.
4. Illegal instruction (2), then misaligned jump target (0), ECALL, EBREAK, as in
   `design-privileged.md` §4.3.

**Explicit data access** (exactly one translation per instruction):
1. Misaligned (4/6), raised "without performing address translation or protection checks" (p.51,
   [D55]). The cfg's `AlignmentException` makes sail do the same, so sail's page-split path is never
   taken.
2. The first fault met during translation (13/15, or 5/7 for a PTE).
3. PMP on `pa` at `p` (5/7).
4. SC only: if steps 1-3 pass and the reservation does not match, `rd := 1` and nothing is written.
   Translation and PMP are evaluated whatever the reservation ([S18], extending [D60]; sail
   `sys/vmem_utils.sail:356-372`).

**AMO**: steps 1-3 with the store codes 6, 15 and 7. Under Svade a page with D = 0 faults.

### 3.9 PMP and paging

- PMP checks of PTE reads use S and the R bit ([S14]).
- PMP checks of the final PA use `p` and the access kind.
- PMP changes take effect at once, with no fence: there is no cache, which is allowed by §3.7.2
  p.74.
- `pmpCheck(pa, n, kind, p) -> bool` keeps its interface ([D53]). PTE accesses are the reason it
  returns `bool` and lets the caller choose the code.

### 3.10 LR/SC reservation [S17]

The reservation set lies within one physical page (P §12.3.1 p.133). sail reserves the **physical**
address (`match_reservation(bits_of(paddr))`, `sys/vmem_utils.sail:358`). Change
`c_ReserveLoad :: id -> vAddr option` (L3 579, 651) to hold the `pAddr` that `dataAddr` returns.
`matchLoadReservation` (L3 1884) compares the SC's translated `pa`. In M-mode the PA equals the VA,
so M-mode theorems keep their shape. The type is still `regType option`, so only the variable name
changes.

### 3.11 L3 structure

Types, in the "memory" block near L3 54, next to `accessType` and `fetchType`:
```
-- The physical address of an access, or the exception it raises (Table 16 p.50).
construct TransResult { TR_Address :: pAddr, TR_Fault :: ExceptionType }

-- One level of the walk (P §12.3.2 p.134): the next table, or a result.
construct walkResult { W_Next :: bits(44), W_Address :: pAddr, W_PageFault, W_AccessFault }
```

Functions, replacing L3 1750-1757 and 1860-1878:
```
ExceptionType pageFault(ft::fetchType, ac::accessType) =
    if ft == Instruction then Fetch_PageFault
    else if ac == Read then Load_PageFault else Store_AMO_PageFault

ExceptionType accessFault(ft::fetchType, ac::accessType) =
    if ft == Instruction then Fetch_Fault
    else if ac == Read then Load_Fault else Store_AMO_Fault

-- Leaf permission checks (P §12.3.2 steps 6, 8, 9 p.134; §3.1.6.4 p.35; Svade).
bool ptePermits(pte::dword, ft::fetchType, ac::accessType, p::Privilege) =
{ store = ft == Data and ac == Write
; uOK   = if p == User then pte<4>
          else not pte<4> or (ft == Data and MCSR.mstatus.SUM)
; xwrOK = if ft == Instruction then pte<3>
          else if ac == Read then pte<1> or (pte<3> and MCSR.mstatus.MXR)
          else pte<2>
; adOK  = pte<6> and (not store or pte<7>)
; uOK and xwrOK and adOK
}

-- Level i of the walk with the table at ppn (§3.5 steps 3-8, 13).
walkResult ptwLevel(i::nat, ppn::bits(44), va::vAddr, ft::fetchType,
                    ac::accessType, p::Privilege) =
{ pteAddr = ((ZeroExtend(ppn)::pAddr) << 12) + (((va >>+ (12 + 9 * i)) && 0x1FF) << 3)
; if not pmpCheck(pteAddr, 8, PMP_Read, Supervisor) then W_AccessFault
  else
  { pte  = MEM(pteAddr<63:3>)                          -- no mark_log ([S6])
  ; leaf = pte<1> or pte<3>
  ; if not pte<0> or (pte<2> and not pte<1>) or (pte && 0xFFC0000000000000) != 0
       or (not leaf and (pte && 0xD0) != 0)
    then W_PageFault
    else if not leaf then (if i == 0 then W_PageFault else W_Next(pte<53:10>))
    else
    { base = (ZeroExtend(pte<53:10>)::pAddr) << 12
    ; mask = ((1::pAddr) << (12 + 9 * i)) - 1
    ; if (base && mask) != 0 then W_PageFault         -- misaligned superpage
      else if not ptePermits(pte, ft, ac, p) then W_PageFault
      else W_Address(base || (va && mask))
    }
  }
}

-- Run level i only while the walk is descending and i < levels.
walkResult ptwStep(r::walkResult, i::nat, levels::nat, va::vAddr,
                   ft::fetchType, ac::accessType, p::Privilege) =
    match r
    { case W_Next(ppn) => if i < levels then ptwLevel(i, ppn, va, ft, ac, p) else r
      case _           => r
    }

-- Address translation (P §12.1.11 p.125-126, §12.3.2 p.134, §12.4-12.6 p.136-139).
-- Off at M (p is curPrivilege() for fetch, effectivePrivilege() for data,
-- P §3.1.6.4 p.35) and with Bare; reserved MODEs are unreachable and act as Bare.
TransResult translateAddr(va::vAddr, ft::fetchType, ac::accessType, p::Privilege) =
  if p == Machine then TR_Address(va)
  else
  { satp   = SCSR.satp
  ; levels = match satp<63:60> { case 8 => 3  case 9 => 4  case 10 => 5  case _ => 0 }
  ; if levels == 0 then TR_Address(va)
    else
    { sh = 64 - (12 + 9 * levels)
    ; if ((va << sh) >> sh) != va then TR_Fault(pageFault(ft, ac))     -- non-canonical
      else
      { r4 = ptwStep(W_Next(satp<43:0>), 4, levels, va, ft, ac, p)
      ; r3 = ptwStep(r4, 3, levels, va, ft, ac, p)
      ; r2 = ptwStep(r3, 2, levels, va, ft, ac, p)
      ; r1 = ptwStep(r2, 1, levels, va, ft, ac, p)
      ; r0 = ptwStep(r1, 0, levels, va, ft, ac, p)
      ; match r0
        { case W_Address(pa)  => TR_Address(pa)
          case W_AccessFault  => TR_Fault(accessFault(ft, ac))
          case _              => TR_Fault(pageFault(ft, ac))   -- W_PageFault; W_Next unreachable
        }
      }
    }
  }

-- The physical address of the 2-byte parcel at vAddr (MPRV does not apply, p.35).
TransResult fetchAddr(vAddr::vAddr) =
{ p = curPrivilege()
; match translateAddr(vAddr, Instruction, Read, p)
  { case TR_Address(pa) => if pmpCheck(pa, 2, PMP_Execute, p) then TR_Address(pa)
                           else TR_Fault(Fetch_Fault)
    case f              => f
  }
}

-- The physical address of an explicit, aligned n-byte data access (P §3.7 p.70).
TransResult dataAddr(vAddr::vAddr, n::nat, kind::pmpAccess) =
{ p  = effectivePrivilege()
; ac = if kind == PMP_Read then Read else Write
; match translateAddr(vAddr, Data, ac, p)
  { case TR_Address(pa) => if pmpCheck(pa, n, kind, p) then TR_Address(pa)
                           else TR_Fault(accessFault(Data, ac))
    case f              => f
  }
}
```

Properties:

- **Unrolled walk** [S5]: five non-recursive `ptwStep` calls with literal levels, in the style of
  the unrolled `pmpCheck` (L3 1823-1857). There is no termination obligation, so
  `checkDelegation.sml`-style hand proofs are not needed.
- **Total**: every `match` is exhaustive, there is no `#UNDEFINED`, and the `nat` subtraction cannot
  underflow because `levels ≥ 3` on that path.
- **Read-only**: the functions read `c_privilege`, `c_MCSR`, `c_SCSR` and `MEM8`. That L3 accepts a
  catch-all `case f => f` that rebinds the scrutinee, and that `MEM(…)` can be read inside a
  function, are both to be confirmed when the export is generated. The fallback is to spell out
  `case TR_Fault(e) => TR_Fault(e)` and to read `MEM8` byte by byte.

*Stage 2 notes.* (1) L3 needs a type declared before it is used, and `pAddr` (L3 60) and
`ExceptionType` (L3 214) come after L3 54, so the types cannot stand in the "memory" block: an
export with `TransResult` there stops with "Bad type: pAddr". Both types open the Address
Translation section, which now follows the PMP section, because `ptwLevel` calls `pmpCheck`.
(2) The first arm of the `levels` match is written `3::nat`: without it L3 types `levels` as
`bits(64)`, from the shifts by `sh`, and the `ptwStep` calls fail to type-check. (3) Q15: L3
accepts both constructs, so no fallback is used. The HOL export defines `ptePermits`, `ptwLevel`,
`ptwStep`, `translateAddr`, `fetchAddr` and `dataAddr` as functions of the state that return no
state (L3's "ok-fun"); `mtime()` already read `MEM` inside a function. `riscvScript.sml` builds
under HOL develop and `trindemossen-2` with no termination goal.

### 3.12 Call-site changes (E4)

- **37 `dataAddr` call sites** (L3 2418-3680: 11 `PMP_Read`, 8 `PMP_Write`, 18 `PMP_ReadWrite`;
  resolution R7):
  - `case Some(pAddr) =>` becomes `case TR_Address(pAddr) =>`;
  - `case None => signalAddressException(X_Fault, vAddr)` becomes
    `case TR_Fault(e) => signalAddressException(e, vAddr)`.
- **`Fetch()`** (L3 4431-4458): `FETCH_FAULT(addr)` (L3 4414) becomes `FETCH_FAULT(e, addr)`, and the
  two `None` arms become `TR_Fault(e)`. `tval` stays `vPC` or `vPC + 2`.
- **`riscv_step$Fetch_def`**: the patterns change as in §1.4 (F1).
- **`recordLoad`/`recordStore`** (L3 1313-1325, `when not PROVER_EXPORT`): record the **PA**, so the
  trace matches sail's `mem[R|W,PA]` (§4.6). This has no HOL impact, because the functions are not
  exported.
- **`ReserveLoad`**: record the PA (§3.10).
- **E1** (`MSTATUS_WMASK`, SUM field) lands in the same commit.

---

## 4. Oracle and corpus

### 4.1 sail's translation behaviour against this model

- **Effective privilege and mode** (`vmem.sail:satp_mode`; `types.sail:satpMode_of_bits`):
  translation is the identity iff `eff = M ∨ MODE = 0`, which equals §3.2.4.
- **Walk** (`vmem.sail:pt_walk`): recursive, with `termination_measure … = level`. Its checks and
  their order are those of §3.5:
  - PTE reads through `mem_read(Load(PageTableEntry), …, Supervisor, pte_addr, 8)`, with PMA
    `supports_pte_read` and PMP R at S;
  - `pte_is_invalid`;
  - non-leaf at level 0;
  - misaligned superpage before the permission checks;
  - `check_PTE_permission`;
  - `update_PTE_Bits`.
- **A/D** (`vmem_pte.sail:hw_updates_pte`): hardware updates iff `(Svadu ∧ menvcfg.ADUE) ∨ (¬Svadu ∧
  ¬Svade)`. `ADUE` is writable only with Svadu (`legalize_menvcfg`, `sys_regs.sail:518`), and
  `menvcfg` resets to 0.

  | cfg | Behaviour |
  |---|---|
  | Svade only (**chosen**) | never updates; A/D faults; ADUE RO0 |
  | Svadu, or Svadu + Svade (sail default) | Svade behaviour until software sets ADUE |
  | neither | always updates (legacy) |

- **TLB** (`vmem_tlb.sail:79-84`): 64 entries, direct-mapped, indexed by `vpn[5:0] ^ stage`,
  **always on with no config knob**.
  - It is filled only on successful walks, so Svvptc holds by construction.
  - It is flushed only by SFENCE.VMA and reset, not by `satp` writes (correct, p.126).
  - On a hit there is no PTE re-read, no re-check of PMP or PMA on the PTE, and no re-check of steps
    6/8. Steps 9-12 are redone on the cached PTE.
  - What this makes observable:
    1. PTE reads appear only on misses;
    2. stale translations, if software skips a required SFENCE.VMA (allowed, p.135);
    3. with hardware A/D, stale write-backs.
- **Experiment** (scratch `sail-oracle/notlb/`: sail with `lookup_TLB` forced to `None()`, compared
  with `compare.py --normalise` against stock sail; scratch results `tlbcmp*-results.txt`):
  - identical normalised traces on all 118 riscv-tests runs with the §4.2 cfg (110 `-v`, 7
    `rv64si-p`, napot);
  - identical on 117/117 with hardware A/D, PTE `mw` writes included;
  - identical on 86 non-Sv57 S/Sv arch tests run with V enabled;
  - only the **number of PTE `mem[R]` lines** differs: `rv64ui-v-add` has 6,871 with the TLB and
    31,458 without.

  **So the TLB-free L3 model can be compared against stock sail, as long as PTE reads are not
  compared** ([S4], [S6]). Keep the `notlb` build for any test that deliberately omits a fence.
- **satp, SFENCE.VMA, asidlen, physaddr_bits**: as in §3.2 and §2.13. sail limits asidlen to 16
  and physaddr_bits to 13..64; 56 is the default.

### 4.2 Oracle cfg hunk (merge into `rv64gc_mu_pmp.json`)

This merges the sail-and-corpus proposal with the S-mode WFI settings and Sv57 (resolutions R4, R8):
```json
{
  "memory":   { "physaddr_bits": 56, "asidlen": 16 },
  "platform": { "wfi_is_nop": false, "max_time_to_wait": 0 },
  "extensions": {
    "Sv39":        { "supported": true },
    "Sv48":        { "supported": true },
    "Sv57":        { "supported": true },
    "Ssccptr":     { "supported": true },
    "Svade":       { "supported": true },
    "Svadu":       { "supported": false },
    "Svvptc":      { "supported": false },
    "Svnapot":     { "supported": false },
    "Svpbmt":      { "supported": false },
    "Svrsw60t59b": { "supported": false },
    "Svinval":     { "supported": false },
    "Svukte":      { "supported": false },
    "Svbare":      { "supported": true, "sfence_vma_illegal_if_svbare_only": false }
  }
}
```

- **Staging.** The `platform` lines go in at stage 1. The `extensions` lines go in at stage 2,
  together with E1 and E4, because SUM's writability in sail follows `Sv39` (§2.1).
- **Validation.** `sail_riscv_sim --config-override rv64gc_mu_pmp.json --config-override
  wp7-override.json --validate-config` reports the config as valid. This was checked on the hunk
  without the `platform` lines and with Sv57 false. The scratch copy is
  `sail-oracle/wp7-override.json`. Re-validate the merged hunk.
- **ISA string**: `rv64imafdc_zicntr_zicsr_zifencei_za128rs_za64rs_zca_zcd_zvl32b_zvl64b_zvl128b_zvl256b_ssccptr_ssstrict_ssu64xl_svade`.
  With Sv57 on, also `sv57`. *Stage 2 note:* with the merged hunk, Sv57 on, sail prints exactly the
  string above (`--print-isa-string`); it names none of `sv39`, `sv48` and `sv57`.
- **Constraints the validator enforces** (`validate_config.sail:check_mmu_config`, each probed):
  - Sv48 needs Sv39, and Sv57 needs Sv48 (Sv57 without Sv48 was rejected);
  - Ssccptr, Svade, Svadu and Svvptc each need Sv39;
  - Svadu needs a PMA region with `supports_pte_write` ∧ RsrvEventual;
  - asidlen ≤ 16 (17 was rejected).
- **Unchanged**: misaligned = AlignmentException, `medeleg` 0xB3FF, `wfi_available_to_user_mode`
  false, simple interrupt generator off ([D73]).
- **Re-run needed.** The sail runs in §4.1 and §4.4 used `wfi_is_nop = true` and Sv57 off. Re-run
  them with the merged hunk. Neither setting matters to vm.c, which never executes WFI and uses
  Sv39.

### 4.3 The riscv-tests virtual-memory environment (`env/v/vm.c`, `entry.S`)

The source is riscv-test-env master of 2026-01-09, kept in scratch `sail-oracle/dl-env/`. The tag
used to build the prebuilt ELFs is unknown, but master matches what the prebuilt ELFs do.

1. **Boot in M** (`entry.S`):
   - zero the GPRs;
   - `INIT_RNMI` (its `csrwi 0x744` traps illegal in M, as in the `-p` tests);
   - `mtvec` → `wtf` (exit 841);
   - `mscratch` = stack;
   - `extra_boot`;
   - `vm_boot(userstart)`.
2. **`vm_boot`**:
   - Builds **Sv39** tables. `-DSv48` would build Sv48, but the prebuilt ELFs use Sv39.
   - `l1pt[0]` → `user_l2pt` → `user_llpt`: 4 KiB user pages, all invalid at first.
   - `l1pt[511]` → `kernel_l2pt[511]`, a **2 MiB leaf** VRWXAD (no U, no G) mapping VA
     `0xFFFFFFFFFFE00000` to PA `0x80000000`. This exercises superpages and sign-extended VAs.
3. **`satp`**: writes `8<<60 | l1pt>>12` in M with ASID 0, **reads it back and fails on a
   mismatch**, then runs `sfence.vma` in M (rs1 = DRAM_BASE, rs2 = x0).
4. **PMP**: `pmpaddr0 = 2^53−1`, `pmpcfg0 = NAPOT|RWX`, which covers 2^56 bytes.
5. **Supervisor state**:
   - `stvec` and `sscratch` = kernel VAs;
   - `medeleg` = {8, 12, 13, 15}; `mideleg` is not written;
   - `mstatus = FS|XS|VS` (MPP = SPP = SUM = 0); `mie = 0`.
6. **Enter U**: `pop_tf` sets `sepc` to the user VA and runs **SRET from M** into U.
7. **The test** runs in U at low VAs. Pass or fail is reported by `ecall` (cause 8, delegated).
8. **The S handler**, for page faults 12/13/15:
   - **No PTE**: map a free page with `V|U|R|W|X|A|D`, `sfence.vma addr`, copy the page **with
     `sstatus.SUM` set** (S accessing a U page), rewrite the PTE **without A/D**,
     `sfence.vma addr`, `fence.i`.
   - **PTE present, A = 0**: set A.
   - **Otherwise**: assert a store with D = 0 and set D, then `sfence.vma addr`.

   So vm.c expects Svade and also works with hardware A/D. Under Svade, `rv64ui-v-sw` takes 7 traps
   (4 with hardware A/D).
9. **Exit**:
   - `evict` all pages, asserting A, and D if the page changed;
   - `terminate(n)`: an S-mode store to `tohost` through VA `0xFFFFFFFFFFE01000` = PA `0x80001000`.
     **HTIF must match on the PA.**
   - An illegal instruction is the FP-absent probe (exit 1 = pass); any other trap is an assert
     failure (exit 3).
10. **Not used**: ASIDs, G, MXR, `mideleg`, interrupts. SFENCE.VMA always has rs1 ≠ x0 and rs2 = x0.

### 4.4 Corpus expectations after WP7

The task text said 109 `-v` tests. `ls corpus/riscv-tests | grep -- -v-` gives **110** rv64 tests in
the scalar suites (ui 54, um 13, ua 19, uf 11, ud 12, uc 1), of which 109 are expected to pass
(R6).

| Suite | n | sail with the §4.2 cfg | L3 after WP7: riscv-sim | compare | Expected failures |
|---|---|---|---|---|---|
| `rv64u{i,m,a,f,d,c}-p-*` | 110 | 109 | 109 | agree on 110 | `rv64ui-p-ma_data` (misaligned traps, [D55]) |
| `rv64u{i,m,a,f,d,c}-v-*` | 110 | 109 | **109** | **agree on 110** (stage 2: 109, see the note below) | `rv64ui-v-ma_data`: the misaligned trap is not delegated and goes to `wtf` (exit 841), as on sail |
| `rv64si-p-*` | 7 | 7 | **7** (`dirty` and `icache-alias` move from fail/diverge to pass/agree) | agree on 7 | none |
| `rv64mi-p-*` | 17 | 16 | 16 | agree on 17 | `breakpoint` (Sdtrig) |
| `rv64ssvnapot-p-napot` | 1 | pass (store page fault in M; the test accepts Svnapot being absent) | pass | agree | none |
| other `rv64*-p-*` rows of `tests/corpus.expected` (Zb*, Zfh, Zicbo, …) | | unchanged | unchanged | unchanged | as recorded |
| arch tests S/Sv, prebuilt for `sail-rv64-max` | ~180 | fail at `vsetvli` (§4.5) | — | not useful | all |

The 110 `-v` tests are the main WP7 acceptance suite. They cover MRET/SRET into S and U, `medeleg`
8/12/13/15, `stvec`/`sscratch`/`sepc`/`scause`/`stval`, SUM, SFENCE.VMA, Sv39 4 KiB pages and a
2 MiB superpage, Svade faults, and HTIF from S through a VA.

*Stage 2 note on `rv64ui-v-ma_data`.* The row above is wrong in two ways. The model and sail agree on
the first 2787 steps: the misaligned load traps (4), is not delegated, and goes to M-mode, whose
`trap_vector` jumps to `wtf`. But `wtf` runs with U-mode's `sp`, which is 0, and its first store,
`sd ra, 8(sp)` to 0xfffffffffffffff8, is outside sail's memory map, so sail raises a store access
fault there and loops until it reports "possible trap loop detected" (the scratch result
`tlbcmp-results.txt`, rc 1 after 2824 steps, is this loop). The model has no PMA ([D54], Q9), so it
stores and reaches `terminate(841)`: `tohost` = 841, which HTIF reports as exit code 420. So the
riscv-sim outcome is "fail: test 420", and compare diverges at step 2787, the store. 109 of the
110 agree. The corpus also has 63 `-v` tests of the other extensions (`rv64uzba` … `rv64uzicond`,
`rv64uziccid`), which the table leaves out: 2 pass, the others fail with exit code 420 like
`ma_data`, and the 17 whose illegal instruction is in U-mode (`uzbc`, `uzbkx`, `uzfh`, `uzicond`)
diverge at the same store of `wtf`; in `uzba`, `uzbb`, `uzbkb` and `uzbs` `vm.c` itself runs the
instruction in M-mode with its own stack, and they agree. `tests/corpus.expected` records all 173.

Harness changes this needs:
- `corpus.py` derives the suite name with `name.split("-p-")` (`:86`), so it must also split on
  `-v-`;
- `DEFAULT_PATTERN` (`:56`) and the header of `corpus.expected` (`rv64*-p-*`) must widen to
  `rv64*-[pv]-*`.

### 4.5 Arch tests: the prebuilt ELFs are not usable (resolution R5)

All 367 ELFs under `corpus/riscv-arch-tests/sail-rv64-max/elfs/priv/` execute `vsetvli` unguarded in
`rvtest_init_regs`. Without V, sail itself fails with "Mismatch in trap signature … XTVAL
0x0d0070d7" and writes no signature. This was checked on `pmps_cfg_A_off.elf` and on an rv64i ELF as
well.

The directories that would exercise WP7:
- `Sv` (97);
- `SvPMP` (12), `Svade` (6), `Svbare` (3), `Ssccptr` (1);
- `ExceptionsS`, `ExceptionsSv`, `ExceptionsSvZaamo`, `ExceptionsSvZalrsc`;
- `InterruptsS`, `InterruptsSSm`, `S` (2), `SsstrictS*`, `Sstvala`, `Sstvecd`, `ZicntrS`, `Ssu64xl`.

As a diagnostic only, sail with the §4.2 cfg **plus V** gives:

| Directory | Pass | Failures |
|---|---|---|
| Sv | 61/97 with Sv57 off; 91/97 with Sv57 on | the rest: the sv57 tests when Sv57 is off, plus 4 that expect max-config behaviour (`sv{39,48}_pte_reserved_field_Smode`, `sv{39,48}_svnapot_not_supported_Smode`, which expect no trap on bits 63:54) |
| SvPMP | 8/12 with Sv57 off; 12/12 with it on | sv57 |
| Svade | 4/6 with Sv57 off; 6/6 with it on | sv57 |
| Svbare | 3/3 | |
| Ssccptr, Sstvecd, Ssu64xl | 1/1 each | |
| S | 1/2 | `S_scsr` expects the Sscofpmf `sie` mask 0x2222 |
| ExceptionsS*, Sstvala | 0 | they expect misaligned accesses to succeed |
| InterruptsS*, ZicntrS, SsstrictS, Svinval, Svnapot, Svpbmt, Svadu, SvaduPMP | 0 | config-dependent expectations, or the feature is absent |

The translation and S-mode-execution reports listed arch-test directories as oracle-relevant and used
the `InterruptsS` `wfi_timeout_s_*` coverpoints as support for [S20]. As prebuilt, these tests
cannot serve as differential tests: both emulators stop at `vsetvli`. [S20] rests on P p.37 and p.62
alone. Arch tests become acceptance tests only after being rebuilt for this config ([S31]).

The same finding questions the WP2 plan's record of "87/87 PMP and 122/122 rv64i arch-test
signatures equal" (§6, Q1).

### 4.6 Trace format, `compare.py` and the harness

1. **Addresses.**
   - sail prints `pc` as a VA, `mem[R|W,…]` and fetch `mem[X,…]` as **PAs**, and `tval`/`stval` as
     VAs. For example, `sd x1,8(x2)` at VA `0xFFFFFFFFFFE0CEE8` logs `mem[W,0x8000CEE8]`.
   - The model's `recordLoad`/`recordStore` must carry the PA (§3.12) [S30].
   - The `sim/README.md` sentence "Addresses are those that the store or load computed" changes
     to say they are physical addresses.
2. **PTE reads.**
   - They are plain `mem[R,PA]` lines, and their number depends on sail's TLB.
   - Add `--trace-ptw` to `SAIL_TRACE_FLAGS`. In the normaliser, classify `mem[R]` lines between
     `PTW: Start` and `PTW: Step|Failed` as PTE reads, and drop them (or keep them in a field that
     is never compared).
   - Ignore `PTW:` lines. Never pass `--trace-tlb`: its box-drawing table would be "not
     understood".
   - Neither a canonical-address fault nor a Svade A/D fault prints a PTW failure line. The A/D case
     shows `PTW: Success` followed by the trap.
   - The model does not emit PTE reads ([S6]). If they are ever wanted, the harness recomputes them
     outside `translateAddr`.
3. **PTE writes** exist only with hardware A/D. Svade removes them.
4. **Traps.**
   - `trap=12/13/15` with `tval` = VA, taken into S when delegated. sail logs `scause`, `stval`,
     `sepc` and `mstatus`, so the model must report `stval`.
   - PTE PMP faults give 1/5/7.
   - A failed fetch has no `[n]` line. `compare.py` already takes the pc from `sepc` when `mepc` is
     absent; for a translated fetch it is a VA.
   - `S_TRAPPING` already accepts `from U to S`.
5. **CSRs**: add `satp` (logged as `CSR satp (0x180)`) and `menvcfg` to the watch list. The
   `sstatus` view logic is as today. *Stage 2 note:* nothing to add: riscv-sim already watches every
   CSR that `is_CSR_defined` accepts, `satp` and `menvcfg` included, and `compare.py` compares every
   CSR that either side logs.
6. **Harness** (`sim.sml`):
   - `htifStore` (`:507-556`) must match `tohost` on the **PA** of the store;
   - symbols and the signature dump are physical;
   - **the harness has no PMA**: sail faults on accesses outside its regions (ROM `0x1000`+4K,
     CLINT/IO `0x2000000`+256M, DRAM `0x80000000`+2G) and on PTE reads from IO regions. No test in
     §4.4 depends on this (§6, Q9).
7. SFENCE.VMA stays a retiring instruction with legality checks and no state change. The `-v` tests
   execute it in M and in S.

### 4.7 WP2 code that already matches 1.13 and sail

Nothing in this list needs changing for WP7, apart from the comments noted.

| Item | L3 n | Matches |
|---|---|---|
| `sstatus` read view and write through `legalize_mstatus` | 459-471; CSRMap 1021, 1109 | yes, once E1 is in |
| `stvec` legaliser and vectoring | 475-476, 1536-1541; 1023, 1112 | yes |
| `sie`/`sip` views, `read_mip`, `sip` RMW base | 1022, 1032, 1110-1111, 1124-1125; 750-758; 4328-4345 | yes (add a comment, [S21]) |
| `scounteren` and counter gating | 762-771, 994-1001; 1024, 1114 | yes |
| `sscratch`, `sepc`, `scause`, `stval` | 481, 494-495, 729-730; 1028-1031, 1120-1123 | yes |
| `senvcfg` (FIOM writable) | 1025, 1116 | yes |
| `satp` access under TVM | 994-1001 | yes (only the legaliser changes) |
| `medeleg`/`mideleg` masks | 1135-1136 | yes |
| `excDest` | 1500-1502 | yes |
| `highestInterrupt`, `checkInterrupts`, interrupts at step start | 1505-1534; `Next` 5281-5290 | yes |
| `takeTrap` into S or M | 1545-1575 | yes |
| SRET legality and effects; MRET to S | 4291-4298, 1592-1601; 1581-1590 | yes |
| ECALL from S | 1488-1496, 4270 | yes |
| SFENCE.VMA legality | 4390-4396 | yes (comment E3) |
| `effectivePrivilege` | 744-745 | yes |
| `pmpCheck(pa, n, kind, p) -> bool` | 1823-1857 | yes, as the PTE-read check |
| `ExceptionType` page-fault constructors and codes | 214-249 | yes |
| two-parcel `Fetch()` with per-parcel `tval` | 4431-4458 | yes (only the patterns change) |

---

## 5. Decisions

Recommendations are for this model: M/S/U, RV64 only, 16 PMP entries with G = 0, no H, HOL-friendly.
The source column names the reports' items: T = translation, DS = S-mode execution, C = consumers,
O = sail and corpus.

| # | Topic (spec) | Options | Recommendation | Rationale | sail default | From |
|---|---|---|---|---|---|---|
| S1 | How `translateAddr` learns the privilege (P §3.1.6.4 p.35, §12.1.11 p.126) | (a) explicit parameter `p`, computed once in `fetchAddr` (`curPrivilege`) and `dataAddr` (`effectivePrivilege`), with `p == Machine` tested first; (b) computed inside from `ft`; (c) read `satp.MODE` first and add H7 to every M-mode theorem | **(a)** | `translateAddr_Machine` holds with no hypotheses; the same `p` goes to `pmpCheck`; no `c_SCSR` term on the M path; mirrors sail; (c) is not required by the spec and touches every consumer | (a): `translateAddr(gva, access, p)`, `vmem.sail:697` | T8, DS3, C1 |
| S2 | Result type of `translateAddr`/`fetchAddr`/`dataAddr` (P §12.3.2 p.134, Table 16 p.50) | (a) `pAddr option`; (b) `TransResult {TR_Address :: pAddr, TR_Fault :: ExceptionType}` for all three, plus an internal `walkResult`; (c) a three-valued `transResult` plus a separate `memResult`; (d) callers re-run the walk to classify | **(b)** | the caller must tell page faults from access faults; one datatype for `datatype_rwts`; call sites stop choosing the code; patterns-only change in `Fetch_def` and the lemmas | `TR_Result = result(…, ExceptionContext)` | T7, C2 |
| S3 | A/D-bit policy (P §12.3.1 p.132, §12.3.2 step 9, §12.10 p.144) | (a) Svade only, ADUE RO0; (b) Svade + Svadu, ADUE writable; (c) unconditional hardware update | **(a)**; cfg Svade = true, Svadu = false | translation only reads state, so the HOL export keeps its shape; no PTE stores, PMP write check or extra `mw`; vm.c and `rv64si-p-dirty` set A/D in software; costs the Svadu arch tests | Svade + Svadu (ADUE resets 0) | T1, C3, O |
| S4 | Address-translation cache (P §12.3.2 p.135, §12.2.1 p.128) | (a) none: SFENCE.VMA is a legality-checked no-op; (b) a TLB like sail's; (c) an abstract nondeterministic cache | **(a)** | spec allows no cache; no hidden state; traces equal stock sail on 118/118 runs once PTE reads are excluded (§4.1) | always-on 64-entry TLB | T4, DS5, C4, O |
| S5 | Termination of the walk | (a) unrolled into five `ptwStep` calls with literal levels; (b) recursive with a level measure; (c) a loop | **(a)** | no termination proof in the export (the WP7 risk); same style as `pmpCheck`; reduces under EVAL | recursive `pt_walk` | T16, C5 |
| S6 | PTE reads in the log and trace | (a) read through `MEM`, no `mark_log`; compare.py drops PTE reads using `--trace-ptw`; (b) log inside the walk | **(a)** | logging would make `translateAddr` state-passing; sail's PTE-read count depends on its TLB anyway | printed as `mem[R]` (and `PTW:` with the flag) | T9, C3, O |
| S7 | Supported modes (Table 40 p.126; p.137-139) | (a) Sv39; (b) Sv39 + Sv48; (c) Sv39 + Sv48 + Sv57 | **(c)**, MODE ∈ {0, 8, 9, 10} | one MODE case and one `ptwStep`; no riscv-test uses Sv48 *or* Sv57 (vm.c is Sv39), so both rely on rebuilt arch tests anyway; sail passes the sv57 arch tests with it on; dropping it later is one legaliser line (R4) | all three on RV64 | T2, O |
| S8 | ASIDLEN (p.125) | 0..16 | **16** | ASID is plain storage with no TLB; `satp` reads match sail; no mask | 16 | T3, O |
| S9 | PABITS | 13..64 for sail; 56 is the maximum for Sv39 and up | **56** | no PPN masking; vm.c's PMP covers 2^56 | 56 | O, [D32] |
| S10 | `legalize_satp` form; Bare with nonzero ASID/PPN (p.125) | (a) store `v` when MODE ∈ {0, 8, 9, 10}, else keep `old`; (b) store 0 for Bare | **(a)**, written as a mask comparison on `v && 0xF000…` | the mandated write-ignore; matches sail; liftable by `riscv_csr_conv` (R9) | stores `v` (`sys_regs.sail:1243`) | T5, C6 |
| S11 | Reserved MODE values in an arbitrary HOL state | (a) act as Bare; (b) page fault; (c) `#UNDEFINED` | **(a)** | total (F2); `translateAddr_Bare` needs only MODE = 0; unreachable | `internal_error` | T6 |
| S12 | Svnapot, Svpbmt, Svrsw60t59b, Svinval, Svukte; non-leaf D/A/U (p.133, p.137, p.145) | implement them, or leave them absent | **absent**: PTE bits 63:54 ≠ 0 give a page fault, a non-leaf PTE with D/A/U gives a page fault, `menvcfg.PBMTE` RO0 | spec default for reserved bits; one mask each; `rv64ssvnapot-p-napot` passes on the fault path | all supported | T12, T13, O |
| S13 | Ssccptr, Svvptc | advertise or not | **Ssccptr true, Svvptc false** in the cfg | both hold by construction; Ssccptr enables `Ssccptr-00`; Svvptc changes only the ISA string | both true | T12, O |
| S14 | PMP and PMA on PTE reads (P §3.7.1 p.70, §3.7.2 p.74) | (a) PMP R at S, access fault of the original type with `tval` = VA, no PMA; (b) original privilege; (c) sail's PMA regions | **(a)** | spec; matches sail and `sv39_pmp_on_pte_Smode`; the model has no PMA ([D54]) | PMP at S + `supports_pte_read` | T17, O |
| S15 | Misaligned versus translation order (Table 17 p.51) | (a) 4/6 before translation; (b) after | **(a)** ([D55]) | allowed; no page-crossing data accesses | allows misaligned accesses, splitting at pages (the cfg makes them trap) | T14, O |
| S16 | Fetch translation granularity | per 2-byte parcel, or per 4-byte word (Ziccif) | **per parcel** ([D59]) | the existing `Fetch()`; `tval = pc + 2` for the upper parcel; the cfg has Ziccif off | Ziccif on: one 4-byte access | O, T |
| S17 | LR/SC reservation address (P §12.3.1 p.133) | (a) VA (as today); (b) PA | **(b)** | reservations are physical; matches sail; equals the VA in M | PA | T10, DS |
| S18 | SC with a failing reservation | (a) translate and PMP-check anyway, then fail; (b) fail first | **(a)**, extending [D60] | matches sail; under Svade only exceptions are observable | (a) | T11 |
| S19 | `mstatus.SUM` (P §3.1.6.4 p.35, §12.1.1.2 p.114) | (a) writable: `MSTATUS_WMASK = 0x7E79AA`, `sstatus` write mask `0xC6122`; (b) RO0 | **(a), in the same commit as `legalize_satp`** (stage 2) | RO0 is mandated iff `satp.MODE` is read-only 0, in both directions (R15); reverses half of [D21] | follows `virtual_memory_supported()` | T18, DS2 |
| S20 | WFI in S with TW = 1 (p.37, p.62), revising [D23] | (a) always illegal; (b) illegal iff `mip_eff && mie = 0`, else NOP; (c) NOP | **(b)**; cfg `wfi_is_nop = false`, `max_time_to_wait = 0` | a zero time limit, plus wake-on-locally-enabled; exact agreement with sail; M arm unchanged | `wfi_is_nop = false`, `max_time_to_wait = 10` | DS1 |
| S21 | `sip` RMW base (P §3.1.9 p.45) | (a) leave as is; (b) also special-case 0x144 | **(a)**, with a comment | SEIP is read-only in `sip`, so the difference is not observable | special-cases both | DS4 |
| S22 | `medeleg`/`mideleg` masks | (a) `0xB3FF`/`0x222` ([D40], [D41]); (b) add 18/19; (c) delegate M-level interrupts | **(a)** | 18/19 are never raised (p.43); no test needs (c) | `0xCB3FF`/`0x222` effective | DS6 |
| S23 | When interrupts are evaluated (p.117) | (a) start of every step ([D38]); (b) after each instruction | **(a)** | satisfies "immediately after SRET/CSR write"; matches `try_step` | (a) | DS7 |
| S24 | `scause` WLRL set (p.120) | (a) [D33]; (b) only the codes raised | **(a)** | bit-identical to sail | (a) | DS8 |
| S25 | `senvcfg`/`menvcfg.FIOM` (p.123, p.54) | writable or RO0 | **writable** (as now) | RO0 is allowed only while `satp.MODE` is read-only 0 | writable | DS9 |
| S26 | Harness "left validated scope" flag for S-mode entry (WP2 open question 12) | drop it, or keep it until Sv48 is validated | **drop** | S-mode is in scope; divergences are regressions or noted in `corpus.expected` | n/a | DS10 |
| S27 | Where `satp` lives | (a) `regType` in `SupervisorCSR`; (b) an L3 register type with fields; (c) move to `MachineCSR` | **(a)** | smallest change; a word slice lifts directly | a plain register with bitfield views | T15 |
| S28 | `prog` visibility of `c_SCSR` | (a) keep hidden, `riscv_ID` unchanged; (b) un-hide; (c) a `satp` component | **(a)** | no step theorem reads `c_SCSR` under S1; there are no U-mode step theorems in the contract (R3) | n/a | C7 vs T15 |
| S29 | HolBA and `satp` | (a) lift `satp` as a 64-bit variable, no assertion, not in `riscv_state_is_OK`; (b) leave it unlifted | **(a)** | sound either way; lets a kernel state "satp is Bare at `mret`"; costs one `BMLI`, one `bmr_rel` conjunct, two selftest cases | n/a | C6 |
| S30 | Trace and HTIF addresses | VA or PA for `mr`/`mw` and `tohost` | **PA**; `pc` and `tval` stay VAs | sail logs PAs; vm.c writes `tohost` through a VA | PA | O |
| S31 | Arch-test corpus | (a) rebuild the priv suite for this cfg (no V, Svade, misaligned trapping); (b) run the prebuilt ELFs in sail with V as a cfg sanity check; (c) prebuilt ELFs differentially | **(a)** for acceptance, **(b)** meanwhile | the prebuilt ELFs stop at `vsetvli` on both emulators (§4.5) | n/a | O |

That is **31 decisions**. They revise [D5] (by S1 and S2), [D21] (S19), [D23] (S20), [D32] (S10) and
[D46] (S4: the reason changes to "no cache", and the cfg knob becomes moot).

### 5.1 Contradictions resolved

| # | Contradiction | Resolution | Deciding source |
|---|---|---|---|
| R1 | Translation report: `translateAddr` computes the privilege internally (T8). Consumers and S-mode reports: explicit parameter (C1, DS3) | explicit parameter (S1) | Both are equivalent under P §3.1.6.4 p.35. §1.3 decides: with an explicit `p`, `translateAddr_Machine` needs no hypotheses, and `p` is shared with `pmpCheck`. sail `vmem.sail:697` does the same |
| R2 | `transResult` + `memResult` (T7) versus a single `TransResult` with `ExceptionType` (C2) | single external type; the page/access distinction stays inside `walkResult` (S2) | P §12.3.2 p.134 needs only that the caller can tell them apart. §1.4: one type to add to `datatype_rwts`, and the lemmas change in patterns only |
| R3 | Translation report: `prog`/HolBA must expose `c_SCSR` and H7 for "U-mode step theorems (S3K)" (T.9.4, T15). Consumers report: keep it hidden | keep it hidden; `translateAddr_Bare` is proved but not added to the contract (S28) | `riscv_stepLib.sml:422-431` `contract_hyps` has H1 (`c_privilege = 3w`): there are no U-mode step theorems. S3K's kernel runs in M (§1.5, §1.6) |
| R4 | Sv57 in the first cut (T2) or not (sail and corpus report) | include it (S7) | P §12.6 p.138-139 is the same algorithm with LEVELS = 5. §4.3: vm.c uses only Sv39, so Sv48 and Sv57 alike are validated only by rebuilt arch tests, where Sv57 passes in sail. Confirm with the user (§6, Q2) |
| R5 | Translation and S-mode reports list priv arch tests as oracle tests and as support for DS1 | not usable as prebuilt; they need a rebuild (S31) | sail and corpus §4.5 finding: unguarded `vsetvli` |
| R6 | "109" `-v` tests (task) versus 110 | 110 tests, 109 pass | `ls` of the corpus (§4.4) |
| R7 | 42 `dataAddr` call sites (translation report) versus 37 (consumers report) | 37 (11 + 8 + 18) | `grep` of `riscv.spec` at `37a5d7e9a` |
| R8 | The sail-and-corpus cfg hunk keeps `wfi_is_nop` as is; DS1 changes it | the merged hunk has `wfi_is_nop = false`, `max_time_to_wait = 0` (§4.2); re-run the oracle | S20, P p.37 and p.62 |
| R9 | `legalize_satp` as `match v<63:60>` (T.2.3) versus a mask comparison (C6) | mask comparison | equivalent semantics; the HolBA lifter (§1.6) decides |
| R10 | Svvptc "either" (T12) versus false (sail and corpus report) | false (S13) | no behaviour either way; keep the ISA string minimal |
| R11 | The S-mode report's change C4 writes the body as `Some(vAddr)` | superseded by S2 | §3.11 |
| R12 | AMO permission: `W` (translation report) versus sail's `W ∧ R'` | not a real conflict: equal after step 6(b) | Table 41 p.131 |
| R13 | Fetch: "sail's single 4-byte Ziccif fetch" (T.8) versus "Ziccif off, per parcel" (sail and corpus report) | per parcel; the cfg has Ziccif off, and both give the same verdicts when `pc` is 4-aligned | cfg; [D59] |
| R14 | `InterruptsS` coverpoints cited for DS1 | DS1 stands on the spec text only | R5 |
| R15 | The S-mode report puts SUM writability (change C1) first, without a stage | SUM changes in the same commit as `legalize_satp` and the cfg `Sv39` flip, in stage 2 | P §3.1.6.4 p.35, §12.1.1.2 p.114: "SUM is read-only 0 if … satp.MODE is read-only 0" |

---

## 6. Open questions

1. **WP2 arch-test claim.** The plan records "87/87 PMP and 122/122 rv64i arch-test signatures equal
   sail's". With the base cfg every prebuilt arch test stops at `vsetvli` in sail, which then writes
   no signature. How were those signatures produced? If both emulators stopped at the same trap, the
   agreement says nothing about PMP.
2. **Sv57** (S7): approve including it, or stop at Sv39 + Sv48 (a one-line legaliser change and
   `Sv57: false`)?
3. **A/D policy** (S3): approve Svade only? Svadu would make `translateAddr` state-passing and every
   memory step theorem thread state. It is a later add-on if HolBA or S3K ever want it.
4. **Arch-test rebuild** (S31): rebuild the riscv-arch-test priv suite for this config (no V, Svade,
   misaligned trapping, Sv39/Sv48/Sv57)? Without it, the S/Sv acceptance suites are the 110 `-v` and
   7 `rv64si-p` tests and the hand-written tests of §7. Which rebuilt tests remain feature-absent
   failures (for example `sv*_svpbmt_*`, `sv*_svnapot_*`, Svadu)?
5. **Sv48 coverage from riscv-tests**: rebuild the `-v` suite with `-DSv48` (and Sv57 if
   supported) from the riscv-tests source, to get the same 110 tests under 4- and 5-level tables?
   This needs a riscv-tests clone; the env source is in scratch `sail-oracle/dl-env/`. *Stage 2:*
   not done. A shallow clone of riscv-tests (3df703c, env 6de71ed) was made, but running its build
   was refused by the permission system of the session that implemented stage 2. Sv48 and Sv57
   are covered by `sim/tests/sv48.S` and `sv57.S` instead.
6. **SFENCE.VMA and sail's TLB** (S4): accept and document divergences for software that omits a
   required fence, or keep using the `notlb` sail build for such tests? None is known in the
   current corpus. *Stage 2:* against the `notlb` build the 173 `-v` tests give the same outcomes
   and the same first divergent steps as against stock sail, and `sv39.S`, `sv48.S` and `sv57.S`,
   which run SFENCE.VMA after every change of `satp`, a PTE or the PMP, agree with both.
7. **WFI cfg** (S20): confirm on a sail run that `wfi_is_nop = false` with `max_time_to_wait = 0`
   gives exactly one `mtime` tick per WFI, and that `compare.py` merges the wait block. Then re-run
   `make compare-corpus` for `rv64si-p-wfi`, `rv64mi-*` and the S3K traces.
8. **External interrupts**: the `InterruptsS*` SEI/MEI coverpoints need an interrupt generator. The
   cfg disables it ([D73]) and the harness keeps `c_extSEIP`/`c_extMEIP` false. Should those
   coverpoints be expected failures on both models, or should the harness drive the lines?
9. **PMA**: the harness has no PMA ([D54]). Add sail's three regions, or record PMA-dependent tests
   as expected divergences? Physical addresses ≥ 2^56 under Bare or M stay memory; no change is
   recommended.
10. **Trace PTE reads** (S6): drop them in the normaliser, or keep a never-compared field? Decide
    before the `-v` suite becomes the stage 2 gate.
11. **HolBA `satp` lifting** (S29) in WP7, or later? Both are sound for M-mode code.
12. **S3K / kernel postcondition**: should the verification eventually state "`satp.MODE` = Bare at
    every `mret` to U"? This is the reason to lift `satp`.
13. **Interface change** (S2): accept the patterns-only edit of the 37 call sites and of `Fetch_def`?
    The alternative keeps `Fetch_def` byte-identical but runs the walk twice on a fault.
14. **CakeML timing**: the `mstatus` record gains `SUM` (S19). Coordinate with the WP6 window that
    rewrites `riscv_ok`.
15. **L3 syntax checks** (§3.11): does L3 accept the catch-all `case f => f` on `TransResult`, and
    reading the `MEM` component inside a pure function? Fallbacks are given in §3.11. *Answered in
    stage 2:* yes to both (§3.11, stage 2 notes).
16. **riscv-test-env version**: the tag behind the prebuilt `sail-riscv-tests 2026-08-20` ELFs is
    unknown. Master of 2026-01-09 matches the observed behaviour.

---

## 7. Staged implementation plan for WP7

The work goes on branch `riscv-l3-smode` (worktree `~/Documents/HOL-fixes-smode`), with one commit
per stage step. The rollback points are tags `riscv-l3-before-smode` (HOL-fixes) and the
corresponding tag on `riscv_priv113` (HolBA). At every stage `src/Makefile hol` and `sml`
regenerate the model, and `model/riscvScript.sml` builds under both HOL develop and
`trindemossen-2`.

"Gate" below means: `make corpus` (riscv-sim against `tests/corpus.expected`) **and**
`make compare-corpus` (`compare.py` against sail with the stage's cfg) report no outcome that differs
from the expected file, plus the stage's named tests. `make corpus-update` may change only the rows
the stage names, and each changed row gets a note.

### Stage 1: S-mode execution, translation still Bare only

- **L3**:
  - E2 (WFI, §2.11);
  - E3 (SFENCE.VMA comment);
  - the `sip` RMW comment ([S21]);
  - a comment on the `Next` and trap paths that S-mode is validated.

  `legalize_satp`, `translateAddr`, `MSTATUS_WMASK` and the SUM field are **not** touched (R15).
- **cfg**: the `platform` lines of §4.2 only.
- **Harness**: drop the "left validated scope" flag ([S26]). Add a hand-written test
  `sim/tests/smode.S`, with a `.sig.expected` file from sail, since the arch tests cannot run. It
  checks:
  - MRET into S, ECALL from S taken in M and, delegated, in S;
  - `medeleg`/`mideleg` writes; `sie`/`sip` through `mideleg`; SSIP set by M and taken in S with
    `stvec` Direct and Vectored;
  - SRET to U and to S, SRET in S with TSR = 1, SRET in M with TSR = 1;
  - WFI in S with TW = 1, with and without a pending `sie`-enabled SSIP and `SIE = 0`;
  - `scounteren`/`mcounteren` gating from S and U;
  - `scause` WLRL writes; `stval` for an illegal instruction in S;
  - `satp` access with TVM = 1.
- **Docs**: amend `design-privileged.md` §2.3.7, §4.7.6, §4.7.7, [D23] and [D46] (§4.7.7 gets the
  "no cache" reason only when stage 2 lands), and close open questions 12 and 22.
- **Acceptance**:
  - The gate passes with **no** row of `corpus.expected` changed. In particular `rv64si-p-csr`,
    `-ma_fetch`, `-sbreak`, `-scall` and `-wfi` pass and agree, and `dirty`/`icache-alias` keep
    their "needs Sv39" rows.
  - `compare.py` reports agreement on `sim/tests/smode.S` and `sim/tests/int.S`, and the signature
    matches.
  - The S3K traces agree as before.
  - `step/` builds unchanged and `selftest` passes (M-mode theorems unaffected).

### Stage 2: Sv39/Sv48/Sv57 translation and page faults

- **L3, in one commit**:
  - `TransResult` and `walkResult`; `pageFault`, `accessFault`, `ptePermits`, `ptwLevel`, `ptwStep`;
    the new `translateAddr`, `fetchAddr` and `dataAddr` (§3.11);
  - `legalize_satp` (§3.2.3);
  - E1 (SUM field and `MSTATUS_WMASK = 0x7E79AA`);
  - the 37 call sites and `Fetch`/`FETCH_FAULT` (§3.12);
  - `recordLoad`/`recordStore` with the PA;
  - `ReserveLoad` with the PA (S17).
- **cfg**: the `extensions` and `memory` lines of §4.2, then re-validate.
- **Harness**:
  - `htifStore` matches the PA;
  - `corpus.py` handles `-v-` suites and the pattern `rv64*-[pv]-*`;
  - `compare.py`: add `--trace-ptw` to `SAIL_TRACE_FLAGS`, drop PTE reads and `PTW:` lines, add
    `satp`/`menvcfg` to the CSR watch list;
  - README: addresses are physical.
- **Hand-written tests** (`sim/tests/`), because no riscv-test uses Sv48 or Sv57 or exercises these
  cases:
  - `sv48.S` and `sv57.S`: 4 KiB, 2 MiB and 1 GiB leaves (512 GiB for Sv48/57); a non-canonical VA;
  - a misaligned superpage; a pointer PTE at level 0; a non-leaf PTE with D/A/U; reserved bits 63:54;
  - U/SUM for loads and fetches; MXR; MPRV with MPP = S and with MPP = U;
  - a PMP-denied PTE read (expect 5/7/1 in M with `tval` = VA);
  - a 32-bit instruction straddling a page whose second page is unmapped (`tval = pc + 2`);
  - `satp` writes with reserved MODEs (ignored).
- **Acceptance**:
  - The gate on `rv64*-[pv]-*` gives:
    - **`rv64u{i,m,a,f,d,c}-v-*`: 109 pass, `rv64ui-v-ma_data` fails with exit 841 as on sail;
      compare agrees on all 110** (traces normalised, PTE reads excluded);
    - `rv64si-p-*`: 7/7 pass and agree (`dirty` and `icache-alias` rows change to pass/agree);
    - `rv64ssvnapot-p-napot`: its row changes to pass/agree;
    - every other `-p` row is unchanged.
  - The new hand-written tests agree with sail, and their signatures match.
  - Optionally (§6, Q5): the `-v` suite rebuilt with `-DSv48` gives the same 109/110.
  - Cross-check with the `notlb` sail build on the `-v` suite: same verdicts.
  - `model/riscvScript.sml` builds with no termination goal and no `#UNDEFINED` on the
    `translateAddr` path.
  - `step/` may be red until stage 3; land stages 2 and 3 together if the branch must stay green.

### Stage 3: step library, `prog`, decompiler

- **`riscv_stepScript.sml`**: the edits of §1.4:
  - the lemmas `translateAddr_Machine`, `effectivePrivilege_Machine`, `translateAddr_Bare`;
  - `fetchAddr_Machine`/`dataAddr_Machine` reproved;
  - `Fetch_def` patterns;
  - delete the `translateAddr` EV;
  - `datatype_rwts`, `bad`.
- **`selftest.sml`**: the edits of §1.8 (`bad_consts`, the new edge cases, the `mstatus` mask, and
  the `c_SCSR` hypothesis check). The `exact` table stays unchanged.
- **`prog`**: hide list and `riscv_ID` unchanged; rebuild `prog/` and `decompiler/` and run their
  selftests.
- **Acceptance**:
  - `Holmake` in `step/`, `prog/` and `decompiler/` succeeds under develop and `trindemossen-2`;
  - `step/selftest` reports zero `UNEXPECTED` hypotheses and an unchanged `exact` table;
  - no hypothesis of any step theorem mentions `riscv_state_c_SCSR`;
  - the new edge cases (`csrw satp`, `csrwi satp,0`, `sfence.vma`, `csrw sstatus`) pass, and `sret`
    still yields no theorem;
  - `contract_hyps` is unchanged;
  - the stage 2 gate still passes (no spec change in stage 3).

*Stage 3 notes.* The notes in §1.3, §1.4, §1.5 and §1.8 give the details.

- **`trindemossen-2`.** It was checked as in stages 1 and 2, in a scratch copy of `model/`,
  `step/`, `prog/` and `decompiler/`. That copy's Holmakefiles use `trindemossen-2`'s own
  `examples/l3-machine-code/common` and `lib`, in the way HolBA builds the vendored files,
  because this tree's `common/Import.sml` needs develop. `prog/` needed the one change of §1.5.
- **No prog selftest.** `prog/` has none. The decompiler's test is `riscv_decomp_demoScript.sml`,
  and it builds all 16 of its theorems under both versions. Its `test5` to `test7` take loads,
  stores and an AMO through `riscv_spec`.
- **Gate.** The stage 2 gate gives the same results as in stage 2:
  - `make test` passes;
  - `make compare` passes;
  - `make corpus` and `make compare-corpus` both give "all 372 outcomes as in
    `tests/corpus.expected`".
- **Not built.** `examples/machine-code/graph`, which also uses `riscv_progLib`, is in no HOL
  build sequence, and was not built.

### Stage 4: HolBA `satp` lifting

- **Re-vendor** `src/shared/l3-machine-code/riscv` per `VENDORING.md` on a new branch off
  `riscv_priv113`.
- **`bir_lifting_machinesScript.sml`**: the `satp` `BMLI` entry; `riscv_state_is_OK` unchanged.
- **`bir_riscv_extrasScript.sml`**: the SUM field theorems.
- **`bir_riscv_backlifterScript.sml`**: the extra `riscv_bmr_rel` conjunct.
- **`selftest_riscv.sml`**: `csrw satp,t0` and `csrwi satp,0`.
- **README** edits (§1.6).
- **Acceptance**:
  - `make tests` in HolBA passes;
  - the lifter selftest lifts `csrw satp,t0` to an assignment of the legalised value and
    `csrr t0,satp` to a read;
  - `examples/riscv` (including the kernel example with `csrwi satp,0`) and `examples/riscv/s3k`
    rebuild with unchanged proofs and unchanged program variable sets;
  - the backlifter theorems build;
  - CakeML is not touched in WP7 (§1.7). Its `mstatus`-record knock-on is checked when WP6 rebuilds.
