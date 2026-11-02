(* ------------------------------------------------------------------------
   PMP isolation of U-mode steps of the RISC-V L3 model (riscvTheory): the
   theorems (a)-(d) of DESIGN.md §2, stated against the step function Next,
   so that interrupts, exceptions and every instruction are covered.

   (a) Write frame   Next_writes, Next_U_writes, Next_U_writes_byte
   (b) Fetch         Next_U_fetch, Next_U_fetch_fault
   (c) Reads         Next_reads, Next_U_reads, Next_U_secret_unchanged
   (d) Frames        Next_U_frame, Next_U_trap

   The PMP rules are those of the privileged spec, P §3.7 (p.70-74), as the
   model implements them in pmpCheck (design-privileged.md chapter 5,
   [D47]-[D62]); riscv_pmpTheory relates pmpCheck to the bytes of an access
   and to the PMP CSR words.  Address translation is off: the privilege of
   the access is M or satp is Bare (design-smode.md chapter 3).
   ------------------------------------------------------------------------ *)
Theory riscv_isolation
Ancestors
  riscv riscv_footprint riscv_frames riscv_pmp
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()
val ERR = mk_HOL_ERR "riscv_isolationTheory"

val sty = ``:riscv_state``
fun thms_with suffix thy =
  List.mapPartial (fn (n, th) => if String.isSuffix suffix n then SOME th else NONE)
                  (DB.thms thy)
val frame_thms = thms_with "_frame" "riscv_frames"

Theorem UNCURRY_FST_SND[local]:
  !f p. UNCURRY f p = f (FST p) (SND p)
Proof
  Cases_on `p` \\ rw []
QED

val fld_prefix = "recordtype.riscv_state.seldef."
fun sel fld st = mk_comb (prim_mk_const {Name = fld_prefix ^ fld, Thy = "riscv"}, st)
val cond_lemmas =
  map (fn fld =>
         let
           val b = mk_var ("b", bool)
           val x = mk_var ("x", sty)
           val y = mk_var ("y", sty)
           val g = mk_eq (sel fld (mk_cond (b, x, y)), mk_cond (b, sel fld x, sel fld y))
         in
           Q.prove (`^g`, rw [])
         end)
      ["procID", "totalCore", "c_privilege", "c_PC", "c_SCSR", "c_MCSR", "c_fpr",
       "c_UCSR", "c_ReserveLoad", "c_NextFetch", "c_gpr", "MEM8"]

(* ------------------------------------------------------------------------
   The effect of one instruction run in U-mode
   ------------------------------------------------------------------------ *)

Definition fs_dirty_of_def:
  fs_dirty_of (h : word8) (m : word8 -> MachineCSR) =
    (h =+ (m h with mstatus := (m h).mstatus with FS := 3w)) m
End

Definition fs_on_def:
  fs_on s <=> ((s.c_MCSR s.procID).mstatus.FS <> 0w)
End

Definition nf_ok_def:
  (nf_ok NONE = T) /\
  (nf_ok (SOME (BranchTo a)) = T) /\
  (nf_ok (SOME (Trap e)) = T) /\
  (nf_ok (SOME Mret) = F) /\
  (nf_ok (SOME Sret) = F)
End

Definition is_trap_def:
  (is_trap (SOME (Trap e)) = T) /\
  (is_trap (SOME (BranchTo a)) = F) /\
  (is_trap (SOME Mret) = F) /\
  (is_trap (SOME Sret) = F) /\
  (is_trap NONE = F)
End

Definition run_ok_def:
  run_ok lrsc s t <=>
    (t.procID = s.procID) /\ (t.totalCore = s.totalCore) /\
    (t.c_privilege = s.c_privilege) /\ (t.c_PC = s.c_PC) /\ (t.c_SCSR = s.c_SCSR) /\
    ((t.c_MCSR = s.c_MCSR) \/ fs_on s /\ (t.c_MCSR = fs_dirty_of s.procID s.c_MCSR)) /\
    (~fs_on s ==> (t.c_fpr = s.c_fpr) /\ (t.c_UCSR = s.c_UCSR)) /\
    ((t.c_ReserveLoad <> s.c_ReserveLoad) ==> lrsc) /\
    nf_ok (t.c_NextFetch s.procID) /\
    (is_trap (t.c_NextFetch s.procID) ==>
     (t.c_MCSR = s.c_MCSR) /\ (t.MEM8 = s.MEM8))
End

Theorem fs_dirty_of_idem:
  !h m. fs_dirty_of h (fs_dirty_of h m) = fs_dirty_of h m
Proof
  rw [fs_dirty_of_def, combinTheory.UPDATE_EQ, combinTheory.UPDATE_APPLY]
QED

Theorem fs_dirty_of_cond:
  !b h m. fs_dirty_of h (if b then fs_dirty_of h m else m) = fs_dirty_of h m
Proof
  rw [fs_dirty_of_idem]
QED

Theorem write'fcsr_MCSR:
  !v s. (write'fcsr v s).c_MCSR = fs_dirty_of s.procID s.c_MCSR
Proof
  simp [write'fcsr_def, fs_dirty_of_def, ext_status_def]
QED

Theorem setFP_MCSR:
  !s. ((setFP_Invalid () s).c_MCSR = fs_dirty_of s.procID s.c_MCSR) /\
      ((setFP_DivZero () s).c_MCSR = fs_dirty_of s.procID s.c_MCSR) /\
      ((setFP_Overflow () s).c_MCSR = fs_dirty_of s.procID s.c_MCSR) /\
      ((setFP_Underflow () s).c_MCSR = fs_dirty_of s.procID s.c_MCSR) /\
      ((setFP_Inexact () s).c_MCSR = fs_dirty_of s.procID s.c_MCSR)
Proof
  simp [setFP_Invalid_def, setFP_DivZero_def, setFP_Overflow_def,
        setFP_Underflow_def, setFP_Inexact_def, write'fcsr_MCSR]
QED

Theorem accrueFlags_MCSR:
  !f s.
    (accrueFlags f s).c_MCSR =
    if f.InvalidOp \/ f.DivideByZero \/ f.Overflow \/ f.Underflow_AfterRounding \/
       f.Precision
    then fs_dirty_of s.procID s.c_MCSR else s.c_MCSR
Proof
  rpt gen_tac
  \\ simp_tac std_ss [accrueFlags_def, LET_THM]
  \\ rpt (IF_CASES_TAC
          \\ asm_simp_tac (srw_ss()) ([setFP_MCSR, fs_dirty_of_idem] @ frame_thms))
QED

Theorem writeFPR_MCSR:
  !x y s. ((writeFPRS x s).c_MCSR = fs_dirty_of s.procID s.c_MCSR) /\
          ((writeFPRD y s).c_MCSR = fs_dirty_of s.procID s.c_MCSR)
Proof
  rpt gen_tac
  \\ PairCases_on `x`
  \\ PairCases_on `y`
  \\ simp ([writeFPRS_def, writeFPRD_def, write'MCSR_def, MCSR_def, fs_dirty_of_def,
            ext_status_def, write'Delta_def] @ frame_thms)
QED

Theorem write'NextFetch_NextFetch:
  !v s. (write'NextFetch v s).c_NextFetch = (s.procID =+ v) s.c_NextFetch
Proof
  simp [write'NextFetch_def]
QED

val run_thms =
  [run_ok_def, nf_ok_def, is_trap_def, fs_on_def, fpEnabled_def, MCSR_def,
   ext_status_def, write'fcsr_MCSR, setFP_MCSR, accrueFlags_MCSR, writeFPR_MCSR,
   write'NextFetch_NextFetch, setTrap_def, signalException_def,
   signalAddressException_def, signalEnvCall_def, branchTo_def,
   fs_dirty_of_idem, fs_dirty_of_cond, combinTheory.APPLY_UPDATE_THM,
   UNCURRY_FST_SND] @ cond_lemmas @ frame_thms

fun inst_tac def =
  rpt gen_tac
  \\ strip_tac
  \\ simp_tac std_ss [def, LET_THM, UNCURRY_FST_SND]
  \\ rpt (IF_CASES_TAC \\ asm_simp_tac std_ss [])
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss [])
  \\ fs run_thms
  \\ rpt (IF_CASES_TAC \\ fs run_thms)


(* In U-mode the only CSRs that an instruction may access are fflags, frm
   and fcsr (0x001-0x003), only while mstatus.FS is not Off (P §3.1.6.7
   p.38), and cycle, time and instret (0xC00-0xC02), read-only (P §2.1
   p.13: csr[11:10] = 11 is read-only, csr[9:8] is the lowest privilege that
   may access it). *)
Theorem checkCSROp_User:
  !csr f a s.
    (curPrivilege () s = User) /\ checkCSROp (csr, f, a) s ==>
    ((csr = 1w) \/ (csr = 2w) \/ (csr = 3w)) /\ fpEnabled () s \/
    (a = Read) /\ ((csr = 0xC00w) \/ (csr = 0xC01w) \/ (csr = 0xC02w))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `checkCSROp _ _` mp_tac
  \\ asm_simp_tac std_ss [checkCSROp_def, check_CSR_access_def, csrRW_def,
                          csrPR_def, privLevel_def, is_CSR_defined_def,
                          check_CSR_conditions_def]
  \\ qpat_x_assum `curPrivilege () s = User` kall_tac
  \\ Cases_on `fpEnabled () s`
  \\ Cases_on `a`
  \\ asm_simp_tac (srw_ss()) []
  \\ blastLib.BBLAST_TAC
QED

Theorem CSR_U_state:
  !csr s.
    ((csr = 1w) \/ (csr = 2w) \/ (csr = 3w) \/ (csr = 0xC00w) \/
     (csr = 0xC01w) \/ (csr = 0xC02w)) ==>
    (SND (CSR csr s) = s)
Proof
  rw [] \\ simp [CSR_def, CSRMap_def]
QED

(* A write of fflags, frm or fcsr changes fcsr and sets mstatus.FS to
   Dirty (P §3.1.6.7 p.39). *)
Theorem writeCSR_FP:
  !csr v s.
    ((csr = 1w) \/ (csr = 2w) \/ (csr = 3w)) ==>
    ((writeCSR (csr, v) s).c_SCSR = s.c_SCSR) /\
    ((writeCSR (csr, v) s).c_MCSR = fs_dirty_of s.procID s.c_MCSR)
Proof
  rw []
  \\ simp [writeCSR_def, write'CSR_def, write'CSRMap_def, CSR_def, CSRMap_def,
           write'Delta_def, Delta_def, fs_dirty_of_def, ext_status_def, LET_THM]
QED

Theorem accessCSR_U:
  !op rd f src csr s.
    (curPrivilege () s = User) /\ (s.c_NextFetch s.procID = NONE) ==>
    run_ok F s (accessCSR (op, rd, f, src, csr) s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [accessCSR_def, LET_THM, UNCURRY_FST_SND]
  \\ IF_CASES_TAC
  \\ TRY (fs run_thms \\ NO_TAC)
  \\ drule_all checkCSROp_User
  \\ strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ asm_simp_tac std_ss [CSR_U_state]
  \\ IF_CASES_TAC
  \\ fs ([writeCSR_FP] @ run_thms)
QED

(* The load reservation is changed only by LR and SC. *)
Definition lr_sc_def:
  (lr_sc (AMO (LR_W x)) = T) /\ (lr_sc (AMO (LR_D x)) = T) /\
  (lr_sc (AMO (SC_W y)) = T) /\ (lr_sc (AMO (SC_D y)) = T) /\
  (lr_sc _ = F)
End

(* For each instruction definition that Run calls: run in U-mode, it
   changes the control state only as run_ok allows (dfn'X_U). *)
val run_insts =
  let
    val run_def = DB.fetch "riscv" "Run_def"
  in
    Lib.mk_set
      (List.filter (String.isPrefix "dfn'")
         (map (fst o dest_const) (find_terms is_const (concl run_def))))
  end

val lrsc_insts = ["dfn'LR_W", "dfn'LR_D", "dfn'SC_W", "dfn'SC_D"]
val csr_insts =
  ["dfn'CSRRW", "dfn'CSRRS", "dfn'CSRRC", "dfn'CSRRWI", "dfn'CSRRSI", "dfn'CSRRCI"]

fun inst_goal nm =
  let
    val def = DB.fetch "riscv" (nm ^ "_def")
    val l = lhs (snd (strip_forall (concl def)))
    val (c, args) = strip_comb l
    val s = mk_var ("s", sty)
    val app = if type_of l = sty then list_mk_comb (c, butlast args @ [s])
              else list_mk_comb (c, args @ [s])
    val b = if Lib.mem nm lrsc_insts then T else F
    val g = ``(curPrivilege () ^s = User) /\ (^s.c_NextFetch ^s.procID = NONE) ==>
              run_ok ^b ^s ^app``
  in
    (def, list_mk_forall (free_vars g, g))
  end

fun csr_tac def =
  rpt gen_tac
  \\ strip_tac
  \\ simp_tac std_ss [def]
  \\ irule accessCSR_U
  \\ asm_rewrite_tac []

val inst_U_thms =
  map (fn nm =>
         let
           val (def, g) = inst_goal nm
           val tac = if Lib.mem nm csr_insts then csr_tac def else inst_tac def
           val th = Q.prove (`^g`, tac)
                    handle e => (print ("riscv_isolation: no U lemma for " ^ nm ^ "\n");
                                 raise e)
         in
           (nm, save_thm (nm ^ "_U", th))
         end) run_insts

val () =
  print ("riscv_isolation: " ^ Int.toString (length inst_U_thms) ^
         " instruction definitions analysed for U-mode\n")

Theorem run_ok_refl:
  !b s. (s.c_NextFetch s.procID = NONE) ==> run_ok b s s
Proof
  simp [run_ok_def, nf_ok_def, is_trap_def]
QED

fun pair_cases_tac (g as (_, w)) =
  let
    val vs = List.filter (fn v => can pairSyntax.dest_prod (type_of v)) (free_vars w)
  in
    MAP_EVERY (fn v => PairCases_on `^v`) vs g
  end

(* Every instruction run in U-mode, from a state between steps
   (c_NextFetch = NONE), changes the control state only as run_ok allows:
   procID, totalCore, the privilege, the pc, the S-level CSRs are
   unchanged; the M-level CSRs too, except that mstatus.FS may become Dirty
   when it is not Off; the floating-point registers and fcsr are unchanged
   when FS is Off; only LR and SC change the load reservation; the next
   fetch is the following instruction, a branch target or a trap, never an
   MRET or SRET (illegal in U-mode, P §3.3.2 p.61); and an instruction that
   traps leaves the M-level CSRs and memory as they were (P §3.7 p.70:
   "PMP violations are always trapped precisely"). *)
Theorem Run_U:
  !i s.
    (curPrivilege () s = User) /\ (s.c_NextFetch s.procID = NONE) ==>
    run_ok (lr_sc i) s (Run i s)
Proof
  Cases_on `i`
  \\ simp_tac (srw_ss()) [Run_def]
  \\ rpt CASE_TAC
  \\ pair_cases_tac
  \\ simp_tac (srw_ss()) [lr_sc_def]
  \\ rpt strip_tac
  \\ FIRST (map (fn (_, th) => irule th \\ asm_rewrite_tac [] \\ NO_TAC) inst_U_thms @
            [irule run_ok_refl \\ asm_rewrite_tac [] \\ NO_TAC])
QED

(* ------------------------------------------------------------------------
   The step, decomposed
   ------------------------------------------------------------------------ *)

(* Next first clears the log and the flag that minstret was written *)
Definition next_pre_def:
  next_pre s =
    (s with log := []) with c_minstret_written := (s.procID =+ F) s.c_minstret_written
End

(* and last counts the cycle, unless mcountinhibit.CY is set after the
   step (P §3.1.12 p.47, [D63]) *)
Definition cycle_step_def:
  cycle_step t =
    if ~word_bit 0 (t.c_MCSR t.procID).mcountinhibit then
      t with c_cycles := (t.procID =+ t.c_cycles t.procID + 1w) t.c_cycles
    else t
End

(* What Next does after the instruction has run, with the value v0 that
   fetchAndExecute returns (the instruction bits): the NextFetch dispatch *)
Definition next_post_def:
  next_post incIR (v0 : word64, t) =
    case t.c_NextFetch t.procID of
      NONE =>
        write'PC (PC (incrInstret incIR t) + Skip (incrInstret incIR t))
          (incrInstret incIR t)
    | SOME (BranchTo addr) =>
        write'PC addr (write'NextFetch NONE (incrInstret incIR t))
    | SOME Mret => mret () (write'NextFetch NONE (incrInstret incIR t))
    | SOME Sret => sret () (write'NextFetch NONE (incrInstret incIR t))
    | SOME (Trap e) =>
        takeTrap
          (F, excCode e.trap, PC (write'NextFetch NONE t),
           (if e.trap = Illegal_Instr then v0 else e.tval),
           excDest (excCode e.trap, curPrivilege () (write'NextFetch NONE t))
             (write'NextFetch NONE t))
          (write'NextFetch NONE t)
End

Theorem checkInterrupts_next_pre:
  !s. checkInterrupts () (next_pre s) = checkInterrupts () s
Proof
  simp [next_pre_def, checkInterrupts_log, checkInterrupts_minstret]
QED

Theorem Fetch_next_pre:
  !s. Fetch () (next_pre s) =
      (FST (Fetch () s), SND (Fetch () s) with
         <| log := []; c_minstret_written := (s.procID =+ F) s.c_minstret_written |>)
Proof
  simp [next_pre_def, Fetch_log, Fetch_minstret]
QED

(* Next, as clear_logs and the reset of c_minstret_written (next_pre),
   then the trap entry of an interrupt, or the fetch and the instruction
   followed by the NextFetch dispatch (next_post), then the cycle count
   (cycle_step) *)
Theorem Next_split:
  !s. Next s =
      cycle_step
        (case checkInterrupts () s of
           SOME (i, p) => takeTrap (T, interruptIndex i, PC s, 0w, p) (next_pre s)
         | NONE =>
             next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
               (fetchAndExecute () (next_pre s)))
Proof
  gen_tac
  \\ simp_tac (srw_ss()) [Next_def, LET_THM, clear_logs_def, UNCURRY_FST_SND,
                          GSYM (SIMP_RULE (srw_ss()) [] next_pre_def),
                          NextFetch_def, MCSR_def]
  \\ simp_tac std_ss [checkInterrupts_next_pre]
  \\ `(PC (next_pre s) = PC s) /\
      ((next_pre s).c_MCSR (next_pre s).procID = s.c_MCSR s.procID)`
     by simp [next_pre_def, PC_def]
  \\ asm_simp_tac std_ss []
  \\ Cases_on `fetchAndExecute () (next_pre s)`
  \\ asm_simp_tac (srw_ss()) [next_post_def, cycle_step_def, LET_THM]
  \\ rpt CASE_TAC
  \\ asm_simp_tac (srw_ss()) []
QED

(* The instruction that the fetch result decodes to, as fetchAndExecute
   runs it, and the bits that it returns *)
Definition fetch_inst_def:
  (fetch_inst (F_Error i) (rvc : bool) = i) /\
  (fetch_inst (F_Result (Half h)) rvc =
     if rvc then DecodeRVC h else UnknownInstruction) /\
  (fetch_inst (F_Result (Word w)) rvc = Decode w)
End

Definition fetch_bits_def:
  (fetch_bits (F_Error i) = 0w : word64) /\
  (fetch_bits (F_Result (Half h)) = w2w h) /\
  (fetch_bits (F_Result (Word w)) = w2w w)
End

(* The instruction that the step runs, or NONE if it takes an interrupt
   instead (P §3.1.14 p.49, [D38]): the one decoded from the parcels that
   Fetch reads, or the internal FETCH_MISALIGNED or FETCH_FAULT of a
   misaligned pc or a fetch that fetchAddr refuses *)
Definition step_inst_def:
  step_inst s =
    if IS_SOME (checkInterrupts () s) then NONE
    else SOME (fetch_inst (FST (Fetch () s)) (haveRVC () s))
End

(* The state in which the instruction runs *)
Definition exec_state_def:
  exec_state s = SND (Fetch () (next_pre s))
End

Theorem exec_state_fields:
  !s. ((exec_state s).procID = s.procID) /\
      ((exec_state s).totalCore = s.totalCore) /\
      ((exec_state s).c_privilege = s.c_privilege) /\
      ((exec_state s).c_PC = s.c_PC) /\
      ((exec_state s).c_SCSR = s.c_SCSR) /\
      ((exec_state s).c_MCSR = s.c_MCSR) /\
      ((exec_state s).c_fpr = s.c_fpr) /\
      ((exec_state s).c_UCSR = s.c_UCSR) /\
      ((exec_state s).c_ReserveLoad = s.c_ReserveLoad) /\
      ((exec_state s).c_NextFetch = s.c_NextFetch) /\
      ((exec_state s).c_gpr = s.c_gpr) /\
      ((exec_state s).MEM8 = s.MEM8)
Proof
  simp [exec_state_def, Fetch_frame, next_pre_def]
QED

Theorem exec_state_priv:
  !s. (effectivePrivilege () (exec_state s) = effectivePrivilege () s) /\
      (curPrivilege () (exec_state s) = curPrivilege () s) /\
      (satp_bare (exec_state s) <=> satp_bare s)
Proof
  simp [effectivePrivilege_def, curPrivilege_def, MCSR_def, satp_bare_def,
        exec_state_fields]
QED

Theorem fetchAndExecute_next_pre:
  !s. fetchAndExecute () (next_pre s) =
      (fetch_bits (FST (Fetch () s)),
       Run (fetch_inst (FST (Fetch () s)) (haveRVC () s)) (exec_state s))
Proof
  gen_tac
  \\ `haveRVC () (exec_state s) = haveRVC () s`
     by simp [haveRVC_def, MCSR_def, exec_state_fields]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [fetchAndExecute_def, LET_THM, UNCURRY_FST_SND,
                      GSYM exec_state_def, Fetch_next_pre]
  \\ strip_tac
  \\ Cases_on `FST (Fetch () s)`
  \\ TRY (Cases_on `r`)
  \\ asm_simp_tac (srw_ss()) [fetch_inst_def, fetch_bits_def]
QED

(* A step either takes an interrupt or runs step_inst. *)
Theorem Next_interrupt:
  !s i p.
    (checkInterrupts () s = SOME (i, p)) ==>
    (Next s = cycle_step (takeTrap (T, interruptIndex i, PC s, 0w, p) (next_pre s)))
Proof
  simp [Next_split]
QED

Theorem Next_inst:
  !s i.
    (step_inst s = SOME i) ==>
    (Next s =
     cycle_step
       (next_post (~word_bit 2 (s.c_MCSR s.procID).mcountinhibit)
          (fetch_bits (FST (Fetch () s)), Run i (exec_state s))))
Proof
  rw [step_inst_def]
  \\ Cases_on `checkInterrupts () s`
  \\ fs [Next_split, fetchAndExecute_next_pre]
QED

Theorem step_inst_NONE:
  !s. (step_inst s = NONE) <=> ?i p. checkInterrupts () s = SOME (i, p)
Proof
  rw [step_inst_def]
  \\ Cases_on `checkInterrupts () s`
  \\ simp []
  \\ metis_tac [pairTheory.pair_CASES]
QED

Theorem cycle_step_fields:
  !t. ((cycle_step t).MEM8 = t.MEM8) /\ ((cycle_step t).procID = t.procID) /\
      ((cycle_step t).totalCore = t.totalCore) /\
      ((cycle_step t).c_privilege = t.c_privilege) /\
      ((cycle_step t).c_PC = t.c_PC) /\
      ((cycle_step t).c_SCSR = t.c_SCSR) /\
      ((cycle_step t).c_MCSR = t.c_MCSR) /\
      ((cycle_step t).c_fpr = t.c_fpr) /\
      ((cycle_step t).c_UCSR = t.c_UCSR) /\
      ((cycle_step t).c_ReserveLoad = t.c_ReserveLoad) /\
      ((cycle_step t).c_NextFetch = t.c_NextFetch) /\
      ((cycle_step t).c_gpr = t.c_gpr)
Proof
  rw [cycle_step_def]
QED

Theorem cycle_step_MEM8:
  !t m. cycle_step (t with MEM8 := m) = cycle_step t with MEM8 := m
Proof
  rw [cycle_step_def]
QED

Theorem next_post_MEM8_frame:
  !b v t. (next_post b (v, t)).MEM8 = t.MEM8
Proof
  rw [next_post_def]
  \\ rpt CASE_TAC
  \\ simp frame_thms
QED

Theorem next_post_MEM8:
  !b v t m. next_post b (v, t with MEM8 := m) = next_post b (v, t) with MEM8 := m
Proof
  rw [next_post_def]
  \\ rpt CASE_TAC
  \\ simp (thms_with "_MEM8" "riscv_footprint")
QED

(* ------------------------------------------------------------------------
   Accesses evaluated in the state in which the instruction runs
   ------------------------------------------------------------------------ *)

Theorem GPR_eq:
  !r s t. (t.procID = s.procID) /\ (t.c_gpr = s.c_gpr) ==> (GPR r t = GPR r s)
Proof
  rw [GPR_def, gpr_def]
QED

Theorem mem_access_eq:
  !i s t. (t.procID = s.procID) /\ (t.c_gpr = s.c_gpr) ==>
          (mem_access i t = mem_access i s)
Proof
  rpt strip_tac
  \\ Cases_on `i`
  \\ TRY (rename1 `mem_access (_ x) _` \\ Cases_on `x`)
  \\ pair_cases_tac
  \\ asm_simp_tac std_ss [mem_access_def, GPR_def, gpr_def]
QED

Theorem mem_access_kind:
  !i s va n kind.
    (mem_access i s = SOME (va, n, kind)) ==>
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\
    ((kind = PMP_Read) \/ (kind = PMP_Write) \/ (kind = PMP_ReadWrite))
Proof
  rpt gen_tac
  \\ Cases_on `i`
  \\ TRY (rename1 `mem_access (_ x) _` \\ Cases_on `x`)
  \\ pair_cases_tac
  \\ simp_tac (srw_ss()) [mem_access_def]
  \\ rw []
  \\ simp []
QED

Theorem effectivePrivilege_eq:
  !s t. (t.procID = s.procID) /\ (t.c_MCSR = s.c_MCSR) /\
        (t.c_privilege = s.c_privilege) ==>
        (effectivePrivilege () t = effectivePrivilege () s) /\
        (curPrivilege () t = curPrivilege () s)
Proof
  rw [effectivePrivilege_def, curPrivilege_def, MCSR_def]
QED

Theorem satp_bare_eq:
  !s t. (t.procID = s.procID) /\ (t.c_SCSR = s.c_SCSR) ==>
        (satp_bare t <=> satp_bare s)
Proof
  rw [satp_bare_def]
QED

(* With translation off, the data access of an instruction in the state in
   which it runs is the access in the state at the start of the step. *)
Theorem data_bytes_exec:
  !s acc x.
    ((effectivePrivilege () s = Machine) \/ satp_bare s) ==>
    (data_bytes acc (exec_state s) x <=> data_bytes acc s x)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ PairCases_on `acc`
  \\ `(effectivePrivilege () (exec_state s) = effectivePrivilege () s) /\
      (satp_bare (exec_state s) <=> satp_bare s)`
     by metis_tac [effectivePrivilege_eq, satp_bare_eq, exec_state_fields]
  \\ `!a. pmpCheck a (exec_state s) = pmpCheck a s`
     by metis_tac [pmpCheck_eq_MCSR, exec_state_fields]
  \\ asm_simp_tac std_ss [data_bytes_def, dataAddr_off]
QED

(* ------------------------------------------------------------------------
   (a) Write frame
   ------------------------------------------------------------------------ *)

(* Every byte that a step changes is a byte of the data access of the
   instruction that it runs, a store, SC, AMO or FP store (kind PMP_Write,
   or PMP_ReadWrite for an AMO, P §3.7.1 p.72), whose n bytes at va are
   naturally aligned and passed the PMP check for the effective privilege
   (P §3.1.6.4 p.35) in the configuration of s.  Translation is off: the
   effective privilege is M, or satp is Bare. *)
Theorem Next_writes:
  !s x.
    ((effectivePrivilege () s = Machine) \/ satp_bare s) /\
    ((Next s).MEM8 x <> s.MEM8 x) ==>
    ?i va n kind.
      (step_inst s = SOME i) /\ (mem_access i s = SOME (va, n, kind)) /\
      ((kind = PMP_Write) \/ (kind = PMP_ReadWrite)) /\ (w2n va MOD n = 0) /\
      in_range va n x /\ pmpCheck (va, n, kind, effectivePrivilege () s) s
Proof
  rpt gen_tac
  \\ disch_then (CONJUNCTS_THEN2 assume_tac assume_tac)
  \\ Cases_on `step_inst s`
  >- (qpat_x_assum `step_inst s = NONE`
        (strip_assume_tac o REWRITE_RULE [step_inst_NONE])
      \\ qpat_x_assum `_ <> _` mp_tac
      \\ imp_res_tac Next_interrupt
      \\ asm_simp_tac std_ss [cycle_step_fields]
      \\ simp (next_pre_def :: frame_thms))
  \\ rename1 `step_inst s = SOME i`
  \\ `(Run i (exec_state s)).MEM8 x <> (exec_state s).MEM8 x`
     by (imp_res_tac Next_inst
         \\ fs [cycle_step_fields, next_post_MEM8_frame, exec_state_fields])
  \\ drule Run_writes
  \\ strip_tac
  \\ PairCases_on `acc`
  \\ `mem_access i s = SOME (acc0, acc1, acc2)`
     by metis_tac [mem_access_eq, exec_state_fields]
  \\ qexistsl_tac [`i`, `acc0`, `acc1`, `acc2`]
  \\ `data_bytes (acc0, acc1, acc2) s x` by metis_tac [data_bytes_exec]
  \\ qpat_x_assum `data_bytes _ (exec_state s) _` kall_tac
  \\ fs [data_bytes_def]
  \\ qpat_x_assum `dataAddr _ _ = _` mp_tac
  \\ asm_simp_tac std_ss [dataAddr_off]
  \\ IF_CASES_TAC
  \\ simp_tac (srw_ss()) []
  \\ strip_tac
  \\ fs []
  \\ metis_tac [mem_access_kind]
QED

(* The hypotheses of the U-mode theorems: the hart is in U-mode, its
   explicit accesses are made with U-mode privilege (mstatus.MPRV = 0), and
   translation is off (satp.MODE = Bare) *)
Definition U_bare_def:
  U_bare s <=>
    (curPrivilege () s = User) /\ (effectivePrivilege () s = User) /\ satp_bare s
End

(* The register-level form, in the words that HolBA's contracts state *)
Theorem U_bare_intro:
  !s. (s.c_privilege s.procID = 0w) /\ ~(s.c_MCSR s.procID).mstatus.MPRV /\
      ((63 >< 60) (s.c_SCSR s.procID).satp = (0w : word4)) ==>
      U_bare s
Proof
  rw [U_bare_def, curPrivilege_def, effectivePrivilege_def, MCSR_def,
      privilege_def, satp_bare_def]
QED

Theorem Next_U_writes:
  !s x.
    (effectivePrivilege () s = User) /\ satp_bare s /\
    ((Next s).MEM8 x <> s.MEM8 x) ==>
    ?i va n kind.
      (step_inst s = SOME i) /\ (mem_access i s = SOME (va, n, kind)) /\
      ((kind = PMP_Write) \/ (kind = PMP_ReadWrite)) /\ (w2n va MOD n = 0) /\
      in_range va n x /\ pmpCheck (va, n, kind, User) s
Proof
  metis_tac [Next_writes]
QED

(* So every byte that a U-mode step changes is one that the PMP lets
   U-mode write (P §3.7.1.3 p.73 byte by byte: pmpCheck_byte). *)
Theorem Next_U_writes_byte:
  !s x.
    (effectivePrivilege () s = User) /\ satp_bare s /\
    ((Next s).MEM8 x <> s.MEM8 x) ==>
    pmpCheck (x, 1, PMP_Write, User) s
Proof
  rpt strip_tac
  \\ drule_all Next_U_writes
  \\ strip_tac
  \\ `(n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)` by metis_tac [mem_access_kind]
  \\ `pmpCheck (va, n, PMP_Write, User) s` by metis_tac [pmpCheck_RW]
  \\ metis_tac [pmpCheck_byte]
QED

(* ------------------------------------------------------------------------
   (b) Fetch
   ------------------------------------------------------------------------ *)

Theorem not_bit0_add2[local]:
  !a : word64. ~word_bit 0 a ==> ~word_bit 0 (a + 2w)
Proof
  blastLib.BBLAST_TAC
QED

(* Every byte of the parcels that the step fetches (fetch_bytes, which are
   the bytes that Fetch reads, Fetch_reads) is one that the PMP lets U-mode
   execute (P §3.7.1 p.72). *)
Theorem Next_U_fetch:
  !s x.
    (curPrivilege () s = User) /\ satp_bare s /\ fetch_bytes s x ==>
    pmpCheck (x, 1, PMP_Execute, User) s
Proof
  rpt strip_tac
  \\ `~word_bit 0 (PC s) /\
      (pmpCheck (PC s, 2, PMP_Execute, User) s /\ in_range (PC s) 2 x \/
       pmpCheck (PC s + 2w, 2, PMP_Execute, User) s /\ in_range (PC s + 2w) 2 x)`
     by metis_tac [fetch_bytes_off]
  >- (match_mp_tac (Q.SPECL [`PC s`, `2`] pmpCheck_byte)
      \\ asm_simp_tac std_ss [align_tests])
  \\ match_mp_tac (Q.SPECL [`PC s + 2w`, `2`] pmpCheck_byte)
  \\ asm_simp_tac std_ss [align_tests, not_bit0_add2]
QED

(* The parcel at the pc, or the second parcel of a 32-bit instruction, is
   one that the PMP does not let the current privilege execute; the pc is
   aligned (a misaligned pc raises the misaligned exception first). *)
Definition fetch_fault_def:
  fetch_fault s a <=>
    ~word_bit 0 (PC s) /\ (word_bit 1 (PC s) ==> haveRVC () s) /\
    ((a = PC s) /\ ~pmpCheck (PC s, 2, PMP_Execute, curPrivilege () s) s \/
     (a = PC s + 2w) /\ pmpCheck (PC s, 2, PMP_Execute, curPrivilege () s) s /\
     word_bit 0 (s.MEM8 (PC s)) /\ word_bit 1 (s.MEM8 (PC s)) /\
     ~pmpCheck (PC s + 2w, 2, PMP_Execute, curPrivilege () s) s)
End

(* The state in which the trap is taken: that of Next after the fetch,
   with NextFetch cleared, and Skip set by the first parcel *)
Definition fetch_fault_state_def:
  fetch_fault_state s a =
    let t = next_pre s with c_NextFetch := (s.procID =+ NONE) s.c_NextFetch in
    if a = PC s then t else t with c_Skip := (s.procID =+ 4w) s.c_Skip
End

Theorem Fetch_fault:
  !s a.
    ((curPrivilege () s = Machine) \/ satp_bare s) /\ fetch_fault s a ==>
    (Fetch () s =
     (F_Error (Internal (FETCH_FAULT (Fetch_Fault, a))),
      if a = PC s then s else s with c_Skip := (s.procID =+ 4w) s.c_Skip))
Proof
  rpt gen_tac
  \\ disch_then (CONJUNCTS_THEN2 assume_tac
                   (strip_assume_tac o REWRITE_RULE [fetch_fault_def]))
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ `!va. fetchAddr va s =
           if pmpCheck (va, 2, PMP_Execute, curPrivilege () s) s then TR_Address va
           else TR_Fault Fetch_Fault`
     by metis_tac [fetchAddr_off]
  \\ `~(word_bit 0 (PC s) \/ word_bit 1 (PC s) /\ ~haveRVC () s)` by metis_tac []
  \\ simp_tac std_ss [Fetch_def]
  \\ PURE_ONCE_REWRITE_TAC [LET_THM]
  \\ BETA_TAC
  \\ asm_simp_tac std_ss [TypeBase.case_def_of ``:TransResult``]
  \\ PURE_ONCE_REWRITE_TAC [LET_THM]
  \\ asm_simp_tac std_ss [rawReadInst_eq, UNCURRY_FST_SND,
                          TypeBase.case_def_of ``:rawInstType``, write'Skip_def,
                          fetchAddr_Skip, TypeBase.case_def_of ``:TransResult``]
  \\ simp_tac (srw_ss()) []
QED

(* A step whose fetch the PMP refuses, and which takes no interrupt, is the
   trap entry of an instruction access fault (code 1, P Table 16 p.50),
   with the address of the parcel as the trap value (P §3.1.16 p.52,
   [D59]), to M or as medeleg delegates (excDest, P §3.1.8 p.42). *)
Theorem Next_fetch_fault:
  !s a.
    ((curPrivilege () s = Machine) \/ satp_bare s) /\
    (checkInterrupts () s = NONE) /\ fetch_fault s a ==>
    (Next s =
     cycle_step
       (takeTrap (F, 1w, PC s, a, excDest (1w, curPrivilege () s) s)
          (fetch_fault_state s a)))
Proof
  rpt gen_tac
  \\ disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac))
  \\ `Fetch () s = (F_Error (Internal (FETCH_FAULT (Fetch_Fault, a))),
                    if a = PC s then s else s with c_Skip := (s.procID =+ 4w) s.c_Skip)`
     by metis_tac [Fetch_fault]
  \\ `step_inst s = SOME (Internal (FETCH_FAULT (Fetch_Fault, a)))`
     by asm_simp_tac (srw_ss()) [step_inst_def, fetch_inst_def]
  \\ drule Next_inst
  \\ disch_then SUBST1_TAC
  \\ `exec_state s =
      if a = PC s then next_pre s
      else next_pre s with c_Skip := (s.procID =+ 4w) s.c_Skip`
     by (asm_simp_tac std_ss [exec_state_def, Fetch_next_pre]
         \\ rw [next_pre_def])
  \\ pop_assum SUBST1_TAC
  \\ `!t. Run (Internal (FETCH_FAULT (Fetch_Fault, a))) t =
          write'NextFetch (SOME (Trap <| tval := a; trap := Fetch_Fault |>)) t`
     by simp [Run_def, dfn'FETCH_FAULT_def, signalAddressException_def,
              setTrap_def]
  \\ pop_assum (fn th => simp_tac std_ss [th])
  \\ asm_simp_tac (srw_ss()) [next_post_def, write'NextFetch_def, excCode_def,
                              combinTheory.UPDATE_EQ, combinTheory.APPLY_UPDATE_THM]
  \\ Cases_on `a = PC s`
  \\ asm_simp_tac (srw_ss()) [fetch_fault_state_def, next_pre_def, PC_def,
                              curPrivilege_def, excDest_def, MCSR_def, LET_THM]
QED

Theorem Next_U_fetch_fault:
  !s a.
    (curPrivilege () s = User) /\ satp_bare s /\
    (checkInterrupts () s = NONE) /\ fetch_fault s a ==>
    ((Next s).MEM8 = s.MEM8) /\
    (Next s =
     cycle_step
       (takeTrap (F, 1w, PC s, a, excDest (1w, User) s) (fetch_fault_state s a)))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `Next s =
      cycle_step
        (takeTrap (F, 1w, PC s, a, excDest (1w, User) s) (fetch_fault_state s a))`
     by metis_tac [Next_fetch_fault]
  \\ asm_simp_tac std_ss [cycle_step_fields]
  \\ rw ([fetch_fault_state_def, next_pre_def] @ frame_thms)
QED

(* ------------------------------------------------------------------------
   (c) Reads

   The bytes that a step reads: the CLINT bytes of the hart (the interrupt
   check, and the time CSR), the parcels it fetches, and the data that the
   instruction reads (loads, LR, AMOs, FLW, FLD).
   ------------------------------------------------------------------------ *)

Definition step_reads_def:
  step_reads s x <=>
    clint_byte s.procID x \/
    (checkInterrupts () s = NONE) /\ fetch_bytes s x \/
    ?i va n kind.
      (step_inst s = SOME i) /\ (mem_access i s = SOME (va, n, kind)) /\
      (kind <> PMP_Write) /\ data_bytes (va, n, kind) s x
End

Theorem next_pre_MEM8:
  !s m. next_pre (s with MEM8 := m) = next_pre s with MEM8 := m
Proof
  simp [next_pre_def]
QED

Theorem haveRVC_next_pre:
  !s. haveRVC () (next_pre s) = haveRVC () s
Proof
  simp [next_pre_def, haveRVC_def, MCSR_def]
QED

Theorem fetch_bytes_next_pre:
  !s x. fetch_bytes (next_pre s) x <=> fetch_bytes s x
Proof
  simp [fetch_bytes_def, next_pre_def, fetchAddr_log, fetchAddr_minstret,
        PC_log, PC_minstret]
QED

Theorem fetchAndExecute_eq:
  !t. fetchAndExecute () t =
      (fetch_bits (FST (Fetch () t)),
       Run (fetch_inst (FST (Fetch () t)) (haveRVC () t)) (SND (Fetch () t)))
Proof
  gen_tac
  \\ `haveRVC () (SND (Fetch () t)) = haveRVC () t`
     by simp [haveRVC_def, MCSR_def, Fetch_frame]
  \\ pop_assum mp_tac
  \\ simp_tac std_ss [fetchAndExecute_def, LET_THM, UNCURRY_FST_SND]
  \\ strip_tac
  \\ Cases_on `FST (Fetch () t)`
  \\ TRY (Cases_on `r`)
  \\ asm_simp_tac (srw_ss()) [fetch_inst_def, fetch_bits_def]
QED

(* Two states that are equal except on a set D of bytes that the step does
   not read take steps whose results are equal except on D, with
   translation off for the privilege of the fetch and of the data access *)
Theorem cycle_next_post_comm[local]:
  !b v t m.
    cycle_step (next_post b (v, t with MEM8 := m)) =
    cycle_step (next_post b (v, t)) with MEM8 := m
Proof
  simp [next_post_MEM8, cycle_step_MEM8]
QED


(* Two states that are equal except on a set D of bytes that the step does
   not read take steps whose results are equal except on D, with
   translation off for the privilege of the fetch and of the data access *)
Theorem Next_reads:
  !D s1 s2.
    ((curPrivilege () s1 = Machine) \/ satp_bare s1) /\
    ((effectivePrivilege () s1 = Machine) \/ satp_bare s1) /\
    same_except D s1 s2 /\ (!x. step_reads s1 x ==> ~D x) ==>
    same_except D (Next s1) (Next s2)
Proof
  rpt gen_tac
  \\ disch_then (CONJUNCTS_THEN2 assume_tac
                   (CONJUNCTS_THEN2 assume_tac
                      (CONJUNCTS_THEN2 assume_tac assume_tac)))
  \\ `?m. (s2 = s1 with MEM8 := m) /\ !x. ~D x ==> (s1.MEM8 x = m x)`
     by metis_tac [same_except_exists]
  \\ BasicProvers.VAR_EQ_TAC
  \\ `clint_agree s1 m`
     by (simp [clint_agree_def] \\ metis_tac [step_reads_def])
  \\ `checkInterrupts () (s1 with MEM8 := m) = checkInterrupts () s1`
     by metis_tac [checkInterrupts_CLINT]
  \\ Cases_on `checkInterrupts () s1`
  >- (
    (* no interrupt: fetch, run the instruction, dispatch, count *)
    asm_simp_tac (srw_ss()) [Next_split, next_pre_MEM8, fetchAndExecute_eq,
                             haveRVC_MEM8]
    \\ qabbrev_tac `t1 = next_pre s1`
    \\ `(t1.MEM8 = s1.MEM8) /\ (t1.procID = s1.procID) /\
        (t1.c_MCSR = s1.c_MCSR) /\ (t1.c_SCSR = s1.c_SCSR) /\
        (t1.c_privilege = s1.c_privilege)`
       by simp [Abbr `t1`, next_pre_def]
    \\ `same_except D t1 (t1 with MEM8 := m)`
       by asm_simp_tac std_ss [same_except_upd]
    \\ `(curPrivilege () t1 = curPrivilege () s1) /\ (satp_bare t1 <=> satp_bare s1) /\
        (effectivePrivilege () t1 = effectivePrivilege () s1)`
       by metis_tac [effectivePrivilege_eq, satp_bare_eq]
    \\ `!a. fetchAddr a (t1 with MEM8 := m) = fetchAddr a t1`
       by metis_tac [fetchAddr_off_MEM8]
    \\ `!x. fetch_bytes t1 x ==> ~D x`
       by metis_tac [fetch_bytes_next_pre, step_reads_def]
    \\ `(FST (Fetch () t1) = FST (Fetch () (t1 with MEM8 := m))) /\
        same_except D (SND (Fetch () t1)) (SND (Fetch () (t1 with MEM8 := m)))`
       by (irule Fetch_reads \\ asm_simp_tac std_ss [])
    \\ pop_assum (fn th => pop_assum (fn th' => SUBST1_TAC (SYM th') \\ assume_tac th))
    \\ qabbrev_tac `i = fetch_inst (FST (Fetch () t1)) (haveRVC () t1)`
    \\ qabbrev_tac `u1 = SND (Fetch () t1)`
    \\ qabbrev_tac `u2 = SND (Fetch () (t1 with MEM8 := m))`
    \\ `step_inst s1 = SOME i`
       by asm_simp_tac std_ss [Abbr `i`, Abbr `t1`, step_inst_def, Fetch_next_pre,
                               haveRVC_next_pre]
    \\ `u1 = exec_state s1` by simp [Abbr `u1`, Abbr `t1`, exec_state_def]
    \\ `same_except D (Run i u1) (Run i u2)`
       by (irule Run_reads
           \\ asm_simp_tac std_ss []
           \\ rpt conj_tac
           \\ rpt strip_tac
           \\ FIRST
                [(* the data the instruction reads *)
                 `mem_access i (exec_state s1) = mem_access i s1`
                   by (irule mem_access_eq \\ simp_tac std_ss [exec_state_fields])
                 \\ `data_bytes acc (exec_state s1) x <=> data_bytes acc s1 x`
                   by (irule data_bytes_exec \\ first_assum ACCEPT_TAC)
                 \\ `step_reads s1 x`
                   by (simp_tac std_ss [step_reads_def]
                       \\ disj2_tac
                       \\ disj2_tac
                       \\ PairCases_on `acc`
                       \\ qexistsl_tac [`i`, `acc0`, `acc1`, `acc2`]
                       \\ fs [])
                 \\ qpat_x_assum `!x. step_reads s1 x ==> ~D x` (qspec_then `x` mp_tac)
                 \\ asm_simp_tac std_ss [],
                 (* the CLINT *)
                 `step_reads s1 x`
                   by (simp_tac std_ss [step_reads_def]
                       \\ disj1_tac
                       \\ fs [exec_state_fields])
                 \\ qpat_x_assum `!x. step_reads s1 x ==> ~D x` (qspec_then `x` mp_tac)
                 \\ asm_simp_tac std_ss [],
                 (* dataAddr reads no memory with translation off *)
                 qpat_assum `same_except D u1 u2`
                   (strip_assume_tac o REWRITE_RULE [same_except_def])
                 \\ qpat_x_assum `u2 = _` SUBST1_TAC
                 \\ qpat_x_assum `u1 = exec_state s1` SUBST1_TAC
                 \\ PairCases_on `acc`
                 \\ irule dataAddr_off_MEM8
                 \\ asm_rewrite_tac [exec_state_priv]])
    \\ irule
         (BETA_RULE
            (Q.ISPEC
               `\t. cycle_step (next_post (~word_bit 2 (s1.c_MCSR s1.procID).mcountinhibit)
                                  (fetch_bits (FST (Fetch () t1)), t))`
               same_except_inert))
    \\ asm_simp_tac std_ss [cycle_next_post_comm])
  \\ PairCases_on `x`
  \\ asm_simp_tac (srw_ss()) [Next_split, next_pre_MEM8, PC_MEM8, takeTrap_MEM8,
                              cycle_step_MEM8, same_except_upd, cycle_step_fields]
  \\ simp ([next_pre_def] @ frame_thms)
QED

(* In U-mode with Bare satp, every byte that a step reads is a CLINT byte,
   or one that the PMP lets U-mode execute (the parcels fetched) or read
   (the data of a load, LR, AMO, FLW or FLD) *)
Theorem step_reads_U:
  !s x.
    U_bare s /\ step_reads s x ==>
    clint_byte s.procID x \/ pmpCheck (x, 1, PMP_Execute, User) s \/
    pmpCheck (x, 1, PMP_Read, User) s
Proof
  rpt gen_tac
  \\ simp_tac std_ss [U_bare_def, step_reads_def]
  \\ strip_tac
  \\ asm_rewrite_tac []
  >- metis_tac [Next_U_fetch]
  \\ disj2_tac
  \\ disj2_tac
  \\ `!a. dataAddr a s =
          if pmpCheck (FST a, FST (SND a), SND (SND a), User) s
          then TR_Address (FST a)
          else TR_Fault (accessFault (Data, if SND (SND a) = PMP_Read then Read else Write))`
     by (Cases \\ Cases_on `r` \\ metis_tac [dataAddr_off, pairTheory.FST, pairTheory.SND])
  \\ qpat_x_assum `data_bytes _ _ _` mp_tac
  \\ asm_simp_tac std_ss [data_bytes_def]
  \\ IF_CASES_TAC
  \\ simp_tac (srw_ss()) []
  \\ rpt strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ `((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\
      ((kind = PMP_Read) \/ (kind = PMP_ReadWrite))`
     by metis_tac [mem_access_kind]
  \\ `pmpCheck (va, n, PMP_Read, User) s` by metis_tac [pmpCheck_RW]
  \\ metis_tac [pmpCheck_byte]
QED

(* (c): two U-mode states that are equal except on a set D of bytes that
   U-mode may neither read nor execute, and that are not CLINT bytes, take
   steps whose results are equal except on D.  The PMP configuration, being
   outside memory, is the same in both. *)
Theorem Next_U_reads:
  !D s1 s2.
    U_bare s1 /\ same_except D s1 s2 /\
    (!x. D x ==> ~pmpCheck (x, 1, PMP_Read, User) s1 /\
                 ~pmpCheck (x, 1, PMP_Execute, User) s1 /\
                 ~clint_byte s1.procID x) ==>
    same_except D (Next s1) (Next s2)
Proof
  rpt strip_tac
  \\ irule Next_reads
  \\ fs [U_bare_def]
  \\ metis_tac [step_reads_U, U_bare_def]
QED

(* A U-mode step leaves the bytes that U-mode may not write as they were *)
Theorem Next_U_secret_unchanged:
  !D s.
    (effectivePrivilege () s = User) /\ satp_bare s /\
    (!x. D x ==> ~pmpCheck (x, 1, PMP_Write, User) s) ==>
    !x. D x ==> ((Next s).MEM8 x = s.MEM8 x)
Proof
  metis_tac [Next_U_writes_byte]
QED

(* With a legal PMP configuration (no entry with W = 1 and R = 0), the
   bytes of (c), which U-mode may not read, are not writable either, so
   both steps leave them unchanged *)
Theorem Next_U_reads_unchanged:
  !D s1 s2.
    U_bare s1 /\
    pmp_legal (s1.c_MCSR s1.procID).pmpcfg0 (s1.c_MCSR s1.procID).pmpcfg2 /\
    same_except D s1 s2 /\
    (!x. D x ==> ~pmpCheck (x, 1, PMP_Read, User) s1 /\
                 ~pmpCheck (x, 1, PMP_Execute, User) s1 /\
                 ~clint_byte s1.procID x) ==>
    same_except D (Next s1) (Next s2) /\
    (!x. D x ==> ((Next s1).MEM8 x = s1.MEM8 x) /\ ((Next s2).MEM8 x = s2.MEM8 x))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ conj_tac
  >- metis_tac [Next_U_reads]
  \\ `(s2.procID = s1.procID) /\ (s2.c_MCSR = s1.c_MCSR) /\ (s2.c_SCSR = s1.c_SCSR) /\
      (s2.c_privilege = s1.c_privilege)`
     by (qpat_x_assum `same_except _ _ _` (strip_assume_tac o REWRITE_RULE [same_except_def])
         \\ pop_assum kall_tac
         \\ pop_assum (fn th => once_rewrite_tac [th])
         \\ simp_tac (srw_ss()) [])
  \\ `U_bare s2` by metis_tac [U_bare_def, effectivePrivilege_eq, satp_bare_eq]
  \\ `!x. pmpCheck (x, 1, PMP_Write, User) s2 = pmpCheck (x, 1, PMP_Write, User) s1`
     by metis_tac [pmpCheck_eq_MCSR]
  \\ `!x. D x ==> ~pmpCheck (x, 1, PMP_Write, User) s1`
     by metis_tac [pmp_legal_write_read]
  \\ fs [U_bare_def]
  \\ metis_tac [Next_U_secret_unchanged]
QED

(* ------------------------------------------------------------------------
   (d) Frames

   What a U-mode step changes in the control state: only a trap entry
   changes the privilege, to M or S, and the trap CSRs; the other M-level
   CSRs, the PMP CSRs and satp among them, are unchanged, but for mstatus.FS
   becoming Dirty; the FP state is unchanged while FS is Off; only LR and SC
   change the load reservation.
   ------------------------------------------------------------------------ *)

(* mstatus without its trap-entry fields (P §3.1.6.1 p.32) and FS *)
Definition mstatus_nontrap_def:
  mstatus_nontrap (ms : mstatus) =
    ms with <| MIE := F; MPIE := F; MPP := 0w; SIE := F; SPIE := F; SPP := F;
               FS := 0w |>
End

(* The M-level CSRs that no trap entry writes, and mstatus but for the
   trap-entry fields and FS *)
Definition mcsr_same_def:
  mcsr_same (m : MachineCSR) (m' : MachineCSR) <=>
    (m'.misa = m.misa) /\ (m'.mhartid = m.mhartid) /\ (m'.medeleg = m.medeleg) /\
    (m'.mideleg = m.mideleg) /\ (m'.mie = m.mie) /\ (m'.mtvec = m.mtvec) /\
    (m'.mcounteren = m.mcounteren) /\ (m'.menvcfg = m.menvcfg) /\
    (m'.mcountinhibit = m.mcountinhibit) /\ (m'.mscratch = m.mscratch) /\
    (m'.mip = m.mip) /\ (m'.pmpcfg0 = m.pmpcfg0) /\ (m'.pmpcfg2 = m.pmpcfg2) /\
    (m'.pmpaddr0 = m.pmpaddr0) /\ (m'.pmpaddr1 = m.pmpaddr1) /\
    (m'.pmpaddr2 = m.pmpaddr2) /\ (m'.pmpaddr3 = m.pmpaddr3) /\
    (m'.pmpaddr4 = m.pmpaddr4) /\ (m'.pmpaddr5 = m.pmpaddr5) /\
    (m'.pmpaddr6 = m.pmpaddr6) /\ (m'.pmpaddr7 = m.pmpaddr7) /\
    (m'.pmpaddr8 = m.pmpaddr8) /\ (m'.pmpaddr9 = m.pmpaddr9) /\
    (m'.pmpaddr10 = m.pmpaddr10) /\ (m'.pmpaddr11 = m.pmpaddr11) /\
    (m'.pmpaddr12 = m.pmpaddr12) /\ (m'.pmpaddr13 = m.pmpaddr13) /\
    (m'.pmpaddr14 = m.pmpaddr14) /\ (m'.pmpaddr15 = m.pmpaddr15) /\
    (mstatus_nontrap m'.mstatus = mstatus_nontrap m.mstatus)
End

(* The S-level CSRs that no trap entry writes *)
Definition scsr_same_def:
  scsr_same (c : SupervisorCSR) (c' : SupervisorCSR) <=>
    (c'.satp = c.satp) /\ (c'.stvec = c.stvec) /\ (c'.scounteren = c.scounteren) /\
    (c'.senvcfg = c.senvcfg) /\ (c'.sscratch = c.sscratch)
End

(* The trap CSRs (P §3.1.14-3.1.16, §12.1.7-12.1.9) and the trap-entry
   fields of mstatus *)
Definition trap_fields_same_def:
  trap_fields_same s t <=>
    let m = s.c_MCSR s.procID; m' = t.c_MCSR s.procID;
        c = s.c_SCSR s.procID; c' = t.c_SCSR s.procID in
    (m'.mepc = m.mepc) /\ (m'.mcause = m.mcause) /\ (m'.mtval = m.mtval) /\
    (c'.sepc = c.sepc) /\ (c'.scause = c.scause) /\ (c'.stval = c.stval) /\
    (m'.mstatus.MIE = m.mstatus.MIE) /\ (m'.mstatus.MPIE = m.mstatus.MPIE) /\
    (m'.mstatus.MPP = m.mstatus.MPP) /\ (m'.mstatus.SIE = m.mstatus.SIE) /\
    (m'.mstatus.SPIE = m.mstatus.SPIE) /\ (m'.mstatus.SPP = m.mstatus.SPP)
End

Theorem mcsr_same_pmpaddr:
  !m m' i. mcsr_same m m' ==> (pmpaddr_of m' i = pmpaddr_of m i)
Proof
  rw [mcsr_same_def, pmpaddr_of_def]
QED

Theorem checkInterrupts_dest:
  !s i p. (checkInterrupts () s = SOME (i, p)) ==> (p = Machine) \/ (p = Supervisor)
Proof
  rw [checkInterrupts_def, LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs []
QED

Theorem excDest_dest:
  !ec p s. (excDest (ec, p) s = Machine) \/ (excDest (ec, p) s = Supervisor)
Proof
  rw [excDest_def]
QED

(* Trap entry to M or S (P §3.1.6.1 p.32, §3.1.14-3.1.16 p.48-53, §12.1.1
   p.113, §12.1.7-12.1.9 p.119-121) writes only the trap CSRs and the
   trap-entry fields of mstatus, the privilege and the pc *)
Theorem takeTrap_fields:
  !intr ec epc tval d s.
    ((d = Machine) \/ (d = Supervisor)) ==>
    mcsr_same (s.c_MCSR s.procID)
              ((takeTrap (intr, ec, epc, tval, d) s).c_MCSR s.procID) /\
    (((takeTrap (intr, ec, epc, tval, d) s).c_MCSR s.procID).mstatus.FS =
     (s.c_MCSR s.procID).mstatus.FS) /\
    scsr_same (s.c_SCSR s.procID)
              ((takeTrap (intr, ec, epc, tval, d) s).c_SCSR s.procID) /\
    ((takeTrap (intr, ec, epc, tval, d) s).c_privilege s.procID = privLevel d)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ simp [takeTrap_def, write'MCSR_def, write'SCSR_def, MCSR_def, SCSR_def,
           setPrivilege_def, write'PC_def, LET_THM, mcsr_same_def, scsr_same_def,
           mstatus_nontrap_def, combinTheory.APPLY_UPDATE_THM]
QED

(* The four forms of a U-mode step: the entry of an interrupt, the next
   instruction, a branch, or the trap entry of an exception that the
   instruction raised, from the state in which it ran *)
Theorem Next_U_shape:
  !s. (curPrivilege () s = User) /\ (s.c_NextFetch s.procID = NONE) ==>
      (?i p. (checkInterrupts () s = SOME (i, p)) /\
             ((p = Machine) \/ (p = Supervisor)) /\
             (Next s =
              cycle_step (takeTrap (T, interruptIndex i, PC s, 0w, p) (next_pre s)))) \/
      ?i r v b.
        (step_inst s = SOME i) /\ (r = Run i (exec_state s)) /\
        run_ok (lr_sc i) (exec_state s) r /\
        (b = ~word_bit 2 (s.c_MCSR s.procID).mcountinhibit) /\
        ((r.c_NextFetch s.procID = NONE) /\
         (Next s = cycle_step (write'PC (PC (incrInstret b r) + Skip (incrInstret b r))
                                 (incrInstret b r))) \/
         (?a. (r.c_NextFetch s.procID = SOME (BranchTo a)) /\
              (Next s = cycle_step (write'PC a (write'NextFetch NONE (incrInstret b r))))) \/
         (?e. (r.c_NextFetch s.procID = SOME (Trap e)) /\
              (Next s =
               cycle_step
                 (takeTrap (F, excCode e.trap, PC s,
                            (if e.trap = Illegal_Instr then v else e.tval),
                            excDest (excCode e.trap, User) s)
                    (write'NextFetch NONE r)))))
Proof
  rpt strip_tac
  \\ Cases_on `step_inst s`
  >- (disj1_tac
      \\ qpat_x_assum `step_inst s = NONE`
           (strip_assume_tac o REWRITE_RULE [step_inst_NONE])
      \\ qexistsl_tac [`i`, `p`]
      \\ metis_tac [checkInterrupts_dest, Next_interrupt])
  \\ disj2_tac
  \\ rename1 `step_inst s = SOME i`
  \\ `run_ok (lr_sc i) (exec_state s) (Run i (exec_state s))`
     by (irule Run_U \\ simp [exec_state_fields, exec_state_priv])
  \\ qexistsl_tac [`i`, `Run i (exec_state s)`, `fetch_bits (FST (Fetch () s))`,
                   `~word_bit 2 (s.c_MCSR s.procID).mcountinhibit`]
  \\ asm_simp_tac std_ss []
  \\ imp_res_tac Next_inst
  \\ asm_rewrite_tac []
  \\ qabbrev_tac `r = Run i (exec_state s)`
  \\ `(r.procID = s.procID) /\ (r.c_PC = s.c_PC) /\ (r.c_privilege = s.c_privilege)`
     by fs [run_ok_def, exec_state_fields]
  \\ `nf_ok (r.c_NextFetch s.procID) /\
      (is_trap (r.c_NextFetch s.procID) ==> (r.c_MCSR = s.c_MCSR))`
     by fs [run_ok_def, exec_state_fields]
  \\ simp_tac std_ss [next_post_def]
  \\ asm_rewrite_tac []
  \\ Cases_on `r.c_NextFetch s.procID`
  \\ asm_simp_tac (srw_ss()) []
  \\ Cases_on `x`
  \\ fs [nf_ok_def, is_trap_def]
  \\ `(PC (write'NextFetch NONE r) = PC s) /\
      (curPrivilege () (write'NextFetch NONE r) = User) /\
      (excDest (excCode S'.trap, User) (write'NextFetch NONE r) =
       excDest (excCode S'.trap, User) s)`
     by (fs [PC_def, curPrivilege_def, excDest_def, MCSR_def, write'NextFetch_def]
         \\ fs [GSYM curPrivilege_def])
  \\ asm_simp_tac std_ss []
QED

Theorem csr_same_refl:
  (!m. mcsr_same m m) /\ (!c. scsr_same c c)
Proof
  simp [mcsr_same_def, scsr_same_def]
QED

Theorem next_pre_fields:
  !s. ((next_pre s).procID = s.procID) /\ ((next_pre s).totalCore = s.totalCore) /\
      ((next_pre s).c_privilege = s.c_privilege) /\ ((next_pre s).c_PC = s.c_PC) /\
      ((next_pre s).c_SCSR = s.c_SCSR) /\ ((next_pre s).c_MCSR = s.c_MCSR) /\
      ((next_pre s).c_fpr = s.c_fpr) /\ ((next_pre s).c_UCSR = s.c_UCSR) /\
      ((next_pre s).c_ReserveLoad = s.c_ReserveLoad) /\
      ((next_pre s).c_NextFetch = s.c_NextFetch) /\ ((next_pre s).c_gpr = s.c_gpr) /\
      ((next_pre s).MEM8 = s.MEM8)
Proof
  simp [next_pre_def]
QED

(* What run_ok says of the CSRs and the FP state *)
Theorem run_ok_csr:
  !b s t.
    run_ok b s t ==>
    mcsr_same (s.c_MCSR s.procID) (t.c_MCSR s.procID) /\
    (((t.c_MCSR s.procID).mstatus.FS = (s.c_MCSR s.procID).mstatus.FS) \/
     ((t.c_MCSR s.procID).mstatus.FS = 3w)) /\
    (((s.c_MCSR s.procID).mstatus.FS = 0w) ==>
     (t.c_MCSR = s.c_MCSR) /\ (t.c_fpr = s.c_fpr) /\ (t.c_UCSR = s.c_UCSR)) /\
    (t.c_SCSR = s.c_SCSR) /\ trap_fields_same s t
Proof
  rw [run_ok_def, fs_on_def]
  \\ fs [mcsr_same_def, mstatus_nontrap_def, trap_fields_same_def, fs_dirty_of_def,
         combinTheory.APPLY_UPDATE_THM, LET_THM]
QED

(* (d): a U-mode step, from a state between steps, keeps procID, the
   M-level CSRs that no trap entry writes (misa, mhartid, medeleg, mideleg,
   mie, mtvec, mcounteren, menvcfg, mcountinhibit, mscratch, mip, the PMP
   CSRs, and mstatus but for its trap-entry fields and FS) and the S-level
   ones (satp, stvec, scounteren, senvcfg, sscratch); FS is unchanged or
   becomes Dirty (3), and while it is Off the FP registers and fcsr are
   unchanged (P §3.1.6.7 p.38); only LR and SC change the load reservation;
   and the next step again starts with NextFetch = NONE *)
Theorem Next_U_frame:
  !s. (curPrivilege () s = User) /\ (s.c_NextFetch s.procID = NONE) ==>
      ((Next s).procID = s.procID) /\ ((Next s).totalCore = s.totalCore) /\
      mcsr_same (s.c_MCSR s.procID) ((Next s).c_MCSR s.procID) /\
      scsr_same (s.c_SCSR s.procID) ((Next s).c_SCSR s.procID) /\
      ((((Next s).c_MCSR s.procID).mstatus.FS = (s.c_MCSR s.procID).mstatus.FS) \/
       (((Next s).c_MCSR s.procID).mstatus.FS = 3w)) /\
      (((s.c_MCSR s.procID).mstatus.FS = 0w) ==>
       (((Next s).c_MCSR s.procID).mstatus.FS = 0w) /\
       ((Next s).c_fpr = s.c_fpr) /\ ((Next s).c_UCSR = s.c_UCSR)) /\
      (((Next s).c_ReserveLoad <> s.c_ReserveLoad) ==>
       ?i. (step_inst s = SOME i) /\ lr_sc i) /\
      ((Next s).c_NextFetch s.procID = NONE)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ drule_all Next_U_shape
  \\ strip_tac
  \\ TRY (qpat_x_assum `r = Run _ _` kall_tac)
  \\ FIRST
       [(* an interrupt, to M or S *)
        qspecl_then [`T`, `interruptIndex i`, `PC s`, `0w`, `p`, `next_pre s`] mp_tac
          takeTrap_fields
        \\ asm_simp_tac (srw_ss()) ([cycle_step_fields, next_pre_fields] @ frame_thms)
        \\ fs [mcsr_same_def, scsr_same_def]
        \\ NO_TAC,
        (* an instruction *)
        `(r.procID = s.procID) /\ (r.totalCore = s.totalCore) /\
         ((r.c_ReserveLoad <> s.c_ReserveLoad) ==> lr_sc i)`
          by fs [run_ok_def, exec_state_fields]
        \\ drule run_ok_csr
        \\ asm_simp_tac std_ss [exec_state_fields]
        \\ strip_tac
        \\ FIRST
             [(* the next instruction, or a branch *)
              asm_simp_tac (srw_ss()) ([cycle_step_fields, write'NextFetch_NextFetch,
                                        combinTheory.APPLY_UPDATE_THM, csr_same_refl] @
                                       frame_thms)
              \\ metis_tac [],
              (* the trap entry of an exception *)
              `r.c_MCSR = s.c_MCSR` by fs [run_ok_def, is_trap_def, exec_state_fields]
              \\ qspecl_then [`F`, `excCode e.trap`, `PC s`,
                              `if e.trap = Illegal_Instr then v else e.tval`,
                              `excDest (excCode e.trap, User) s`,
                              `write'NextFetch NONE r`]
                   mp_tac takeTrap_fields
              \\ asm_simp_tac (srw_ss()) ([cycle_step_fields, write'NextFetch_NextFetch,
                                           combinTheory.APPLY_UPDATE_THM, excDest_dest] @
                                          frame_thms)
              \\ fs [mcsr_same_def, scsr_same_def]
              \\ metis_tac []]]
QED

(* (d): either the privilege and the trap CSRs are unchanged, or the step
   is a trap entry (takeTrap, design-privileged.md §4.6), to M or S as
   mideleg or medeleg delegate (P §3.1.8 p.42-43), from a state with the
   CSRs, privilege, pc and memory of s: an interrupt (P §3.1.14 p.49,
   [D38]), or an exception that the instruction raised before any other
   architectural effect (P §3.7 p.70); either way memory is unchanged *)
Theorem Next_U_trap:
  !s. (curPrivilege () s = User) /\ (s.c_NextFetch s.procID = NONE) ==>
      ((Next s).c_privilege = s.c_privilege) /\ trap_fields_same s (Next s)
      \/
      ((Next s).MEM8 = s.MEM8) /\
      ?intr ec tval d t.
        (Next s = cycle_step (takeTrap (intr, ec, PC s, tval, d) t)) /\
        ((d = Machine) \/ (d = Supervisor)) /\
        (if intr then ?i. (checkInterrupts () s = SOME (i, d)) /\ (ec = interruptIndex i)
         else d = excDest (ec, User) s) /\
        (t.c_MCSR = s.c_MCSR) /\ (t.c_SCSR = s.c_SCSR) /\
        (t.c_privilege = s.c_privilege) /\ (t.c_PC = s.c_PC) /\
        (t.MEM8 = s.MEM8) /\ (t.procID = s.procID)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ drule_all Next_U_shape
  \\ strip_tac
  \\ TRY (qpat_x_assum `r = Run _ _` kall_tac)
  \\ FIRST
       [(* an interrupt, to M or S *)
        disj2_tac
        \\ conj_tac
        >- asm_simp_tac (srw_ss()) ([cycle_step_fields, next_pre_fields] @ frame_thms)
        \\ qexistsl_tac [`T`, `interruptIndex i`, `0w`, `p`, `next_pre s`]
        \\ asm_simp_tac (srw_ss()) [next_pre_fields]
        \\ NO_TAC,
        (* an instruction *)
        `(r.procID = s.procID) /\ (r.c_privilege = s.c_privilege) /\ (r.c_PC = s.c_PC)`
          by fs [run_ok_def, exec_state_fields]
        \\ drule run_ok_csr
        \\ asm_simp_tac std_ss [exec_state_fields]
        \\ strip_tac
        \\ FIRST
             [(* the next instruction, or a branch *)
              disj1_tac
              \\ fs ([trap_fields_same_def, LET_THM, exec_state_fields,
                      cycle_step_fields] @ frame_thms)
              \\ NO_TAC,
              (* the trap entry of an exception *)
              disj2_tac
              \\ `(r.c_MCSR = s.c_MCSR) /\ (r.MEM8 = s.MEM8)`
                   by fs [run_ok_def, is_trap_def, exec_state_fields]
              \\ conj_tac
              >- asm_simp_tac (srw_ss()) ([cycle_step_fields] @ frame_thms)
              \\ qexistsl_tac [`F`, `excCode e.trap`,
                               `if e.trap = Illegal_Instr then v else e.tval`,
                               `excDest (excCode e.trap, User) s`, `write'NextFetch NONE r`]
              \\ asm_simp_tac (srw_ss()) ([excDest_dest] @ frame_thms)]]
QED

(* ------------------------------------------------------------------------
   Composition: a U-mode step that does not trap keeps the hypotheses
   ------------------------------------------------------------------------ *)

Theorem mcsr_same_mstatus:
  !m m'. mcsr_same m m' ==>
         (m'.mstatus.MPRV = m.mstatus.MPRV) /\ (m'.mstatus.MXR = m.mstatus.MXR) /\
         (m'.mstatus.SUM = m.mstatus.SUM) /\ (m'.mstatus.TSR = m.mstatus.TSR) /\
         (m'.mstatus.TVM = m.mstatus.TVM) /\ (m'.mstatus.TW = m.mstatus.TW)
Proof
  rw [mcsr_same_def]
  \\ qpat_x_assum `mstatus_nontrap _ = _`
       (fn th => map_every (fn f => mp_tac (AP_TERM f th))
                   [``mstatus_MPRV``, ``mstatus_MXR``, ``mstatus_SUM``,
                    ``mstatus_TSR``, ``mstatus_TVM``, ``mstatus_TW``])
  \\ simp [mstatus_nontrap_def]
QED

(* A U-mode step either traps, raising the privilege to M or S, or leaves
   the privilege, the trap CSRs, mstatus.MPRV, satp and the PMP CSRs as
   they were, so that the hypotheses of (a)-(d) hold again for the next
   step, with the same PMP configuration *)
Theorem Next_U_stays:
  !s. U_bare s /\ (s.c_NextFetch s.procID = NONE) /\
      ((Next s).c_privilege s.procID = s.c_privilege s.procID) ==>
      U_bare (Next s) /\ ((Next s).c_NextFetch (Next s).procID = NONE) /\
      ((Next s).procID = s.procID) /\
      (((Next s).c_MCSR (Next s).procID).pmpcfg0 = (s.c_MCSR s.procID).pmpcfg0) /\
      (((Next s).c_MCSR (Next s).procID).pmpcfg2 = (s.c_MCSR s.procID).pmpcfg2) /\
      (!i. pmpaddr i (Next s) = pmpaddr i s) /\
      (!acc. pmpCheck acc (Next s) = pmpCheck acc s)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `curPrivilege () s = User` by fs [U_bare_def]
  \\ drule_all Next_U_frame
  \\ strip_tac
  \\ drule_all Next_U_trap
  \\ strip_tac
  \\ FIRST
       [(* no trap *)
        `mcsr_same (s.c_MCSR s.procID) ((Next s).c_MCSR (Next s).procID) /\
         scsr_same (s.c_SCSR s.procID) ((Next s).c_SCSR (Next s).procID)`
          by asm_rewrite_tac []
        \\ imp_res_tac mcsr_same_mstatus
        \\ `!i. pmpaddr i (Next s) = pmpaddr i s`
             by (simp_tac std_ss [pmpaddr_of] \\ metis_tac [mcsr_same_pmpaddr])
        \\ `((Next s).c_MCSR s.procID).mstatus.MPP = (s.c_MCSR s.procID).mstatus.MPP`
             by fs [trap_fields_same_def, LET_THM]
        \\ `(((Next s).c_MCSR (Next s).procID).pmpcfg0 = (s.c_MCSR s.procID).pmpcfg0) /\
            (((Next s).c_MCSR (Next s).procID).pmpcfg2 = (s.c_MCSR s.procID).pmpcfg2)`
             by fs [mcsr_same_def]
        \\ asm_simp_tac std_ss []
        \\ conj_tac
        >- (fs [U_bare_def, curPrivilege_def, effectivePrivilege_def, MCSR_def,
                satp_bare_def, scsr_same_def]
            \\ rfs [])
        \\ metis_tac [pmpCheck_eq],
        (* a trap raises the privilege to 1 or 3, which is not U-mode *)
        qspecl_then [`intr`, `ec`, `PC s`, `tval`, `d`, `t`] mp_tac takeTrap_fields
        \\ fs [cycle_step_fields, curPrivilege_def, privilege_def, privLevel_def]
        \\ rpt strip_tac
        \\ rfs []
        \\ fs []]
QED

(* ------------------------------------------------------------------------
   The word-level forms, for HolBA's contracts

   With pmpCheck_MCSR, every PMP side condition above is a pmp_check of the
   18 PMP CSR words of the hart, pmpcfg0, pmpcfg2 and pmpaddr0-15.
   ------------------------------------------------------------------------ *)

Theorem Next_U_writes_words:
  !s x.
    (effectivePrivilege () s = User) /\ satp_bare s /\
    ((Next s).MEM8 x <> s.MEM8 x) ==>
    pmp_check ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
               pmpaddr_of (s.c_MCSR s.procID)) (x, 1, PMP_Write, User)
Proof
  metis_tac [Next_U_writes_byte, pmpCheck_MCSR]
QED

Theorem Next_U_fetch_words:
  !s x.
    (curPrivilege () s = User) /\ satp_bare s /\ fetch_bytes s x ==>
    pmp_check ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
               pmpaddr_of (s.c_MCSR s.procID)) (x, 1, PMP_Execute, User)
Proof
  metis_tac [Next_U_fetch, pmpCheck_MCSR]
QED

(* ------------------------------------------------------------------------
   The physical forms, with no hypothesis on the privilege or satp

   Whatever the translation, the physical address of an access passed the
   PMP check (dataAddr_pmpCheck, fetchAddr_pmpCheck; design-privileged.md
   §5.6.3, design-smode.md §3.11), and the model never writes a page-table
   entry (A and D are managed by software, design-smode.md [S3]).
   ------------------------------------------------------------------------ *)

(* Every byte that a step changes is a byte of the physical address of the
   data access of its instruction, which passed the PMP check for the
   effective privilege *)
Theorem Next_writes_pa:
  !s x.
    ((Next s).MEM8 x <> s.MEM8 x) ==>
    ?i va n kind pa.
      (step_inst s = SOME i) /\ (mem_access i s = SOME (va, n, kind)) /\
      ((kind = PMP_Write) \/ (kind = PMP_ReadWrite)) /\ (w2n va MOD n = 0) /\
      (dataAddr (va, n, kind) (exec_state s) = TR_Address pa) /\
      in_range pa n x /\ pmpCheck (pa, n, kind, effectivePrivilege () s) s
Proof
  rpt strip_tac
  \\ Cases_on `step_inst s`
  >- (qpat_x_assum `step_inst s = NONE`
        (strip_assume_tac o REWRITE_RULE [step_inst_NONE])
      \\ qpat_x_assum `_ <> _` mp_tac
      \\ imp_res_tac Next_interrupt
      \\ asm_simp_tac std_ss [cycle_step_fields]
      \\ simp (next_pre_def :: frame_thms))
  \\ rename1 `step_inst s = SOME i`
  \\ `(Run i (exec_state s)).MEM8 x <> (exec_state s).MEM8 x`
     by (imp_res_tac Next_inst
         \\ fs [cycle_step_fields, next_post_MEM8_frame, exec_state_fields])
  \\ drule Run_writes
  \\ strip_tac
  \\ PairCases_on `acc`
  \\ `mem_access i s = SOME (acc0, acc1, acc2)`
     by metis_tac [mem_access_eq, exec_state_fields]
  \\ qpat_x_assum `data_bytes _ _ _` (strip_assume_tac o REWRITE_RULE [data_bytes_def])
  \\ qexistsl_tac [`i`, `acc0`, `acc1`, `acc2`, `pa`]
  \\ fs []
  \\ `pmpCheck (pa, acc1, acc2, effectivePrivilege () (exec_state s)) (exec_state s)`
     by metis_tac [dataAddr_pmpCheck]
  \\ `pmpCheck (pa, acc1, acc2, effectivePrivilege () s) s`
     by metis_tac [exec_state_priv, pmpCheck_eq_MCSR, exec_state_fields]
  \\ asm_simp_tac std_ss []
  \\ metis_tac [mem_access_kind]
QED

(* Every byte of the parcels that a step fetches is a byte of the physical
   address of a parcel that passed the PMP check for execution by the
   current privilege (P §3.7.1 p.72) *)
Theorem fetch_bytes_pmp:
  !s x.
    fetch_bytes s x ==>
    ?pa. in_range pa 2 x /\ pmpCheck (pa, 2, PMP_Execute, curPrivilege () s) s
Proof
  rw [fetch_bytes_def]
  \\ metis_tac [fetchAddr_pmpCheck]
QED
