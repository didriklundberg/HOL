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
  riscv riscv_step riscv_footprint riscv_frames riscv_pmp
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
