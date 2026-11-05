(* ------------------------------------------------------------------------
   A sanity check of riscv_timerTheory on a concrete state: hart 0 in U-mode
   at 0x80000000, with only the timer interrupt enabled (mie = MTIE),
   nothing delegated (mideleg = 0), mtvec = 0x80002000 (Direct mode), and in
   the CLINT mtimecmp of hart 0 = 100.

   - ex_timer_only_checkInterrupts, ex_timer_only_Next:
     checkInterrupts_U_timer and Next_U_timer for mie = MTIE and
     mideleg = 0;
   - ex_timer_base: the state with mtime = 0, from which no interrupt is
     taken (ex_timer_base_no_interrupt); ex_timer_witness: the same state
     with the clock set to 200 (set_mtime), so that the timer interrupt is
     pending (ex_timer_witness_pending);
   - ex_ssi_base, ex_ssi_taken: the same state as ex_timer_base but with
     SSIE also set in mie and SSIP pending: it meets the hypotheses on mie
     and mideleg of checkInterrupts_U_timer_pending, the timer interrupt is
     not pending, and the supervisor software interrupt is taken, so the
     equation of checkInterrupts_U_timer needs SEIE, STIE and SSIE clear as
     well;
   - ex_timer_step: the step from ex_timer_witness, evaluated by EVAL from
     the definitions of the model: no instruction is run, the privilege
     becomes M, the pc 0x80002000, mcause 7 with the interrupt bit
     (0x8000000000000007), mepc 0x80000000 and mtval 0, MPP U and MIE
     clear, and the GPRs and memory are unchanged;
   - ex_timer_hyps, ex_timer_trap: the hypotheses of Next_U_timer hold for
     ex_timer_witness, and the theorem gives the same trap state;
   - ex_timer_tick: a tick at a transition into ex_timer_base that the tick
     condition selects sets the clock to 200 and gives ex_timer_witness;
   - ex_timer_stopped: with the stopped clock, the tick-point execution of
     one step from ex_timer_witness is that step (tpexec_stopped), so it
     enters the trap vector; ex_timer_tick_trap: with the clock at 300 and
     a tick condition that selects the step out of U-mode, the step enters
     the trap vector and the tick then sets mtime to 300.

   This theory has riscv_stepTheory as an ancestor through riscv_timerTheory
   (DESIGN.md I11).
   ------------------------------------------------------------------------ *)
Theory riscv_timer_example
Ancestors
  riscv riscv_footprint riscv_isolation riscv_trap riscv_timer riscv_step[qualified]
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

(* EVAL evaluates the model.  L3 exports the definitions of the model
   without adding them to EVAL's compset, and outside the heap of ../step
   the update and accessor theorems of the model's records are not in it
   either, so this script adds the definitions of the functions that Next
   reaches (the closure of Next_def over the constants of riscvTheory) and
   those record theorems.  It does not add every definition of riscvTheory:
   with HOL4 trindemossen-2 they include the constructors of the enumerated
   types (User = num2Privilege 0, ...), with which EVAL did not prove
   ex_timer_base_no_interrupt below in ten minutes. *)
local
  fun model_def c =
    let
      val {Name, Thy, ...} = Term.dest_thy_const c
    in
      if Thy = "riscv" then Lib.total (DB.fetch "riscv") (Name ^ "_def") else NONE
    end
  fun reach (_, defs, []) = defs
    | reach (seen, defs, c :: rest) =
        let
          val {Name, Thy, ...} = Term.dest_thy_const c
          val n = Thy ^ "$" ^ Name
        in
          if Redblackset.member (seen, n) then reach (seen, defs, rest)
          else
            case model_def c of
              NONE => reach (Redblackset.add (seen, n), defs, rest)
            | SOME th =>
                reach (Redblackset.add (seen, n), th :: defs,
                       HolKernel.find_terms Term.is_const (Thm.concl th) @ rest)
        end
  fun record_thms (n, _) =
    let
      val ty = Type.mk_thy_type {Tyop = n, Thy = "riscv", Args = []}
    in
      TypeBase.updates_of ty @ TypeBase.accessors_of ty
    end
    handle HOL_ERR _ => []
in
  val () =
    computeLib.add_funs (reach (Redblackset.empty String.compare, [], [``Next``]))
  val () =
    computeLib.add_funs (List.concat (List.map record_thms (Theory.types "riscv")))
end

(* ------------------------------------------------------------------------
   1. Only the timer interrupt enabled, nothing delegated
   ------------------------------------------------------------------------ *)

(* With mie = MTIE alone and mideleg = 0, a U-mode state takes an interrupt
   exactly when the timer interrupt is pending, into M-mode *)
Theorem ex_timer_only_checkInterrupts:
  !s. (curPrivilege () s = User) /\ (reg'mie (s.c_MCSR s.procID).mie = 0x80w) /\
      ((s.c_MCSR s.procID).mideleg = 0w) ==>
      (checkInterrupts () s =
         if mtimecmp s.procID s <=+ mtime () s then SOME (MTI, Machine) else NONE)
Proof
  rpt strip_tac
  \\ irule checkInterrupts_U_timer
  \\ asm_rewrite_tac []
  \\ EVAL_TAC
QED

(* ... and the step from such a state with the timer interrupt pending is
   its trap entry *)
Theorem ex_timer_only_Next:
  !s. (curPrivilege () s = User) /\ (reg'mie (s.c_MCSR s.procID).mie = 0x80w) /\
      ((s.c_MCSR s.procID).mideleg = 0w) /\ (mtimecmp s.procID s <=+ mtime () s) ==>
      (step_inst s = NONE) /\
      ((Next s).procID = s.procID) /\
      ((Next s).c_privilege s.procID = 3w) /\
      ((Next s).c_PC s.procID = trapVector ((s.c_MCSR s.procID).mtvec, T, 7w)) /\
      (((Next s).c_MCSR s.procID).mcause = <| EC := 7w; Int := T |>) /\
      (((Next s).c_MCSR s.procID).mepc = PC s) /\
      (((Next s).c_MCSR s.procID).mtval = 0w) /\
      (((Next s).c_MCSR s.procID).mstatus =
         (s.c_MCSR s.procID).mstatus with
           <| MIE := F; MPIE := (s.c_MCSR s.procID).mstatus.MIE; MPP := 0w |>) /\
      (((Next s).c_MCSR s.procID) with
         <| mcause := (s.c_MCSR s.procID).mcause; mepc := (s.c_MCSR s.procID).mepc;
            mtval := (s.c_MCSR s.procID).mtval;
            mstatus := (s.c_MCSR s.procID).mstatus |> =
       s.c_MCSR s.procID) /\
      ((Next s).c_SCSR = s.c_SCSR) /\ ((Next s).c_gpr = s.c_gpr) /\
      ((Next s).c_fpr = s.c_fpr) /\ ((Next s).MEM8 = s.MEM8) /\
      ((Next s).c_ReserveLoad = s.c_ReserveLoad) /\
      ((Next s).c_NextFetch = s.c_NextFetch) /\
      ((Next s).exception = s.exception)
Proof
  gen_tac
  \\ strip_tac
  \\ `word_bit 7 (reg'mie (s.c_MCSR s.procID).mie) /\
      ~word_bit 7 (s.c_MCSR s.procID).mideleg /\
      (reg'mie (s.c_MCSR s.procID).mie && 0x808w = 0w)`
     by (asm_rewrite_tac [] \\ EVAL_TAC)
  \\ drule_all Next_U_timer
  \\ simp_tac std_ss []
QED

(* ------------------------------------------------------------------------
   2. A concrete state, and the step that takes the timer interrupt
   ------------------------------------------------------------------------ *)

(* The memory: mtimecmp of hart 0 (CLINT_BASE + 0x4000) is 100, mtime
   (CLINT_BASE + 0xBFF8), the msip word of hart 0 (CLINT_BASE) and every
   other byte are 0 *)
Definition ex_timer_mem_def:
  ex_timer_mem (a : word64) : word8 = if a = 0x2004000w then 100w else 0w
End

(* Hart 0 in U-mode at 0x80000000, with mie = MTIE, mideleg = 0, mtvec =
   0x80002000 (Direct), mstatus, mcause, the stored mip and mcountinhibit
   0, and no external interrupt line raised; the other fields are left
   unspecified (ARB) *)
Definition ex_timer_base_def:
  ex_timer_base =
    (ARB : riscv_state) with
      <| procID := 0w; c_privilege := K 0w; c_PC := K 0x80000000w;
         MEM8 := ex_timer_mem; c_extSEIP := K F; c_extMEIP := K F;
         c_MCSR := K ((ARB : MachineCSR) with
                        <| mstatus := rec'mstatus 0w; mcause := rec'mcause 0w;
                           mie := rec'mie 0x80w; mideleg := 0w; mip := rec'mip 0w;
                           mtvec := 0x80002000w; mcountinhibit := 0w |>) |>
End

(* The same state after the clock has reached 200 *)
Definition ex_timer_witness_def:
  ex_timer_witness = set_mtime 200w ex_timer_base
End

Theorem ex_timer_base_no_interrupt:
  (mtime () ex_timer_base = 0w) /\ (mtimecmp 0w ex_timer_base = 100w) /\
  (checkInterrupts () ex_timer_base = NONE)
Proof
  rpt conj_tac
  \\ EVAL_TAC
QED

Theorem ex_timer_witness_pending:
  (mtime () ex_timer_witness = 200w) /\ (mtimecmp 0w ex_timer_witness = 100w) /\
  (checkInterrupts () ex_timer_witness = SOME (MTI, Machine))
Proof
  rpt conj_tac
  \\ EVAL_TAC
QED

(* ex_timer_base with SSIE (bit 1) set in mie besides MTIE and SSIP set in
   the stored mip *)
Definition ex_ssi_base_def:
  ex_ssi_base =
    ex_timer_base with
      c_MCSR := K ((ex_timer_base.c_MCSR 0w) with
                     <| mie := rec'mie 0x82w; mip := rec'mip 0x2w |>)
End

(* With MTIE set and not delegated and MEIE and MSIE clear, but SSIE set, a
   pending supervisor software interrupt is taken (into M-mode, as mideleg
   does not delegate it) while the timer interrupt is not pending: the
   hypothesis of checkInterrupts_U_timer cannot be weakened to that of
   checkInterrupts_U_timer_pending *)
Theorem ex_ssi_taken:
  (curPrivilege () ex_ssi_base = User) /\
  word_bit 7 (reg'mie (ex_ssi_base.c_MCSR ex_ssi_base.procID).mie) /\
  ~word_bit 7 (ex_ssi_base.c_MCSR ex_ssi_base.procID).mideleg /\
  (reg'mie (ex_ssi_base.c_MCSR ex_ssi_base.procID).mie && 0x808w = 0w) /\
  ~(mtimecmp ex_ssi_base.procID ex_ssi_base <=+ mtime () ex_ssi_base) /\
  (checkInterrupts () ex_ssi_base = SOME (SSI, Machine))
Proof
  rpt conj_tac
  \\ EVAL_TAC
QED

(* The step, by evaluation of the model's Next *)
Theorem ex_timer_step:
  (step_inst ex_timer_witness = NONE) /\
  ((Next ex_timer_witness).procID = 0w) /\
  ((Next ex_timer_witness).c_privilege 0w = 3w) /\
  ((Next ex_timer_witness).c_PC 0w = 0x80002000w) /\
  (((Next ex_timer_witness).c_MCSR 0w).mcause.EC = 7w) /\
  ((Next ex_timer_witness).c_MCSR 0w).mcause.Int /\
  (reg'mcause ((Next ex_timer_witness).c_MCSR 0w).mcause = 0x8000000000000007w) /\
  (((Next ex_timer_witness).c_MCSR 0w).mepc = 0x80000000w) /\
  (((Next ex_timer_witness).c_MCSR 0w).mtval = 0w) /\
  (((Next ex_timer_witness).c_MCSR 0w).mstatus.MPP = 0w) /\
  ~((Next ex_timer_witness).c_MCSR 0w).mstatus.MIE /\
  ((Next ex_timer_witness).c_gpr = ex_timer_witness.c_gpr) /\
  ((Next ex_timer_witness).MEM8 = ex_timer_witness.MEM8)
Proof
  rpt conj_tac
  \\ EVAL_TAC
QED

(* The hypotheses of Next_U_timer hold for the state *)
Theorem ex_timer_hyps:
  (curPrivilege () ex_timer_witness = User) /\
  word_bit 7 (reg'mie (ex_timer_witness.c_MCSR ex_timer_witness.procID).mie) /\
  ~word_bit 7 (ex_timer_witness.c_MCSR ex_timer_witness.procID).mideleg /\
  (reg'mie (ex_timer_witness.c_MCSR ex_timer_witness.procID).mie && 0x808w = 0w) /\
  (mtimecmp ex_timer_witness.procID ex_timer_witness <=+ mtime () ex_timer_witness)
Proof
  rpt conj_tac
  \\ EVAL_TAC
QED

(* ... so Next_U_timer gives the trap state of ex_timer_step *)
Theorem ex_timer_trap:
  (step_inst ex_timer_witness = NONE) /\
  ((Next ex_timer_witness).c_privilege 0w = 3w) /\
  ((Next ex_timer_witness).c_PC 0w = 0x80002000w) /\
  (reg'mcause ((Next ex_timer_witness).c_MCSR 0w).mcause = 0x8000000000000007w) /\
  (((Next ex_timer_witness).c_MCSR 0w).mepc = 0x80000000w) /\
  ((Next ex_timer_witness).c_gpr = ex_timer_witness.c_gpr) /\
  ((Next ex_timer_witness).MEM8 = ex_timer_witness.MEM8)
Proof
  `(ex_timer_witness.procID = 0w) /\ (PC ex_timer_witness = 0x80000000w) /\
   ((ex_timer_witness.c_MCSR 0w).mtvec = 0x80002000w)`
     by EVAL_TAC
  \\ mp_tac (MATCH_MP Next_U_timer ex_timer_hyps)
  \\ asm_rewrite_tac []
  \\ strip_tac
  \\ asm_rewrite_tac [reg'mcause_timer]
  \\ simp_tac (srw_ss()) []
  \\ irule trapVector_direct
  \\ EVAL_TAC
QED

(* ------------------------------------------------------------------------
   3. The state in the tick-point execution
   ------------------------------------------------------------------------ *)

(* A tick at a transition into ex_timer_base that C selects, with the bound
   above 200, sets the clock to 200 *)
Theorem ex_timer_tick:
  !C mx pre. C pre ex_timer_base /\ 200 < mx ==>
             (tptick C mx 200w pre ex_timer_base = ex_timer_witness)
Proof
  rpt strip_tac
  \\ `mtime () ex_timer_base <+ 200w` by EVAL_TAC
  \\ `w2n (200w : word64) = 200` by EVAL_TAC
  \\ asm_simp_tac std_ss [tptick_def, ex_timer_witness_def]
QED

(* With the stopped clock the tick-point execution takes the trap *)
Theorem ex_timer_stopped:
  !C mx.
    (tpexec C mx (K 0w) ex_timer_witness 1 = Next ex_timer_witness) /\
    ((tpexec C mx (K 0w) ex_timer_witness 1).c_privilege 0w = 3w) /\
    ((tpexec C mx (K 0w) ex_timer_witness 1).c_PC 0w = 0x80002000w) /\
    (reg'mcause ((tpexec C mx (K 0w) ex_timer_witness 1).c_MCSR 0w).mcause =
     0x8000000000000007w)
Proof
  rpt gen_tac
  \\ `tpexec C mx (K 0w) ex_timer_witness 1 = Next ex_timer_witness`
     by simp [tpexec_stopped, arithmeticTheory.FUNPOW_1]
  \\ asm_rewrite_tac [ex_timer_step]
QED

(* With the clock at 300 and a tick condition that selects the step out of
   U-mode, the step from ex_timer_witness enters the trap vector and the
   tick after it sets mtime to 300 *)
Theorem ex_timer_tick_trap:
  !mx. 300 < mx ==>
    let C = (\(pre : riscv_state) (post : riscv_state). pre.c_privilege pre.procID = 0w);
        u = tpexec C mx (K 300w) ex_timer_witness 1 in
      (mtime () u = 300w) /\ (u.c_privilege 0w = 3w) /\ (u.c_PC 0w = 0x80002000w) /\
      (reg'mcause (u.c_MCSR 0w).mcause = 0x8000000000000007w)
Proof
  rpt strip_tac
  \\ `1 = SUC 0` by simp []
  \\ pop_assum SUBST1_TAC
  \\ `mtime () (Next ex_timer_witness) = 200w` by EVAL_TAC
  \\ `ex_timer_witness.c_privilege ex_timer_witness.procID = 0w` by EVAL_TAC
  \\ `200w <+ 300w : word64` by EVAL_TAC
  \\ `w2n (300w : word64) = 300` by EVAL_TAC
  \\ asm_simp_tac std_ss [LET_THM, tpexec_def, tptick_def, mtime_set_mtime]
  \\ simp_tac (srw_ss()) [set_mtime_def, ex_timer_step]
QED
