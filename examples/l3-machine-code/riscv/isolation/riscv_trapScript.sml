(* ------------------------------------------------------------------------
   Trap entry from U-mode in the RISC-V L3 model: what an M-mode kernel
   that takes system calls by ECALL (P §3.3.1 p.60-61) needs to know of the
   step of a process that enters it, and of the steps that take no
   interrupt.

   - Next_U_ecall: a step in which U-mode runs ECALL, with medeleg not
     delegating it, is exactly the trap entry of the environment call from
     U-mode into M-mode (cause 8, P Table 16 p.50): the privilege becomes M,
     the pc the trap vector of mtvec, mepc the pc of the ECALL, mtval 0,
     mstatus.MIE 0, MPIE the old MIE and MPP U; no other CSR, no GPR and no
     memory changes, and NextFetch is NONE again;
   - checkInterrupts_U_MTIP: a U-mode state from which no interrupt is
     taken, with the timer interrupt enabled in mie, has no timer
     interrupt pending (mtimecmp > mtime), whatever mideleg delegates;
   - Next_U_stays_no_interrupt: a step from U-mode that stays in U-mode
     took no interrupt;
   - reg'mcause_8, trapVector_direct: the mcause word of that trap is 8,
     and a trap vector in Direct mode is mtvec itself.

   Unlike riscv_isolationTheory and the theories below it (DESIGN.md I11),
   this theory has the step library's riscv_stepTheory as an ancestor, for
   takeTrap_Machine and read_mip_eval.  It opens it qualified only, so that
   the model's Fetch_def is not shadowed by the step library's.
   ------------------------------------------------------------------------ *)
Theory riscv_trap
Ancestors
  riscv riscv_isolation riscv_step[qualified]
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()
val ERR = mk_HOL_ERR "riscv_trapTheory"

(* riscv_isolationTheory, and so riscv_footprintTheory, riscv_framesTheory
   and riscv_pmpTheory below it, does not have riscv_stepTheory as an
   ancestor (DESIGN.md I11) *)
val () =
  if Lib.mem "riscv_step" (Theory.ancestry "riscv_isolation") then
    raise ERR "riscv_trap" "riscv_stepTheory is an ancestor of riscv_isolationTheory"
  else ()

(* ------------------------------------------------------------------------
   1. The exception field, the privilege, and the instruction of a step
   ------------------------------------------------------------------------ *)

(* The spec's Fetch writes c_update (setupDelta) and Skip, and returns
   F_Error where the fetch fails rather than raising an exception: it
   leaves the exception field as it was *)
Theorem Fetch_exception:
  !s. (SND (Fetch () s)).exception = s.exception
Proof
  gen_tac
  \\ simp [Fetch_def, LET_THM]
  \\ rpt (CASE_TAC
          \\ simp [write'Delta_def, write'Skip_def, LET_THM, pairTheory.UNCURRY,
                   rawReadInst_def])
QED

Theorem exec_state_exception:
  !s. (exec_state s).exception = s.exception
Proof
  simp [exec_state_def, Fetch_exception, next_pre_def]
QED

(* curPrivilege reads the reserved encoding 2 as U-mode *)
Theorem curPrivilege_User:
  !s. (curPrivilege () s = User) <=>
      (s.c_privilege s.procID = 0w) \/ (s.c_privilege s.procID = 2w)
Proof
  gen_tac
  \\ simp [curPrivilege_def]
  \\ wordsLib.Cases_on_word_value `s.c_privilege s.procID`
  \\ simp [privilege_def]
QED

(* A step that runs an instruction took no interrupt *)
Theorem step_inst_SOME:
  !s i. (step_inst s = SOME i) ==> (checkInterrupts () s = NONE)
Proof
  rw [step_inst_def]
  \\ Cases_on `checkInterrupts () s`
  \\ fs []
QED

(* ------------------------------------------------------------------------
   2. The step that runs ECALL in U-mode
   ------------------------------------------------------------------------ *)

(* ECALL in U-mode raises the environment call from U-mode and does nothing
   else (P §3.3.1 p.60-61; cause 8, Table 16 p.50).  Unless bit 8 of
   medeleg delegates it to S (P §3.1.8 p.42), the trap goes to M
   (takeTrap_Machine): mcause, mepc and mtval are written (P §3.1.14-3.1.16
   p.48-53; mtval is 0 for an environment call, p.53), MPIE becomes MIE,
   MIE becomes 0 and MPP becomes U (P §3.1.6.1 p.32), the privilege becomes
   M and the pc the trap vector of mtvec (P §3.1.7 p.41).  No other M-level
   or S-level CSR, no GPR and no memory changes, NextFetch is NONE (whatever
   it was before the step), and the exception field is unchanged. *)
Theorem Next_U_ecall:
  !s. (curPrivilege () s = User) /\ (step_inst s = SOME (System ECALL)) /\
      ~word_bit 8 (s.c_MCSR s.procID).medeleg ==>
      ((Next s).procID = s.procID) /\
      ((Next s).c_privilege s.procID = 3w) /\
      ((Next s).c_PC s.procID = trapVector ((s.c_MCSR s.procID).mtvec, F, 8w)) /\
      (((Next s).c_MCSR s.procID).mcause = <| EC := 8w; Int := F |>) /\
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
      ((Next s).c_SCSR = s.c_SCSR) /\
      ((Next s).c_gpr = s.c_gpr) /\ ((Next s).MEM8 = s.MEM8) /\
      ((Next s).c_NextFetch s.procID = NONE) /\
      ((Next s).exception = s.exception)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ imp_res_tac Next_inst
  \\ `curPrivilege () (exec_state s) = User` by metis_tac [exec_state_priv]
  \\ `Run (System ECALL) (exec_state s) =
      write'NextFetch (SOME (Trap <| tval := 0w; trap := UMode_Env_Call |>))
        (exec_state s)`
     by simp [Run_def, dfn'ECALL_def, signalEnvCall_def, signalException_def,
              setTrap_def]
  \\ qpat_x_assum `Next s = _` SUBST1_TAC
  \\ pop_assum SUBST1_TAC
  \\ `excDest (8w, User)
        (exec_state s with
           c_NextFetch := ((exec_state s).procID =+ NONE) (exec_state s).c_NextFetch) =
      Machine`
     by fs [excDest_def, MCSR_def, exec_state_fields]
  \\ `(s.c_privilege s.procID = 0w) \/ (s.c_privilege s.procID = 2w)`
     by metis_tac [curPrivilege_User]
  \\ simp [next_post_def, write'NextFetch_def, combinTheory.UPDATE_EQ,
           combinTheory.UPDATE_APPLY, excCode_def, PC_def]
  \\ fs [curPrivilege_def, MCSR_def, exec_state_fields]
  \\ simp [riscv_stepTheory.takeTrap_Machine, cycle_step_def, exec_state_fields,
           exec_state_exception, combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
  \\ rw []
  \\ fs [exec_state_fields, exec_state_exception, combinTheory.UPDATE_APPLY,
         privilege_def, MachineCSR_component_equality, mstatus_component_equality]
QED

(* ------------------------------------------------------------------------
   3. Steps that take no interrupt
   ------------------------------------------------------------------------ *)

(* In U-mode an interrupt that is pending and enabled in mie is taken: to M
   if mideleg does not delegate it, and to S if it does (P §3.1.9 p.43,
   §12.1.3 p.117), so both branches of checkInterrupts are enabled.  When
   no interrupt is taken and MTIE (mie bit 7) is set, the timer interrupt is
   therefore not pending: MTIP, which read_mip computes from the CLINT as
   mtimecmp <=+ mtime (P §3.2.1 p.59, [D67]), is clear. *)
Theorem checkInterrupts_U_MTIP:
  !s. (curPrivilege () s = User) /\ word_bit 7 (reg'mie (s.c_MCSR s.procID).mie) /\
      (checkInterrupts () s = NONE) ==>
      ~(mtimecmp s.procID s <=+ mtime () s)
Proof
  rpt strip_tac
  \\ qpat_x_assum `checkInterrupts () s = NONE` mp_tac
  \\ simp [checkInterrupts_def, riscv_stepTheory.read_mip_eval, MCSR_def, LET_THM]
  \\ rw [highestInterrupt_def]
  \\ rpt (pop_assum mp_tac)
  \\ blastLib.BBLAST_TAC
QED

(* An interrupt is taken into M or S (checkInterrupts_dest, takeTrap_fields),
   so a step from U-mode that stays in U-mode took none *)
Theorem Next_U_stays_no_interrupt:
  !s. (s.c_privilege s.procID = 0w) /\
      ((Next s).c_privilege s.procID = s.c_privilege s.procID) ==>
      (checkInterrupts () s = NONE)
Proof
  rpt strip_tac
  \\ Cases_on `checkInterrupts () s`
  \\ simp []
  \\ PairCases_on `x`
  \\ imp_res_tac checkInterrupts_dest
  \\ imp_res_tac Next_interrupt
  \\ qspecl_then [`T`, `interruptIndex x0`, `PC s`, `0w`, `x1`, `next_pre s`]
       mp_tac takeTrap_fields
  \\ fs [cycle_step_fields, next_pre_def, privLevel_def]
  \\ rpt strip_tac
  \\ rfs []
  \\ fs [privLevel_def]
QED

(* ------------------------------------------------------------------------
   4. The trap CSRs as words
   ------------------------------------------------------------------------ *)

(* mcause as a word: Int in bit 63 and the exception code below it
   (P §3.1.15 Figure 22 p.49) *)
Theorem reg'mcause_8:
  !c. (reg'mcause c = 8w) <=> (c.EC = 8w) /\ ~c.Int
Proof
  Cases
  \\ simp [reg'mcause_def]
  \\ blastLib.BBLAST_TAC
QED

(* In Direct mode (mtvec.MODE = 0) every trap sets the pc to BASE, which is
   then mtvec itself (P §3.1.7 Table 15 p.41) *)
Theorem trapVector_direct:
  !tvec intr ec.
    ((1 >< 0) tvec = 0w : word2) ==> (trapVector (tvec, intr, ec) = tvec)
Proof
  rpt strip_tac
  \\ simp [trapVector_def]
  \\ pop_assum mp_tac
  \\ blastLib.BBLAST_TAC
QED

(* An exception goes to BASE in Direct and in Vectored mode (P §3.1.7
   p.41-42) *)
Theorem trapVector_exception:
  !tvec ec. trapVector (tvec, F, ec) = tvec && ~3w
Proof
  simp [trapVector_def]
  \\ blastLib.BBLAST_TAC
QED
