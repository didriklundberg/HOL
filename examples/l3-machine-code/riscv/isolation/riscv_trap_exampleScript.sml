(* ------------------------------------------------------------------------
   A sanity check of riscv_trapTheory on the PMP configuration of
   riscv_isolation_exampleTheory (entry 0 a NAPOT region of 4 KiB at
   0x80000000 that U-mode may read, write and execute, entries 1-15 OFF):
   a U-mode state with ecall at a 4-aligned pc inside the region, only the
   timer interrupt enabled and not pending, ECALL not delegated and mtvec
   in Direct mode.

   - ex_timer_only: with only MTIE set in mie, a U-mode state takes no
     interrupt iff the timer interrupt is not pending
     (checkInterrupts_U_MTIP one way);
   - ex_ecall_step_inst: the step from such a state runs ECALL;
   - ex_ecall: it is the trap entry into M-mode at mtvec, with mcause 8,
     mepc the pc of the ecall, MPP U and MIE clear, and it changes no GPR,
     no memory and not the PMP configuration (Next_U_ecall, reg'mcause_8,
     trapVector_direct);
   - ex_ecall_state_witness, ex_ecall_witness_trap: a concrete state of
     this kind, so the hypotheses of Next_U_ecall can be met together.

   This theory has riscv_stepTheory as an ancestor through riscv_trapTheory,
   so it is a theory of its own rather than a part of
   riscv_isolation_exampleTheory, which does not (DESIGN.md I11).
   ------------------------------------------------------------------------ *)
Theory riscv_trap_example
Ancestors
  riscv riscv_footprint riscv_pmp riscv_isolation riscv_isolation_example riscv_trap
  riscv_step[qualified]
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

(* ecall is 0x00000073 (P §3.3.1 p.60): funct12 = 0, rs1 = 0, funct3 = PRIV
   = 0, rd = 0, opcode SYSTEM *)
val ex_ecall_decode =
  let
    val bits = bitstringSyntax.bitstring_of_hexstring "00000073"
    val v = bitstringSyntax.mk_v2w (bits, ``:32``)
    val eq = EVAL ``^v = 0x00000073w : word32`` |> EQT_ELIM
    val th =
      Decode_def |> Q.SPEC `^v`
      |> CONV_RULE (RAND_CONV
           (REWRITE_CONV [boolify32_v2w, asImm12_def, asImm20_def, asSImm12_def]
            THENC DEPTH_CONV PairedLambda.let_CONV THENC EVAL))
  in
    save_thm ("ex_ecall_decode",
              th |> CONV_RULE (RAND_CONV (DEPTH_CONV bitstringLib.v2w_n2w_CONV))
                 |> REWRITE_RULE [eq])
  end

(* With only the timer interrupt enabled (mie = MTIE, P §3.1.9 p.43-45), a
   U-mode state takes no interrupt iff the timer interrupt is not pending:
   checkInterrupts_U_MTIP one way, read_mip_eval the other *)
Theorem ex_timer_only:
  !s. (curPrivilege () s = User) /\ (reg'mie (s.c_MCSR s.procID).mie = 0x80w) ==>
      ((checkInterrupts () s = NONE) <=> ~(mtimecmp s.procID s <=+ mtime () s))
Proof
  rpt strip_tac
  \\ eq_tac
  >- (strip_tac
      \\ irule checkInterrupts_U_MTIP
      \\ asm_simp_tac (srw_ss()) [])
  \\ strip_tac
  \\ asm_simp_tac std_ss [checkInterrupts_def, riscv_stepTheory.read_mip_eval, MCSR_def,
                          LET_THM]
  \\ `!x : word64. ~word_bit 7 x ==> (x && 0x80w = 0w)` by blastLib.BBLAST_TAC
  \\ rw [highestInterrupt_def]
  \\ rpt (pop_assum mp_tac)
  \\ blastLib.BBLAST_TAC
QED

(* The bytes of ecall at the pc *)
Definition ex_ecall_at_def:
  ex_ecall_at s <=>
    (s.MEM8 (PC s) = 0x73w) /\ (s.MEM8 (PC s + 1w) = 0x00w) /\
    (s.MEM8 (PC s + 2w) = 0x00w) /\ (s.MEM8 (PC s + 3w) = 0x00w)
End

(* A U-mode state with Bare satp and the configuration of ex_pmp, only the
   timer interrupt enabled and not pending, ECALL not delegated (medeleg =
   0), mtvec in Direct mode, and ecall at a 4-aligned pc inside the
   region *)
Definition ex_ecall_state_def:
  ex_ecall_state s <=>
    U_bare s /\ ex_pmp (s.c_MCSR s.procID) /\
    (reg'mie (s.c_MCSR s.procID).mie = 0x80w) /\ ~(mtimecmp s.procID s <=+ mtime () s) /\
    ((s.c_MCSR s.procID).medeleg = 0w) /\ ((1 >< 0) (s.c_MCSR s.procID).mtvec = 0w : word2) /\
    in_region (PC s) /\ ((1 >< 0) (PC s) = 0w : word2) /\ ex_ecall_at s
End

Theorem ex_ecall_step_inst:
  !s. ex_ecall_state s ==> (step_inst s = SOME (System ECALL))
Proof
  rw [ex_ecall_state_def, U_bare_def]
  \\ `checkInterrupts () s = NONE` by metis_tac [ex_timer_only]
  \\ `in_region (PC s + 2w)`
     by (qpat_x_assum `in_region _` mp_tac \\ qpat_x_assum `(1 >< 0) (PC s) = _` mp_tac
         \\ simp_tac std_ss [in_region_def] \\ blastLib.BBLAST_TAC)
  \\ `(w2n (PC s) MOD 2 = 0) /\ (w2n (PC s + 2w) MOD 2 = 0)`
     by (simp_tac std_ss [align_tests]
         \\ qpat_x_assum `(1 >< 0) (PC s) = _` mp_tac \\ blastLib.BBLAST_TAC)
  \\ `pmpCheck (PC s, 2, PMP_Execute, User) s /\
      pmpCheck (PC s + 2w, 2, PMP_Execute, User) s`
     by metis_tac [pmpCheck_MCSR, ex_pmp_check]
  \\ fs [ex_ecall_at_def]
  \\ `FST (Fetch () s) = F_Result (Word 0x00000073w)`
     by (qspec_then `s` mp_tac Fetch_word \\ asm_simp_tac (srw_ss()) [] \\ EVAL_TAC)
  \\ asm_simp_tac (srw_ss()) [step_inst_def, fetch_inst_def, ex_ecall_decode]
QED

(* The step is the trap entry of the environment call into M-mode at
   mtvec, and keeps the GPRs, memory and the PMP configuration *)
Theorem ex_ecall:
  !s. ex_ecall_state s ==>
      ((Next s).procID = s.procID) /\
      ((Next s).c_privilege s.procID = 3w) /\
      ((Next s).c_PC s.procID = (s.c_MCSR s.procID).mtvec) /\
      (reg'mcause ((Next s).c_MCSR s.procID).mcause = 8w) /\
      (((Next s).c_MCSR s.procID).mepc = PC s) /\
      (((Next s).c_MCSR s.procID).mstatus.MPP = 0w) /\
      ~((Next s).c_MCSR s.procID).mstatus.MIE /\
      ex_pmp ((Next s).c_MCSR s.procID) /\
      ((Next s).c_gpr = s.c_gpr) /\ ((Next s).MEM8 = s.MEM8)
Proof
  gen_tac
  \\ strip_tac
  \\ drule ex_ecall_step_inst
  \\ strip_tac
  \\ `(curPrivilege () s = User) /\ ~word_bit 8 (s.c_MCSR s.procID).medeleg`
     by fs [ex_ecall_state_def, U_bare_def]
  \\ drule_all Next_U_ecall
  \\ strip_tac
  \\ `(1 >< 0) (s.c_MCSR s.procID).mtvec = 0w : word2` by fs [ex_ecall_state_def]
  \\ `ex_pmp (s.c_MCSR s.procID)` by fs [ex_ecall_state_def]
  \\ qpat_x_assum `_ with <| mcause := _; mepc := _; mtval := _; mstatus := _ |> = _`
       (strip_assume_tac o SIMP_RULE (srw_ss()) [MachineCSR_component_equality])
  \\ fs [reg'mcause_8, trapVector_direct, ex_pmp_def]
QED

(* A concrete state of this kind: hart 0 in U-mode at 0x80000000, where
   memory holds ecall, with mtimecmp of hart 0 (CLINT_BASE + 0x4000) all
   ones and mtime (CLINT_BASE + 0xBFF8) zero, the PMP configuration of
   ex_pmp, mie = MTIE, medeleg = 0 and mtvec = 0x80002000 (Direct); the
   other fields are left unspecified (ARB) *)
Definition ex_ecall_mem_def:
  ex_ecall_mem (a : word64) : word8 =
    if a = 0x80000000w then 0x73w
    else if 0x2004000w <=+ a /\ a <+ 0x2004008w then 0xFFw
    else 0w
End

Definition ex_ecall_witness_def:
  ex_ecall_witness =
    (ARB : riscv_state) with
      <| procID := 0w; c_privilege := K 0w; c_PC := K 0x80000000w;
         MEM8 := ex_ecall_mem;
         c_SCSR := K ((ARB : SupervisorCSR) with satp := 0w);
         c_MCSR := K ((ARB : MachineCSR) with
                        <| mstatus := (ARB : mstatus) with MPRV := F;
                           pmpcfg0 := 0x1Fw; pmpcfg2 := 0w; pmpaddr0 := 0x200001FFw;
                           medeleg := 0w; mtvec := 0x80002000w;
                           mie := rec'mie 0x80w |>) |>
End

Theorem ex_ecall_state_witness:
  ex_ecall_state ex_ecall_witness
Proof
  simp_tac (srw_ss())
    [ex_ecall_state_def, ex_ecall_witness_def, U_bare_def, curPrivilege_def,
     effectivePrivilege_def, MCSR_def, SCSR_def, privilege_def, satp_bare_def,
     ex_pmp_def, PC_def, in_region_def, ex_ecall_at_def, mtimecmp_def, mtime_def,
     MEM_def, CLINT_BASE_def, riscv_stepTheory.reg_rec_id]
  \\ simp_tac (srw_ss()) [ex_ecall_mem_def]
  \\ EVAL_TAC
QED

(* So for that state the step runs ECALL and enters M-mode at 0x80002000
   with mepc = 0x80000000 and mcause 8 *)
Theorem ex_ecall_witness_trap:
  (step_inst ex_ecall_witness = SOME (System ECALL)) /\
  ((Next ex_ecall_witness).c_privilege 0w = 3w) /\
  ((Next ex_ecall_witness).c_PC 0w = 0x80002000w) /\
  (reg'mcause ((Next ex_ecall_witness).c_MCSR 0w).mcause = 8w) /\
  (((Next ex_ecall_witness).c_MCSR 0w).mepc = 0x80000000w)
Proof
  `(ex_ecall_witness.procID = 0w) /\ (PC ex_ecall_witness = 0x80000000w) /\
   ((ex_ecall_witness.c_MCSR 0w).mtvec = 0x80002000w)`
     by simp_tac (srw_ss()) [ex_ecall_witness_def, PC_def]
  \\ assume_tac (MATCH_MP ex_ecall_step_inst ex_ecall_state_witness)
  \\ mp_tac (MATCH_MP ex_ecall ex_ecall_state_witness)
  \\ asm_rewrite_tac []
  \\ strip_tac
  \\ asm_rewrite_tac []
QED
