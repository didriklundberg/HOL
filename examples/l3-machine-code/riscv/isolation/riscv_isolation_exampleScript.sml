(* ------------------------------------------------------------------------
   A sanity check of the U-mode PMP theorems of riscv_isolationTheory on a
   concrete configuration: PMP entry 0 is a NAPOT region of 4 KiB at
   0x80000000 that U-mode may read, write and execute, and entries 1-15
   are OFF (P §3.7.1 p.70-73).

   - ex_pmp_check, ex_pmp_byte: the PMP check of this configuration allows
     a U-mode access exactly inside the region, by EVAL on the words;
   - ex_writes: (a) instantiated: a U-mode step changes memory only inside
     the region;
   - ex_reads: (c) instantiated: a U-mode step does not depend on memory
     outside the region, but for the CLINT;
   - ex_store_inside, ex_store_outside: the step that runs sd x6, 0(x5)
     from inside the region writes the 8 bytes of x6 at the address in x5
     when that is inside the region, and when it is outside is the trap
     entry of a store access fault that changes no memory.
   ------------------------------------------------------------------------ *)
Theory riscv_isolation_example
Ancestors
  riscv riscv_footprint riscv_frames riscv_pmp riscv_isolation
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

fun thms_with suffix thy =
  List.mapPartial (fn (n, th) => if String.isSuffix suffix n then SOME th else NONE)
                  (DB.thms thy)
val frame_thms = thms_with "_frame" "riscv_frames"

Theorem UNCURRY_FST_SND[local]:
  !f p. UNCURRY f p = f (FST p) (SND p)
Proof
  Cases_on `p` \\ rw []
QED

(* Entry 0: L = 0, A = 3 (NAPOT), X = W = R = 1 (P §3.7.1 Figure 34 p.72);
   pmpaddr0 is 0x80000000 / 4 with the 9 trailing ones of a 2^12-byte NAPOT
   region (Table 24 p.72).  The other entries are OFF. *)
Definition ex_pmp_def:
  ex_pmp (m : MachineCSR) <=>
    (m.pmpcfg0 = 0x1Fw) /\ (m.pmpcfg2 = 0w) /\ (m.pmpaddr0 = 0x200001FFw)
End

Definition in_region_def:
  in_region (x : word64) <=> 0x80000000w <=+ x /\ x <+ 0x80001000w
End

(* The word-level check of this configuration, by evaluation: an aligned
   access by U-mode of 1, 2, 4 or 8 bytes, of any kind, is allowed iff it
   starts inside the region *)
Theorem ex_pmp_check:
  !m a n kind.
    ex_pmp m /\ ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\ (w2n a MOD n = 0) ==>
    (pmp_check (m.pmpcfg0, m.pmpcfg2, pmpaddr_of m) (a, n, kind, User) <=>
     in_region a)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `ex_pmp m` (strip_assume_tac o REWRITE_RULE [ex_pmp_def])
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ asm_rewrite_tac [pmp_check_def, pmpaddr_of_def]
  \\ CONV_TAC (LAND_CONV EVAL)
  \\ asm_rewrite_tac []
  \\ CONV_TAC (LAND_CONV EVAL)
  \\ qpat_x_assum `w2n a MOD _ = 0` mp_tac
  \\ rpt (pop_assum kall_tac)
  \\ simp_tac std_ss [align_tests]
  \\ Cases_on `kind`
  \\ simp_tac (srw_ss()) [in_region_def, COND_RAND, COND_RATOR]
  \\ blastLib.BBLAST_TAC
QED

Theorem ex_pmp_byte:
  !s x kind.
    ex_pmp (s.c_MCSR s.procID) ==>
    (pmpCheck (x, 1, kind, User) s <=> in_region x)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [pmpCheck_MCSR]
  \\ irule ex_pmp_check
  \\ simp []
QED

(* (a) on this configuration: every byte that a U-mode step changes is
   inside the region *)
Theorem ex_writes:
  !s x.
    ex_pmp (s.c_MCSR s.procID) /\ (effectivePrivilege () s = User) /\
    satp_bare s /\ ((Next s).MEM8 x <> s.MEM8 x) ==>
    in_region x
Proof
  metis_tac [Next_U_writes_byte, ex_pmp_byte]
QED

(* (c) on this configuration: two U-mode states that differ only outside the
   region, and not at the CLINT, take steps that differ only there *)
Theorem ex_reads:
  !s1 s2.
    ex_pmp (s1.c_MCSR s1.procID) /\ U_bare s1 /\
    same_except (\x. ~in_region x /\ ~clint_byte s1.procID x) s1 s2 ==>
    same_except (\x. ~in_region x /\ ~clint_byte s1.procID x) (Next s1) (Next s2)
Proof
  rpt strip_tac
  \\ irule Next_U_reads
  \\ asm_simp_tac std_ss []
  \\ metis_tac [ex_pmp_byte]
QED

(* ------------------------------------------------------------------------
   sd x6, 0(x5) inside and outside the region
   ------------------------------------------------------------------------ *)

(* sd x6, 0(x5) is 0x0062B023 (U §2.6, Table 70): imm[11:5] = 0, rs2 = 6,
   rs1 = 5, funct3 = 011, imm[4:0] = 0, opcode STORE *)
val ex_sd_decode =
  let
    val bits = bitstringSyntax.bitstring_of_hexstring "0062B023"
    val v = bitstringSyntax.mk_v2w (bits, ``:32``)
    val eq = EVAL ``^v = 0x0062B023w : word32`` |> EQT_ELIM
    val th =
      Decode_def |> Q.SPEC `^v`
      |> CONV_RULE (RAND_CONV
           (REWRITE_CONV [boolify32_v2w, asImm12_def, asImm20_def, asSImm12_def]
            THENC DEPTH_CONV PairedLambda.let_CONV THENC EVAL))
  in
    save_thm ("ex_sd_decode",
              th |> CONV_RULE (RAND_CONV (DEPTH_CONV bitstringLib.v2w_n2w_CONV))
                 |> REWRITE_RULE [eq])
  end

(* The parcel at a 4-aligned pc and the next one, both executable, give the
   32-bit instruction of the four bytes at the pc (Fetch, [D59]) *)
Theorem Fetch_word:
  !s.
    ((curPrivilege () s = Machine) \/ satp_bare s) /\
    ((1 >< 0) (PC s) = 0w : word2) /\
    pmpCheck (PC s, 2, PMP_Execute, curPrivilege () s) s /\
    pmpCheck (PC s + 2w, 2, PMP_Execute, curPrivilege () s) s /\
    word_bit 0 (s.MEM8 (PC s)) /\ word_bit 1 (s.MEM8 (PC s)) ==>
    (FST (Fetch () s) =
     F_Result (Word (s.MEM8 (PC s + 3w) @@ s.MEM8 (PC s + 2w) @@
                     s.MEM8 (PC s + 1w) @@ s.MEM8 (PC s))))
Proof
  rpt gen_tac
  \\ disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac)
  \\ `!va. fetchAddr va s =
           if pmpCheck (va, 2, PMP_Execute, curPrivilege () s) s then TR_Address va
           else TR_Fault Fetch_Fault`
     by metis_tac [fetchAddr_off]
  \\ `~(word_bit 0 (PC s) \/ word_bit 1 (PC s) /\ ~haveRVC () s)`
     by (qpat_x_assum `(1 >< 0) _ = _` mp_tac \\ blastLib.BBLAST_TAC)
  \\ simp_tac std_ss [Fetch_def]
  \\ PURE_ONCE_REWRITE_TAC [LET_THM]
  \\ BETA_TAC
  \\ asm_simp_tac std_ss [TypeBase.case_def_of ``:TransResult``]
  \\ PURE_ONCE_REWRITE_TAC [LET_THM]
  \\ asm_simp_tac std_ss [rawReadInst_eq, UNCURRY_FST_SND, write'Skip_def,
                          fetchAddr_Skip, TypeBase.case_def_of ``:rawInstType``,
                          TypeBase.case_def_of ``:TransResult``]
  \\ PURE_ONCE_REWRITE_TAC [LET_THM]
  \\ simp_tac (srw_ss()) []
  \\ `PC s + 2w + 1w = PC s + 3w` by blastLib.BBLAST_TAC
  \\ asm_simp_tac std_ss []
  \\ blastLib.BBLAST_TAC
QED

(* The bytes of sd x6, 0(x5) at the pc *)
Definition ex_sd_at_def:
  ex_sd_at s <=>
    (s.MEM8 (PC s) = 0x23w) /\ (s.MEM8 (PC s + 1w) = 0xB0w) /\
    (s.MEM8 (PC s + 2w) = 0x62w) /\ (s.MEM8 (PC s + 3w) = 0x00w)
End

(* A U-mode state between steps, with Bare satp and the configuration
   above, that takes no interrupt, on an RV64 hart, with sd x6, 0(x5) at a
   4-aligned pc inside the region *)
Definition ex_state_def:
  ex_state s <=>
    U_bare s /\ ex_pmp (s.c_MCSR s.procID) /\ (s.c_NextFetch s.procID = NONE) /\
    (checkInterrupts () s = NONE) /\ ~in32BitMode () s /\
    in_region (PC s) /\ ((1 >< 0) (PC s) = 0w : word2) /\ ex_sd_at s
End

Theorem ex_step_inst:
  !s. ex_state s ==> (step_inst s = SOME (Store (SD (5w, 6w, 0w))))
Proof
  rw [ex_state_def, U_bare_def]
  \\ `in_region (PC s + 2w)`
     by (qpat_x_assum `in_region _` mp_tac \\ qpat_x_assum `(1 >< 0) _ = _` mp_tac
         \\ simp_tac std_ss [in_region_def] \\ blastLib.BBLAST_TAC)
  \\ `(w2n (PC s) MOD 2 = 0) /\ (w2n (PC s + 2w) MOD 2 = 0)`
     by (simp_tac std_ss [align_tests]
         \\ qpat_x_assum `(1 >< 0) _ = _` mp_tac \\ blastLib.BBLAST_TAC)
  \\ `pmpCheck (PC s, 2, PMP_Execute, User) s /\
      pmpCheck (PC s + 2w, 2, PMP_Execute, User) s`
     by metis_tac [pmpCheck_MCSR, ex_pmp_check]
  \\ fs [ex_sd_at_def]
  \\ `FST (Fetch () s) = F_Result (Word 0x0062B023w)`
     by (qspec_then `s` mp_tac Fetch_word \\ asm_simp_tac (srw_ss()) [] \\ EVAL_TAC)
  \\ asm_simp_tac (srw_ss()) [step_inst_def, fetch_inst_def, ex_sd_decode]
QED

(* The state in which the instruction runs is that of s for the registers,
   the CSRs, the privilege and memory *)
Theorem ex_exec_dataAddr:
  !s a n kind.
    ex_state s /\ ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\ (w2n a MOD n = 0) ==>
    (dataAddr (a, n, kind) (exec_state s) =
     if in_region a then TR_Address a
     else TR_Fault (accessFault (Data, if kind = PMP_Read then Read else Write)))
Proof
  rpt strip_tac
  \\ `U_bare (exec_state s) /\ ex_pmp ((exec_state s).c_MCSR (exec_state s).procID)`
     by fs [ex_state_def, U_bare_def, exec_state_priv, exec_state_fields]
  \\ fs [U_bare_def]
  \\ `pmpCheck (a, n, kind, User) (exec_state s) <=> in_region a`
     by metis_tac [pmpCheck_MCSR, ex_pmp_check]
  \\ metis_tac [dataAddr_off]
QED

(* Inside the region the store is allowed: the step writes the 8 bytes of
   x6, little-endian, at the address in x5, changes no other byte, and
   takes no trap *)
Theorem ex_store_inside:
  !s.
    ex_state s /\ in_region (GPR 5w s) /\ ((2 >< 0) (GPR 5w s) = 0w : word3) ==>
    ((Next s).c_privilege = s.c_privilege) /\
    !x. (Next s).MEM8 x =
        if in_range (GPR 5w s) 8 x then (7 >< 0) (GPR 6w s >>> (8 * w2n (x - GPR 5w s)))
        else s.MEM8 x
Proof
  rpt gen_tac
  \\ strip_tac
  \\ drule ex_step_inst
  \\ strip_tac
  \\ drule Next_inst
  \\ disch_then SUBST1_TAC
  \\ `(GPR 5w (exec_state s) = GPR 5w s) /\ (GPR 6w (exec_state s) = GPR 6w s)`
     by metis_tac [GPR_eq, exec_state_fields]
  \\ `dataAddr (GPR 5w s, 8, PMP_Write) (exec_state s) = TR_Address (GPR 5w s)`
     by (qspecl_then [`s`, `GPR 5w s`, `8`, `PMP_Write`] mp_tac ex_exec_dataAddr
         \\ asm_simp_tac std_ss [align_tests])
  \\ `~in32BitMode () (exec_state s)`
     by fs [ex_state_def, in32BitMode_def, MCSR_def, exec_state_fields]
  \\ asm_simp_tac (srw_ss()) [Run_def, dfn'SD_def, LET_THM]
  \\ qabbrev_tac `r = rawWriteData (GPR 5w s, GPR 6w s, 8) (exec_state s)`
  \\ `(r.c_NextFetch = s.c_NextFetch) /\ (r.procID = s.procID) /\
      (r.c_privilege = s.c_privilege)`
     by simp ([Abbr `r`, exec_state_fields] @ frame_thms)
  \\ `r.c_NextFetch r.procID = NONE` by fs [ex_state_def]
  \\ asm_simp_tac (srw_ss()) ([next_post_def, cycle_step_fields] @ frame_thms)
  \\ simp [Abbr `r`, rawWriteData_bytes, exec_state_fields]
QED

(* Outside the region the store is the trap entry of a store access fault
   (code 7, P Table 16 p.50) with the address as the trap value, and
   memory is unchanged *)
Theorem ex_store_outside:
  !s.
    ex_state s /\ ~in_region (GPR 5w s) /\ ((2 >< 0) (GPR 5w s) = 0w : word3) ==>
    ((Next s).MEM8 = s.MEM8) /\
    (Next s =
     cycle_step (takeTrap (F, 7w, PC s, GPR 5w s, excDest (7w, User) s) (exec_state s)))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ drule ex_step_inst
  \\ strip_tac
  \\ drule Next_inst
  \\ disch_then SUBST1_TAC
  \\ `GPR 5w (exec_state s) = GPR 5w s` by metis_tac [GPR_eq, exec_state_fields]
  \\ `dataAddr (GPR 5w s, 8, PMP_Write) (exec_state s) = TR_Fault Store_AMO_Fault`
     by (qspecl_then [`s`, `GPR 5w s`, `8`, `PMP_Write`] mp_tac ex_exec_dataAddr
         \\ asm_simp_tac (srw_ss()) [align_tests, accessFault_def])
  \\ `~in32BitMode () (exec_state s)`
     by fs [ex_state_def, in32BitMode_def, MCSR_def, exec_state_fields]
  \\ asm_simp_tac (srw_ss()) [Run_def, dfn'SD_def, LET_THM, signalAddressException_def,
                              setTrap_def]
  \\ `(exec_state s).c_NextFetch (exec_state s).procID = NONE`
     by fs [ex_state_def, exec_state_fields]
  \\ asm_simp_tac (srw_ss()) [next_post_def, write'NextFetch_def, excCode_def,
                              combinTheory.UPDATE_EQ, combinTheory.APPLY_UPDATE_THM]
  \\ `!t. (t.procID = s.procID) /\ (t.c_PC = s.c_PC) /\ (t.c_MCSR = s.c_MCSR) /\
          (t.c_privilege = s.c_privilege) ==>
          (PC t = PC s) /\ (curPrivilege () t = curPrivilege () s) /\
          (excDest (7w, User) t = excDest (7w, User) s)`
     by simp [PC_def, curPrivilege_def, excDest_def, MCSR_def]
  \\ `(exec_state s with c_NextFetch :=
         ((exec_state s).procID =+ NONE) (exec_state s).c_NextFetch) = exec_state s`
     by (simp [riscv_state_component_equality, FUN_EQ_THM,
               combinTheory.APPLY_UPDATE_THM]
         \\ rw [] \\ fs [])
  \\ fs [ex_state_def, U_bare_def, exec_state_fields, cycle_step_fields]
  \\ simp (exec_state_fields :: frame_thms)
QED
