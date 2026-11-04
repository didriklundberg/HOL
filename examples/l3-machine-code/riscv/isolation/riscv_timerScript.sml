(* ------------------------------------------------------------------------
   The machine timer of the RISC-V L3 model: the timer interrupt by which an
   M-mode kernel takes the hart back from U-mode, two executions in which
   the platform's clock advances, and the commutation of M-mode steps with
   a change of the clock.

   The model has no clock of its own: mtime and mtimecmp are doublewords of
   the CLINT in memory (P §3.2.1 p.59, [D67]), which only an instruction
   that writes memory changes.  The clock of the platform is therefore an
   environment that writes the eight bytes of mtime between steps.

   - mtime_byte, set_mtime: the bytes of mtime, and the clock setting them
     to a value, byte by byte as mtime () reads them; mtime_set_mtime,
     mtimecmp_set_mtime: set_mtime v sets mtime to v and keeps mtimecmp of
     every hart; same_except_set_mtime, same_except_set_mtime_eq,
     set_mtime_id: it changes only the bytes of mtime, gives one result on
     states that differ only there, and keeps a state whose mtime bytes
     are those it writes;
   - tptick, tpexec: the tick-point execution, in which after each step the
     environment may raise mtime, strictly and below a bound, at the
     transitions that a condition C on the pre- and the post-state
     selects; tpexec_shift, tpexec_segment, tpexec_stopped,
     tptick_same_except, mtime_tptick, mtimecmp_tptick: its restart at any
     index, the run of Next before the first selected transition, the
     stopped clock, and what a tick changes;
   - read_mip_MTIP, checkInterrupts_U_timer_pending,
     checkInterrupts_U_timer, Next_U_timer, reg'mcause_timer: in U-mode
     with MTIE set and not delegated, and the machine external and
     software interrupts disabled, a pending timer interrupt is taken into
     M-mode and the step is exactly its trap entry (cause 7, interrupt bit
     set); with every other interrupt disabled, an interrupt is taken
     exactly when the timer interrupt is pending;
   - Next_M_no_interrupt, dfn'WFI_Machine: in M-mode with mstatus.MIE clear
     no interrupt is taken, whatever the memory holds, and WFI in M-mode
     does nothing;
   - clint_csr, noclint_inst and the commutations CSRMap_noclint,
     writeCSR_noclint, accessCSR_noclint, dfn'CSRRW_noclint, ...,
     dfn'CSRRCI_noclint, WFI_M_comm, Run_noclint; Run_reads_M,
     Next_reads_M: an M-mode step with MIE clear that reads no byte of a
     set D maps states that differ only on D to states that differ only on
     D, also when D has CLINT bytes;
   - texec, timer_mono, kstep_noclock, noclock_step, texec_defer,
     texec_defer_read: the hardware execution, in which the clock sets
     mtime before every step, and, along M-mode steps that read the clock
     at most once, its agreement but for the bytes of mtime with the run
     of Next from a state whose mtime is the value that the read sees.

   Like riscv_trapTheory (DESIGN.md I11, I14), this theory has the step
   library's riscv_stepTheory as an ancestor, for takeTrap_Machine,
   read_mip_eval and checkInterrupts_Machine, and opens it qualified only.
   ------------------------------------------------------------------------ *)
Theory riscv_timer
Ancestors
  riscv riscv_footprint riscv_isolation riscv_trap riscv_step[qualified]
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

(* ------------------------------------------------------------------------
   1. The clock sets mtime
   ------------------------------------------------------------------------ *)

(* The eight bytes of mtime in the CLINT (P §3.2.1 p.59, [D67]): the first
   disjunct of clint_byte *)
Definition mtime_byte_def:
  mtime_byte (x : word64) <=> in_range (CLINT_BASE + 0xBFF8w) 8 x
End

(* The clock sets mtime to t: byte i of mtime, at CLINT_BASE + 0xBFF8 + i,
   becomes byte i of t, as mtime () reads the doubleword (little-endian);
   no other byte changes *)
Definition set_mtime_def:
  set_mtime (t : word64) (s : riscv_state) =
    s with MEM8 :=
      (\x. if mtime_byte x then (7 >< 0) (t >>> (8 * w2n (x - (CLINT_BASE + 0xBFF8w))))
           else s.MEM8 x)
End

Theorem same_except_sym:
  !D s1 s2. same_except D s1 s2 ==> same_except D s2 s1
Proof
  rw [same_except_def]
  >- (qpat_x_assum `s2 = _` (fn th => once_rewrite_tac [th])
      \\ simp [MEM8_fupd_id])
  \\ metis_tac []
QED

Theorem same_except_trans:
  !D s1 s2 s3. same_except D s1 s2 /\ same_except D s2 s3 ==> same_except D s1 s3
Proof
  rw [same_except_def]
  >- (qpat_x_assum `s3 = _` (fn th => once_rewrite_tac [th])
      \\ qpat_x_assum `s2 = _` (fn th => once_rewrite_tac [th])
      \\ simp [])
  \\ metis_tac []
QED

Theorem same_except_set_mtime:
  !t s. same_except mtime_byte s (set_mtime t s)
Proof
  rw [set_mtime_def, same_except_upd]
QED

Theorem same_except_set_mtime_eq:
  !v s1 s2. same_except mtime_byte s1 s2 ==> (set_mtime v s1 = set_mtime v s2)
Proof
  rpt strip_tac
  \\ `?m. (s2 = s1 with MEM8 := m) /\ !x. ~mtime_byte x ==> (s1.MEM8 x = m x)`
     by metis_tac [same_except_exists]
  \\ BasicProvers.VAR_EQ_TAC
  \\ simp [set_mtime_def, riscv_state_component_equality, FUN_EQ_THM]
  \\ rw []
QED

(* A state whose mtime bytes are those that set_mtime v writes is kept by
   set_mtime v *)
Theorem set_mtime_id:
  !v s z. (!x. mtime_byte x ==> (z.MEM8 x = (set_mtime v s).MEM8 x)) ==>
          (set_mtime v z = z)
Proof
  rpt strip_tac
  \\ fs [set_mtime_def]
  \\ simp [riscv_state_component_equality, FUN_EQ_THM]
  \\ rw []
QED

Theorem mtime_set_mtime:
  !v s. mtime () (set_mtime v s) = v
Proof
  rpt gen_tac
  \\ simp [mtime_def, MEM_def, set_mtime_def, mtime_byte_def, in_range_def,
           CLINT_BASE_def]
  \\ EVAL_TAC
  \\ blastLib.BBLAST_TAC
QED

Theorem w2n_lt_8[local]:
  !x : word64. w2n x < 8 <=> x <+ 8w
Proof
  simp [wordsTheory.WORD_LO]
QED

(* The bytes of mtime are disjoint from mtimecmp of every hart *)
Theorem mtimecmp_set_mtime:
  !v s h. mtimecmp h (set_mtime v s) = mtimecmp h s
Proof
  rpt gen_tac
  \\ simp [mtimecmp_def, MEM_def, set_mtime_def, mtime_byte_def, in_range_def,
           CLINT_BASE_def, w2n_lt_8]
  \\ rpt (IF_CASES_TAC
          >- (`F` suffices_by simp []
              \\ pop_assum mp_tac
              \\ blastLib.BBLAST_TAC))
  \\ simp []
QED

(* ------------------------------------------------------------------------
   2. The tick-point execution
   ------------------------------------------------------------------------ *)

(* After the step from pre to post, the environment may set mtime to v: if
   the transition is one that C selects, v is above mtime (the clock only
   advances) and below the bound mx; otherwise the tick does nothing *)
Definition tptick_def:
  tptick (C : riscv_state -> riscv_state -> bool) (mx : num) (v : word64)
         (pre : riscv_state) (post : riscv_state) =
    if C pre post /\ mtime () post <+ v /\ w2n v < mx then set_mtime v post
    else post
End

(* The execution of Next from s in which the environment t offers t k after
   step k *)
Definition tpexec_def:
  (tpexec C mx (t : num -> word64) s 0 = s) /\
  (tpexec C mx t s (SUC k) =
     tptick C mx (t k) (tpexec C mx t s k) (Next (tpexec C mx t s k)))
End

(* The execution restarts at any index, with the environment shifted *)
Theorem tpexec_shift:
  !C mx t s j i.
    tpexec C mx t s (j + i) = tpexec C mx (\m. t (j + m)) (tpexec C mx t s j) i
Proof
  ntac 5 gen_tac
  \\ Induct
  \\ asm_simp_tac std_ss [tpexec_def, arithmeticTheory.ADD_CLAUSES]
QED

(* If no transition of the run of Next from x before step d is selected by
   C, the execution from x is that run up to index d (excluded: the
   transition into index d may be selected) *)
Theorem tpexec_segment:
  !C mx t x d.
    (!i. i + 1 < d ==> ~C (FUNPOW Next i x) (FUNPOW Next (SUC i) x)) ==>
    !i. i < d ==> (tpexec C mx t x i = FUNPOW Next i x)
Proof
  ntac 5 gen_tac
  \\ strip_tac
  \\ Induct
  >- simp [tpexec_def]
  \\ strip_tac
  \\ `tpexec C mx t x i = FUNPOW Next i x` by (first_x_assum irule \\ decide_tac)
  \\ `~C (FUNPOW Next i x) (FUNPOW Next (SUC i) x)` by (first_x_assum irule \\ decide_tac)
  \\ fs [tpexec_def, tptick_def, arithmeticTheory.FUNPOW_SUC]
QED

(* With the stopped clock no tick happens: the execution is the run of
   Next *)
Theorem tpexec_stopped:
  !C mx s k. tpexec C mx (K 0w) s k = FUNPOW Next k s
Proof
  ntac 3 gen_tac
  \\ Induct
  \\ simp [tpexec_def, tptick_def, arithmeticTheory.FUNPOW_SUC, wordsTheory.WORD_LO]
QED

(* A tick changes only the eight bytes of mtime *)
Theorem tptick_same_except:
  !C mx v pre post. same_except mtime_byte post (tptick C mx v pre post)
Proof
  rw [tptick_def, set_mtime_def, same_except_upd, same_except_refl]
QED

Theorem mtime_tptick:
  !C mx v pre post.
    mtime () (tptick C mx v pre post) =
    if C pre post /\ mtime () post <+ v /\ w2n v < mx then v else mtime () post
Proof
  rw [tptick_def, mtime_set_mtime]
QED

Theorem mtimecmp_tptick:
  !C mx v pre post h. mtimecmp h (tptick C mx v pre post) = mtimecmp h post
Proof
  rw [tptick_def, mtimecmp_set_mtime]
QED

(* ------------------------------------------------------------------------
   3. The timer interrupt
   ------------------------------------------------------------------------ *)

(* MTIP, bit 7 of mip as read_mip reads it, is set exactly when mtime has
   reached mtimecmp of the hart (P §3.1.9 p.43-45, §3.2.1 p.59, [D67]) *)
Theorem read_mip_MTIP:
  !s. read_mip () s && 128w = if mtimecmp s.procID s <=+ mtime () s then 128w else 0w
Proof
  gen_tac
  \\ simp [riscv_stepTheory.read_mip_eval]
  \\ Cases_on `mtimecmp s.procID s <=+ mtime () s`
  \\ asm_simp_tac std_ss []
  \\ rw []
  \\ blastLib.BBLAST_TAC
QED

(* In U-mode an interrupt that is pending, enabled in mie and not delegated
   in mideleg is taken into M-mode, whatever mstatus.MIE is, and the one of
   highest priority among them is taken: MEI, MSI, MTI, then SEI, SSI, STI
   (P §3.1.9 p.43-45).  So with MTIE set and not delegated, and MEIE and
   MSIE clear, a pending timer interrupt is the one taken. *)
Theorem checkInterrupts_U_timer_pending:
  !s. (curPrivilege () s = User) /\ word_bit 7 (reg'mie (s.c_MCSR s.procID).mie) /\
      ~word_bit 7 (s.c_MCSR s.procID).mideleg /\
      (reg'mie (s.c_MCSR s.procID).mie && 0x808w = 0w) /\
      (mtimecmp s.procID s <=+ mtime () s) ==>
      (checkInterrupts () s = SOME (MTI, Machine))
Proof
  rpt strip_tac
  \\ asm_simp_tac (srw_ss())
       [checkInterrupts_def, riscv_stepTheory.read_mip_eval, MCSR_def, LET_THM]
  \\ rw [highestInterrupt_def]
  \\ rpt (pop_assum mp_tac)
  \\ blastLib.BBLAST_TAC
QED

(* With MTIE set and not delegated and the other five interrupt-enable bits
   of mie (MEIE, SEIE, STIE, MSIE, SSIE) clear, a U-mode state takes an
   interrupt exactly when the timer interrupt is pending, and it is taken
   into M-mode *)
Theorem checkInterrupts_U_timer:
  !s. (curPrivilege () s = User) /\ word_bit 7 (reg'mie (s.c_MCSR s.procID).mie) /\
      ~word_bit 7 (s.c_MCSR s.procID).mideleg /\
      (reg'mie (s.c_MCSR s.procID).mie && 0xA2Aw = 0w) ==>
      (checkInterrupts () s =
         if mtimecmp s.procID s <=+ mtime () s then SOME (MTI, Machine) else NONE)
Proof
  rpt strip_tac
  \\ Cases_on `mtimecmp s.procID s <=+ mtime () s`
  \\ asm_simp_tac (srw_ss())
       [checkInterrupts_def, riscv_stepTheory.read_mip_eval, MCSR_def, LET_THM]
  \\ rw [highestInterrupt_def]
  \\ rpt (pop_assum mp_tac)
  \\ blastLib.BBLAST_TAC
QED

(* The step from U-mode that takes the timer interrupt into M-mode is
   exactly its trap entry (P §3.1.14-3.1.16 p.48-53, §3.1.6.1 p.32,
   §3.1.7 p.41): the step runs no instruction (an interrupt is taken
   before the fetch, P §3.1.14 p.49, [D38]); the privilege becomes M and
   the pc the trap vector of mtvec for interrupt 7; mcause becomes code 7
   with the interrupt bit set (Table 16 p.50), mepc the pc of the
   instruction not run and mtval 0; MPIE becomes MIE, MIE becomes 0 and MPP
   U.  No other M-level CSR, no S-level CSR, no GPR or FPR, no memory, and
   neither the load reservation (the model keeps it on a trap, [D45]),
   NextFetch nor the exception field changes. *)
Theorem Next_U_timer:
  !s. (curPrivilege () s = User) /\ word_bit 7 (reg'mie (s.c_MCSR s.procID).mie) /\
      ~word_bit 7 (s.c_MCSR s.procID).mideleg /\
      (reg'mie (s.c_MCSR s.procID).mie && 0x808w = 0w) /\
      (mtimecmp s.procID s <=+ mtime () s) ==>
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
  rpt gen_tac
  \\ strip_tac
  \\ `checkInterrupts () s = SOME (MTI, Machine)`
     by (irule checkInterrupts_U_timer_pending \\ asm_rewrite_tac [])
  \\ conj_tac
  >- simp [step_inst_def]
  \\ imp_res_tac Next_interrupt
  \\ qpat_x_assum `Next s = _` SUBST1_TAC
  \\ `(s.c_privilege s.procID = 0w) \/ (s.c_privilege s.procID = 2w)`
     by metis_tac [curPrivilege_User]
  \\ simp [riscv_stepTheory.takeTrap_Machine, cycle_step_def, next_pre_def,
           interruptIndex_def, PC_def]
  \\ rw [combinTheory.UPDATE_APPLY, combinTheory.UPDATE_EQ]
  \\ fs [MachineCSR_component_equality, mstatus_component_equality]
  \\ rw [combinTheory.APPLY_UPDATE_THM]
  \\ fs [MachineCSR_component_equality, mstatus_component_equality]
QED

(* mcause as a word: Int in bit 63 and the exception code below it
   (P §3.1.15 Figure 22 p.49); the machine timer interrupt is
   0x8000000000000007 *)
Theorem reg'mcause_timer:
  !c. (reg'mcause c = 0x8000000000000007w) <=> (c.EC = 7w) /\ c.Int
Proof
  Cases
  \\ simp [reg'mcause_def]
  \\ blastLib.BBLAST_TAC
QED

(* In M-mode an interrupt into M-mode is enabled only when mstatus.MIE is
   set, and none goes to S-mode (P §3.1.6.1 p.32, §3.1.9 p.43-45): with MIE
   clear no interrupt is taken, whatever the memory, and so the CLINT,
   holds, and the step runs an instruction *)
Theorem Next_M_no_interrupt:
  !s m. (s.c_privilege s.procID = 3w) /\ ~(s.c_MCSR s.procID).mstatus.MIE ==>
        (checkInterrupts () (s with MEM8 := m) = NONE) /\
        IS_SOME (step_inst (s with MEM8 := m))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `checkInterrupts () (s with MEM8 := m) = NONE`
     by (irule riscv_stepTheory.checkInterrupts_Machine \\ simp [])
  \\ simp [step_inst_def]
QED

(* WFI in M-mode is a no-op (P §3.3.3 p.62 allows it): it does not wait
   for an interrupt *)
Theorem dfn'WFI_Machine:
  !s. (curPrivilege () s = Machine) ==> (dfn'WFI s = s)
Proof
  simp [dfn'WFI_def]
QED

(* ------------------------------------------------------------------------
   4. M-mode steps that read no byte of a set of bytes
   ------------------------------------------------------------------------ *)

(* The CSRs whose read reads the CLINT: time (0xC01), which is mtime, and
   mip (0x344) and sip (0x144), whose MSIP and MTIP read_mip computes from
   the CLINT (P §3.1.9 p.43-45, [D67]) *)
Definition clint_csr_def:
  clint_csr (c : word12) <=> (c = 0xC01w) \/ (c = 0x344w) \/ (c = 0x144w)
End

(* A read of any other CSR does not read memory *)
Theorem CSRMap_noclint:
  !s m csr. ~clint_csr csr ==>
    (CSRMap csr (s with MEM8 := m) = (FST (CSRMap csr s), SND (CSRMap csr s) with MEM8 := m))
Proof
  rpt strip_tac
  \\ fs [clint_csr_def]
  \\ asm_simp_tac (srw_ss()) [CSRMap_def, MCSR_MEM8, read_xepc_MEM8, raise'exception_MEM8]
  \\ rpt (CASE_TAC
          \\ asm_simp_tac (srw_ss()) [MCSR_MEM8, read_xepc_MEM8, raise'exception_MEM8])
  \\ fs []
QED

Theorem writeCSR_noclint:
  !s m csr v. ~clint_csr csr ==>
    (writeCSR (csr, v) (s with MEM8 := m) = writeCSR (csr, v) s with MEM8 := m)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [writeCSR_def, LET_THM, pairTheory.UNCURRY, write'CSR_MEM8,
                      Delta_MEM8, write'Delta_MEM8]
  \\ asm_simp_tac std_ss [CSR_def, CSRMap_noclint, write'Delta_MEM8]
QED

Theorem accessCSR_noclint:
  !s m op rd f src csr. ~clint_csr csr ==>
    (accessCSR (op, rd, f, src, csr) (s with MEM8 := m) =
     accessCSR (op, rd, f, src, csr) s with MEM8 := m)
Proof
  rpt strip_tac
  \\ `csr <> 836w` by fs [clint_csr_def]
  \\ simp_tac std_ss [accessCSR_def, LET_THM, pairTheory.UNCURRY, checkCSROp_MEM8]
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [signalException_MEM8, CSR_def, CSRMap_noclint]
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [writeCSR_noclint, MCSR_MEM8, write'GPR_MEM8]
QED

(* dfn'CSRRW_noclint, ..., dfn'CSRRCI_noclint: the six CSR instructions on
   a CSR other than time, mip and sip commute with replacing the memory *)
local
  fun csr_comm nm =
    let
      val c = prim_mk_const {Name = nm, Thy = "riscv"}
      val argty = fst (dom_rng (type_of c))
      val (t1, t2, t3) = case pairSyntax.strip_prod argty of
                           [t1, t2, t3] => (t1, t2, t3)
                         | _ => raise mk_HOL_ERR "riscv_timer" "csr_comm" nm
      val a = mk_var ("a", t1)
      val b = mk_var ("b", t2)
      val cc = mk_var ("c", t3)
      val args = pairSyntax.list_mk_pair [a, b, cc]
      val g = ``!s m. ~clint_csr ^cc ==>
                      (^c ^args (s with MEM8 := m) = ^c ^args s with MEM8 := m)``
      val th = Q.prove (`!^a ^b ^cc. ^g`,
                 rpt strip_tac
                 \\ asm_simp_tac std_ss [DB.fetch "riscv" (nm ^ "_def"), GPR_MEM8,
                                         accessCSR_noclint, LET_THM])
    in
      save_thm (nm ^ "_noclint", th)
    end
in
  val csr_comms =
    map csr_comm ["dfn'CSRRW", "dfn'CSRRS", "dfn'CSRRC", "dfn'CSRRWI", "dfn'CSRRSI",
                  "dfn'CSRRCI"]
end

Theorem WFI_M_comm:
  !s m. (curPrivilege () s = Machine) ==>
        (dfn'WFI (s with MEM8 := m) = dfn'WFI s with MEM8 := m)
Proof
  rpt strip_tac
  \\ `curPrivilege () (s with MEM8 := m) = Machine` by fs [curPrivilege_def]
  \\ asm_simp_tac (srw_ss()) [dfn'WFI_def]
QED

(* The instructions of clint_inst (the CSR instructions and WFI, which may
   read the CLINT) that read no memory: a CSR instruction on a CSR other
   than time, mip and sip, and WFI in M-mode *)
Definition noclint_inst_def:
  (noclint_inst (System (CSRRW (rd, rs1, c))) (s : riscv_state) <=> ~clint_csr c) /\
  (noclint_inst (System (CSRRS (rd, rs1, c))) s <=> ~clint_csr c) /\
  (noclint_inst (System (CSRRC (rd, rs1, c))) s <=> ~clint_csr c) /\
  (noclint_inst (System (CSRRWI (rd, i, c))) s <=> ~clint_csr c) /\
  (noclint_inst (System (CSRRSI (rd, i, c))) s <=> ~clint_csr c) /\
  (noclint_inst (System (CSRRCI (rd, i, c))) s <=> ~clint_csr c) /\
  (noclint_inst (System WFI) s <=> (curPrivilege () s = Machine)) /\
  (noclint_inst _ s <=> F)
End

Theorem Run_noclint:
  !i s m. noclint_inst i s ==> (Run i (s with MEM8 := m) = Run i s with MEM8 := m)
Proof
  Cases
  \\ simp [noclint_inst_def]
  \\ rename1 `System sy`
  \\ Cases_on `sy`
  \\ simp [noclint_inst_def, Run_def]
  \\ TRY (PairCases_on `p`)
  \\ simp [noclint_inst_def, Run_def]
  \\ rpt strip_tac
  \\ FIRST (map (fn th => irule th \\ simp [] \\ NO_TAC) (WFI_M_comm :: csr_comms))
QED

Theorem noclint_mem_access:
  !i s t. noclint_inst i s ==> (mem_access i t = NONE)
Proof
  Cases
  \\ simp [noclint_inst_def]
  \\ rename1 `System sy`
  \\ Cases_on `sy`
  \\ simp [noclint_inst_def, mem_access_def]
  \\ TRY (PairCases_on `p`)
  \\ simp [noclint_inst_def, mem_access_def]
QED

Theorem noclint_inst_priv:
  !i s t. (curPrivilege () t = curPrivilege () s) ==>
          (noclint_inst i t = noclint_inst i s)
Proof
  Cases
  \\ simp [noclint_inst_def]
  \\ rename1 `System sy`
  \\ Cases_on `sy`
  \\ simp [noclint_inst_def]
  \\ TRY (PairCases_on `p`)
  \\ simp [noclint_inst_def]
QED

(* Run_reads of riscv_footprintTheory, with no hypothesis on the CLINT for
   the CSR instructions on CSRs other than time, mip and sip and for WFI in
   M-mode, which read no CLINT byte *)
Theorem Run_reads_M:
  !i D s1 s2.
    same_except D s1 s2 /\
    (!acc x. (mem_access i s1 = SOME acc) /\ (SND (SND acc) <> PMP_Write) /\
             data_bytes acc s1 x ==> ~D x) /\
    (!acc. (mem_access i s1 = SOME acc) ==> (dataAddr acc s2 = dataAddr acc s1)) /\
    (clint_inst i /\ ~noclint_inst i s1 ==> !x. clint_byte s1.procID x ==> ~D x) ==>
    same_except D (Run i s1) (Run i s2)
Proof
  rpt strip_tac
  \\ Cases_on `noclint_inst i s1`
  >- (`?m. (s2 = s1 with MEM8 := m) /\ !x. ~D x ==> (s1.MEM8 x = m x)`
        by metis_tac [same_except_exists]
      \\ BasicProvers.VAR_EQ_TAC
      \\ asm_simp_tac std_ss [Run_noclint, same_except_upd]
      \\ `mem_access i s1 = NONE` by metis_tac [noclint_mem_access]
      \\ `(Run i s1).MEM8 = s1.MEM8` by metis_tac [Run_MEM8_frame]
      \\ asm_simp_tac std_ss [])
  \\ irule Run_reads
  \\ fs []
QED

Theorem cycle_next_post_comm[local]:
  !b v t m. cycle_step (next_post b (v, t with MEM8 := m)) =
            cycle_step (next_post b (v, t)) with MEM8 := m
Proof
  simp [next_post_MEM8, cycle_step_MEM8]
QED

(* curPrivilege reads privilege 3 as M-mode, and nothing else *)
Theorem curPrivilege_Machine:
  !s. (curPrivilege () s = Machine) <=> (s.c_privilege s.procID = 3w)
Proof
  gen_tac
  \\ simp [curPrivilege_def]
  \\ wordsLib.Cases_on_word_value `s.c_privilege s.procID`
  \\ simp [privilege_def]
QED

(* An M-mode step with MIE clear (it takes no interrupt, whatever the CLINT
   holds: Next_M_no_interrupt) from two states that are equal but for the
   bytes of D, none of which the step reads (the fetched parcels, the data
   that the instruction reads, and the CLINT bytes that a CSR instruction
   on time, mip or sip, or WFI outside M-mode, reads), gives two states
   that are equal but for the bytes of D.  Unlike Next_reads of
   riscv_isolationTheory, D may contain the CLINT bytes that the interrupt
   check reads.  The effective privilege M puts translation off for the
   data access. *)
Theorem Next_reads_M:
  !D s1 s2.
    (curPrivilege () s1 = Machine) /\ ~(s1.c_MCSR s1.procID).mstatus.MIE /\
    (effectivePrivilege () s1 = Machine) /\
    same_except D s1 s2 /\
    (!x. fetch_bytes s1 x ==> ~D x) /\
    (!i acc x. (step_inst s1 = SOME i) /\ (mem_access i s1 = SOME acc) /\
               (SND (SND acc) <> PMP_Write) /\ data_bytes acc s1 x ==> ~D x) /\
    (!i. (step_inst s1 = SOME i) /\ clint_inst i /\ ~noclint_inst i s1 ==>
         !x. clint_byte s1.procID x ==> ~D x) ==>
    same_except D (Next s1) (Next s2)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `?m. (s2 = s1 with MEM8 := m) /\ !x. ~D x ==> (s1.MEM8 x = m x)`
     by metis_tac [same_except_exists]
  \\ BasicProvers.VAR_EQ_TAC
  \\ `s1.c_privilege s1.procID = 3w` by metis_tac [curPrivilege_Machine]
  \\ `checkInterrupts () s1 = NONE`
     by (irule riscv_stepTheory.checkInterrupts_Machine \\ fs [])
  \\ `checkInterrupts () (s1 with MEM8 := m) = NONE`
     by (irule riscv_stepTheory.checkInterrupts_Machine \\ fs [])
  \\ asm_simp_tac (srw_ss()) [Next_split, next_pre_MEM8, fetchAndExecute_eq, haveRVC_MEM8]
  \\ qabbrev_tac `t1 = next_pre s1`
  \\ `(t1.MEM8 = s1.MEM8) /\ (t1.procID = s1.procID) /\ (t1.c_MCSR = s1.c_MCSR) /\
      (t1.c_SCSR = s1.c_SCSR) /\ (t1.c_privilege = s1.c_privilege) /\
      (t1.c_gpr = s1.c_gpr)`
     by simp [Abbr `t1`, next_pre_def]
  \\ `same_except D t1 (t1 with MEM8 := m)` by asm_simp_tac std_ss [same_except_upd]
  \\ `(curPrivilege () t1 = curPrivilege () s1) /\
      (effectivePrivilege () t1 = effectivePrivilege () s1)`
     by metis_tac [effectivePrivilege_eq]
  \\ `!a. fetchAddr a (t1 with MEM8 := m) = fetchAddr a t1`
     by metis_tac [fetchAddr_off_MEM8]
  \\ `!x. fetch_bytes t1 x ==> ~D x` by metis_tac [fetch_bytes_next_pre]
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
  \\ `(effectivePrivilege () (exec_state s1) = Machine) /\
      (curPrivilege () (exec_state s1) = Machine)` by metis_tac [exec_state_priv]
  \\ `same_except D (Run i u1) (Run i u2)`
     by (irule Run_reads_M
         \\ asm_simp_tac std_ss []
         \\ rpt conj_tac
         >- (rpt strip_tac
             \\ `mem_access i (exec_state s1) = mem_access i s1`
                by (irule mem_access_eq \\ simp_tac std_ss [exec_state_fields])
             \\ `data_bytes acc (exec_state s1) x <=> data_bytes acc s1 x`
                by (irule data_bytes_exec \\ asm_simp_tac std_ss [])
             \\ metis_tac [])
         >- (rpt strip_tac
             \\ qpat_assum `same_except D u1 u2`
                  (strip_assume_tac o REWRITE_RULE [same_except_def])
             \\ qpat_x_assum `u2 = _` SUBST1_TAC
             \\ qpat_x_assum `u1 = exec_state s1` SUBST1_TAC
             \\ PairCases_on `acc`
             \\ irule dataAddr_off_MEM8
             \\ asm_rewrite_tac [])
         \\ rpt strip_tac
         \\ `noclint_inst i (exec_state s1) = noclint_inst i s1`
            by metis_tac [noclint_inst_priv]
         \\ fs [exec_state_fields]
         \\ metis_tac [])
  \\ irule
       (BETA_RULE
          (Q.ISPEC
             `\t. cycle_step (next_post (~word_bit 2 (s1.c_MCSR s1.procID).mcountinhibit)
                                (fetch_bits (FST (Fetch () t1)), t))`
             same_except_inert))
  \\ asm_simp_tac std_ss [cycle_next_post_comm]
QED

(* ------------------------------------------------------------------------
   5. The hardware execution
   ------------------------------------------------------------------------ *)

(* The execution in which the clock ck sets mtime to ck k before step k *)
Definition texec_def:
  (texec (ck : num -> word64) s 0 = s) /\
  (texec ck s (SUC k) = Next (set_mtime (ck k) (texec ck s k)))
End

(* A clock that never goes back *)
Definition timer_mono_def:
  timer_mono (ck : num -> word64) <=> !k. ck k <=+ ck (SUC k)
End

Theorem timer_mono_le:
  !ck. timer_mono ck ==> !i j. i <= j ==> ck i <=+ ck j
Proof
  gen_tac
  \\ strip_tac
  \\ gen_tac
  \\ Induct
  >- (strip_tac
      \\ `i = 0` by decide_tac
      \\ simp [wordsTheory.WORD_LOWER_EQ_REFL])
  \\ strip_tac
  \\ Cases_on `i = SUC j`
  >- simp [wordsTheory.WORD_LOWER_EQ_REFL]
  \\ `i <= j` by decide_tac
  \\ `ck j <=+ ck (SUC j)` by fs [timer_mono_def]
  \\ metis_tac [wordsTheory.WORD_LOWER_EQ_TRANS]
QED

(* An M-mode step with MIE clear and the effective privilege M (so with
   translation off) that reads no byte of mtime: no fetched byte and no
   byte of the data that its instruction reads is one, and if its
   instruction is one that may read the CLINT (clint_inst), it reads no
   memory (noclint_inst) *)
Definition kstep_noclock_def:
  kstep_noclock (s : riscv_state) <=>
    (curPrivilege () s = Machine) /\ ~(s.c_MCSR s.procID).mstatus.MIE /\
    (effectivePrivilege () s = Machine) /\
    (!x. fetch_bytes s x ==> ~mtime_byte x) /\
    (!i acc x. (step_inst s = SOME i) /\ (mem_access i s = SOME acc) /\
               (SND (SND acc) <> PMP_Write) /\ data_bytes acc s x ==> ~mtime_byte x) /\
    (!i. (step_inst s = SOME i) /\ clint_inst i ==> noclint_inst i s)
End

(* A tick before a step that does not read the clock does not matter: the
   steps from h with the clock set and from z, equal to h but for the bytes
   of mtime, give states that are equal but for the bytes of mtime *)
Theorem noclock_step:
  !v h z. same_except mtime_byte h z /\ kstep_noclock z ==>
          same_except mtime_byte (Next (set_mtime v h)) (Next z)
Proof
  rpt strip_tac
  \\ irule same_except_sym
  \\ irule Next_reads_M
  \\ fs [kstep_noclock_def]
  \\ metis_tac [same_except_trans, same_except_sym, same_except_set_mtime]
QED

(* Along a segment of steps that do not read the clock after its first one,
   the hardware execution is, up to the bytes of mtime, the run of Next
   from the state at the start of the segment with the clock set by its
   first tick *)
Theorem texec_defer:
  !ck s0 j d.
    (!i. 0 < i /\ i <= d ==> kstep_noclock (FUNPOW Next i (set_mtime (ck j) (texec ck s0 j)))) ==>
    same_except mtime_byte (texec ck s0 (j + SUC d))
                           (FUNPOW Next (SUC d) (set_mtime (ck j) (texec ck s0 j)))
Proof
  ntac 3 gen_tac
  \\ Induct
  >- simp [texec_def, GSYM arithmeticTheory.ADD1, same_except_refl]
  \\ strip_tac
  \\ qabbrev_tac `x = set_mtime (ck j) (texec ck s0 j)`
  \\ `same_except mtime_byte (texec ck s0 (j + SUC d)) (FUNPOW Next (SUC d) x)`
     by (first_x_assum irule \\ rpt strip_tac \\ first_x_assum irule \\ simp [])
  \\ `kstep_noclock (FUNPOW Next (SUC d) x)` by (first_x_assum irule \\ simp [])
  \\ `j + SUC (SUC d) = SUC (j + SUC d)` by simp []
  \\ `FUNPOW Next (SUC (SUC d)) x = Next (FUNPOW Next (SUC d) x)`
     by simp [arithmeticTheory.FUNPOW_SUC]
  \\ asm_rewrite_tac [texec_def]
  \\ qabbrev_tac `y = FUNPOW Next (SUC d) x`
  \\ qabbrev_tac `z = set_mtime (ck (j + SUC d)) (texec ck s0 (j + SUC d))`
  \\ `same_except mtime_byte y z`
     by metis_tac [same_except_trans, same_except_sym, same_except_set_mtime]
  \\ irule same_except_sym
  \\ irule Next_reads_M
  \\ fs [kstep_noclock_def]
  \\ metis_tac []
QED

(* The deferral with the read anywhere in the segment: along d + 1 steps
   from index j of the hardware execution, of which only step r may read
   the clock (every other step is kstep_noclock) and none before it writes
   a byte of mtime, the hardware execution is, up to the bytes of mtime,
   the run of Next from the state at index j with mtime set to the value
   ck (j + r) that the read sees *)
Theorem texec_defer_read:
  !ck s0 j r d y.
    (set_mtime (ck (j + r)) (texec ck s0 j) = y) /\ r <= d /\
    (!i. i <= d /\ i <> r ==> kstep_noclock (FUNPOW Next i y)) /\
    (!i x. i < r /\ mtime_byte x ==>
           ((FUNPOW Next (SUC i) y).MEM8 x = (FUNPOW Next i y).MEM8 x)) ==>
    same_except mtime_byte (texec ck s0 (j + SUC d)) (FUNPOW Next (SUC d) y)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `!i. (i <= r ==> same_except mtime_byte (texec ck s0 (j + i)) (FUNPOW Next i y) /\
                      !x. mtime_byte x ==> ((FUNPOW Next i y).MEM8 x = y.MEM8 x)) /\
          (r < i /\ i <= SUC d ==>
           same_except mtime_byte (texec ck s0 (j + i)) (FUNPOW Next i y))`
     suffices_by (disch_then (qspec_then `SUC d` mp_tac) \\ simp [])
  \\ Induct
  >- (simp [] \\ metis_tac [same_except_set_mtime])
  \\ `texec ck s0 (j + SUC i) = Next (set_mtime (ck (j + i)) (texec ck s0 (j + i)))`
     by simp [arithmeticTheory.ADD_CLAUSES, texec_def]
  \\ `FUNPOW Next (SUC i) y = Next (FUNPOW Next i y)` by simp [arithmeticTheory.FUNPOW_SUC]
  \\ Cases_on `i < r`
  >- ((* before the read *)
      `i <= r /\ i <= d /\ i <> r /\ ~(r < SUC i)` by decide_tac
      \\ `kstep_noclock (FUNPOW Next i y)` by metis_tac []
      \\ `same_except mtime_byte (texec ck s0 (j + i)) (FUNPOW Next i y) /\
          !x. mtime_byte x ==> ((FUNPOW Next i y).MEM8 x = y.MEM8 x)` by metis_tac []
      \\ `!x. mtime_byte x ==> ((FUNPOW Next (SUC i) y).MEM8 x = (FUNPOW Next i y).MEM8 x)`
         by metis_tac []
      \\ asm_rewrite_tac []
      \\ rpt strip_tac
      >- (irule noclock_step \\ asm_rewrite_tac [])
      \\ metis_tac [])
  \\ Cases_on `i = r`
  >- ((* the read: the two states are equal *)
      `same_except mtime_byte (texec ck s0 (j + i)) (FUNPOW Next i y) /\
       !x. mtime_byte x ==> ((FUNPOW Next i y).MEM8 x = y.MEM8 x)`
         by metis_tac [arithmeticTheory.LESS_EQ_REFL]
      \\ `set_mtime (ck (j + i)) (texec ck s0 (j + i)) =
          set_mtime (ck (j + i)) (FUNPOW Next i y)`
         by metis_tac [same_except_set_mtime_eq]
      \\ `set_mtime (ck (j + i)) (FUNPOW Next i y) = FUNPOW Next i y`
         by (irule set_mtime_id \\ qexists_tac `texec ck s0 j` \\ metis_tac [])
      \\ `texec ck s0 (j + SUC i) = FUNPOW Next (SUC i) y` by metis_tac []
      \\ conj_tac
      >- (strip_tac \\ `F` by decide_tac)
      \\ strip_tac
      \\ metis_tac [same_except_refl])
  \\ (* after the read *)
  `r < i` by decide_tac
  \\ conj_tac
  >- (strip_tac \\ `F` by decide_tac)
  \\ strip_tac
  \\ `i <= d /\ i <> r /\ i <= SUC d` by decide_tac
  \\ `kstep_noclock (FUNPOW Next i y)` by metis_tac []
  \\ `same_except mtime_byte (texec ck s0 (j + i)) (FUNPOW Next i y)` by metis_tac []
  \\ `same_except mtime_byte (Next (set_mtime (ck (j + i)) (texec ck s0 (j + i))))
                             (Next (FUNPOW Next i y))`
     by (irule noclock_step \\ asm_rewrite_tac [])
  \\ metis_tac []
QED
