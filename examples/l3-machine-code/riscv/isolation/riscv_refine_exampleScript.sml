(* ------------------------------------------------------------------------
   The refinement lemma of riscv_refineTheory on step theorems of the step
   library.

   For an instruction word, riscv_stepLib gives the M-mode step theorem

     hyps |- NextRISCV s = SOME s'

   and Next_NextRISCV_ghost turns it into a step of the spec's Next: the
   no-interrupt hypothesis follows from hyps (privilege M and mstatus.MIE
   clear, riscv_stepTheory.checkInterrupts_Machine), and the fetch
   hypothesis from the instruction bytes in hyps (riscv_stepTheory.Fetch32
   and Fetch16) and the decoding of the instruction, which reads no counter
   CSR.  What is left is

     hyps |- !s0. ghost_eq s0 s ==> ghost_eq (Next s0) s'

   with no hypothesis beyond those of the step theorem (checked).  This is
   done for csrw pmpcfg0, sd, c.jr, beq and mret.  A read of the cycle
   counter is refused: its instruction reads a counter CSR, so the fetch
   hypothesis does not hold.
   ------------------------------------------------------------------------ *)
Theory riscv_refine_example
Ancestors
  riscv riscv_refine riscv_step[qualified]
Libs
  riscv_stepLib

val _ = ParseExtras.temp_loose_equality ()
val ERR = mk_HOL_ERR "riscv_refine_exampleTheory"

val s_tm = ``s : riscv_state``
val s0_tm = ``s0 : riscv_state``

(* the bits of an instruction given in hex, most significant first *)
fun bits_of hex =
  let
    val (l, _) = listSyntax.dest_list (bitstringSyntax.bitstring_of_hexstring hex)
  in
    utilsLib.padLeft boolSyntax.F (if String.size hex > 4 then 32 else 16) l
  end

(* The fetch of the instruction in the state of its step theorem: Fetch32 or
   Fetch16, with their hypotheses discharged by those of the step theorem *)
fun fetch_thm hex step =
  let
    val bits = bits_of hex
    val xs = listSyntax.mk_list (bits, bool)
    val th0 = SPEC_ALL (if length bits = 32 then riscv_stepTheory.Fetch32
                        else riscv_stepTheory.Fetch16)
    val (ant0, _) = dest_imp (concl th0)
    val (xs_var, pat) = dest_eq (hd (strip_conj ant0))
    val (sub, _) = match_term pat xs
    val th = INST ((xs_var |-> xs) :: sub) th0
    val (ant, _) = dest_imp (concl th)
  in
    MP th (TAC_PROOF ((hyp step, ant), asm_simp_tac std_ss []))
  end

(* Under the hypotheses of the step theorem, the fetched instruction, as
   the step library decodes it (riscv_decode_hex), reads no counter CSR *)
fun no_counter_thm hex step =
  let
    val fetch = fetch_thm hex step
    val rvc = ``haveRVC () ^s_tm``
    val dec = INST [``rvc : bool`` |-> rvc] (riscv_stepLib.riscv_decode_hex hex)
    val dec =
      if null (hyp dec) then dec
      else PROVE_HYP (TAC_PROOF ((hyp step, rvc),
                        asm_simp_tac std_ss [haveRVC_def, MCSR_def])) dec
    val g = ``!w t1. (riscv_step$Fetch ^s_tm = (w, t1)) ==>
                     ~reads_counter (DecodeAny ^rvc w)``
  in
    TAC_PROOF ((hyp step, g),
      rpt gen_tac
      \\ rewrite_tac [fetch, pairTheory.PAIR_EQ]
      \\ strip_tac
      \\ rpt BasicProvers.VAR_EQ_TAC
      \\ rewrite_tac [dec]
      \\ EVAL_TAC)
  end

(* The instance of Next_NextRISCV_ghost on the step theorem of an instruction *)
fun refine hex =
  let
    val step = riscv_stepLib.riscv_step_hex hex
    val s' = optionSyntax.dest_some (rhs (concl step))
    val no_interrupt =
      MP riscv_stepTheory.checkInterrupts_Machine
         (CONJ (ASSUME ``^s_tm.c_privilege ^s_tm.procID = 3w``)
               (ASSUME ``~(^s_tm.c_MCSR ^s_tm.procID).mstatus.MIE``))
    val geq = ``ghost_eq ^s0_tm ^s_tm``
    val th =
      MP (SPECL [s0_tm, s_tm, s'] Next_NextRISCV_ghost)
         (LIST_CONJ [ASSUME geq, no_interrupt, no_counter_thm hex step, step])
      |> DISCH geq |> GEN s0_tm
    val () =
      if HOLset.isSubset (hypset th, hypset step) then ()
      else raise ERR "refine" (hex ^ ": a hypothesis that the step theorem does not have")
  in
    th
  end

(* hyps |- c  as  !s. h1 /\ ... /\ hn ==> c *)
fun close th =
  let
    val c = list_mk_conj (hyp th)
  in
    GEN s_tm (DISCH c (List.foldl (uncurry PROVE_HYP) th (CONJUNCTS (ASSUME c))))
  end

fun save (name, hex) =
  let
    val th = save_thm (name, close (refine hex))
  in
    print ("riscv_refine_example: " ^ name ^ " (" ^ hex ^ ")\n")
  end

val () =
  List.app save
    [("csrw_pmpcfg0_refine", "3A029073"),   (* csrrw x0, pmpcfg0, x5 *)
     ("sd_refine", "0062B023"),             (* sd x6, 0(x5) *)
     ("c_jr_refine", "8082"),               (* c.jr x1 *)
     ("beq_refine", "00000463"),            (* beq x0, x0, 8 *)
     ("mret_refine", "30200073")]           (* mret *)

(* csrrs x10, cycle, x0 (csrr a0, cycle) reads the cycle counter, which Next
   counts and NextRISCV does not: the step library has a step theorem for
   it, but the lemma does not apply *)
Theorem cycle_read_refused:
  !rvc. reads_counter (DecodeAny rvc (Word 0xC0002573w))
Proof
  gen_tac
  \\ `(0xC0002573w : word32) =
      v2w ^(listSyntax.mk_list (bits_of "C0002573", bool))` by EVAL_TAC
  \\ pop_assum SUBST1_TAC
  \\ rewrite_tac [riscv_stepLib.riscv_decode_hex "C0002573"]
  \\ EVAL_TAC
QED

val () =
  let
    val step = riscv_stepLib.riscv_step_hex "C0002573"
  in
    if can (no_counter_thm "C0002573") step then
      raise ERR "cycle_read_refused" "the lemma applied to a read of cycle"
    else print "riscv_refine_example: a read of cycle is refused\n"
  end
