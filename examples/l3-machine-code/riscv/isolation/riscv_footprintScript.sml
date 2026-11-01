(* ------------------------------------------------------------------------
   The memory footprint of the RISC-V L3 model: which bytes of memory each
   function on the way from the step function Next reads and writes.

   This is the foundation of the PMP isolation theorems of DESIGN.md.  It
   is stated against riscvTheory alone, for any privilege and any satp,
   except where a lemma says otherwise.
   ------------------------------------------------------------------------ *)
Theory riscv_footprint
Ancestors
  alignment riscv
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

val ERR = mk_HOL_ERR "riscv_footprintTheory"

(* ------------------------------------------------------------------------
   1. Definitions
   ------------------------------------------------------------------------ *)

(* The n bytes a, a + 1, ..., a + (n - 1), modulo 2^64. *)
Definition in_range_def:
  in_range (a : word64) (n : num) (x : word64) <=> w2n (x - a) < n
End

(* s1 and s2 are equal, except possibly for the contents of the memory
   bytes in D. *)
Definition same_except_def:
  same_except (D : word64 -> bool) (s1 : riscv_state) (s2 : riscv_state) <=>
    (s2 = s1 with MEM8 := s2.MEM8) /\ !x. ~D x ==> (s1.MEM8 x = s2.MEM8 x)
End

(* The bytes of the core-local interruptor that the model reads without a
   PMP check (design-privileged.md §6.6.2, [D67]): mtime, mtimecmp of hart
   h and the byte of msip of hart h.  read_mip reads them for mip.MTIP and
   mip.MSIP (P §3.1.9 p.44, §3.2.1 p.59), and so do checkInterrupts and
   the CSR reads of time, mip and sip. *)
Definition clint_byte_def:
  clint_byte (h : word8) x <=>
    in_range (CLINT_BASE + 0xBFF8w) 8 x \/
    in_range (CLINT_BASE + 0x4000w + 8w * w2w h) 8 x \/
    (x = CLINT_BASE + 4w * w2w h)
End

(* The bytes of an explicit data access of n bytes at the virtual address
   va: the access is naturally aligned (the instructions raise the
   misaligned exception before calling dataAddr otherwise, [D55]) and
   dataAddr gives its physical address pa, which needs the PMP's permission
   of the given kind for the effective privilege (P §3.7 p.70,
   dataAddr_pmpCheck below).  These are the bytes that a load (kind
   PMP_Read), a store (PMP_Write) or an AMO (PMP_ReadWrite) may read or
   write. *)
Definition data_bytes_def:
  data_bytes (va, n, kind) s x <=>
    (w2n (va : word64) MOD n = 0) /\
    ?pa. (dataAddr (va, n, kind) s = TR_Address pa) /\ in_range pa n x
End

(* Address translation is off for privilege p (P §12.1.11 p.126): p is M,
   or satp.MODE is not one of Sv39, Sv48, Sv57 (Table 40 p.126).
   legalize_satp keeps the reserved MODEs out of satp, so in a reachable
   state the second disjunct is satp.MODE = Bare (0). *)
Definition satp_bare_def:
  satp_bare s <=>
    ~MEM ((63 >< 60) (s.c_SCSR s.procID).satp : word4) [8w; 9w; 10w]
End

(* ------------------------------------------------------------------------
   2. The functions that do not touch memory

   Every function of riscvTheory that Next can reach is classified from its
   definition: it touches memory iff its definition mentions the MEM8 field
   of the state, or calls a function that touches memory.  The list of
   those that do is asserted below, so that a change to the model that
   adds a memory access makes this theory fail to build.  Every other one
   commutes with replacing the memory, which is proved here for each of
   them by one tactic, in the order of the call graph.  The theorem for a
   function f is f_MEM8:

     state transformer:  f x (s with MEM8 := m) = f x s with MEM8 := m
     value and state:    f x (s with MEM8 := m) =
                           (FST (f x s), SND (f x s) with MEM8 := m)
     value only:         f x (s with MEM8 := m) = f x s

   so f neither reads nor writes memory.
   ------------------------------------------------------------------------ *)

Theorem MEM8_COND_UP[local]:
  !b x y m.
    (if b then x with MEM8 := m else y with MEM8 := m) =
    (if b then x else y) with MEM8 := m
Proof
  rw []
QED

Theorem UNCURRY_FST_SND[local]:
  !f p. UNCURRY f p = f (FST p) (SND p)
Proof
  Cases_on `p` \\ rw []
QED

Theorem word4_cases[local]:
  !i : word4.
    (i = 0w) \/ (i = 1w) \/ (i = 2w) \/ (i = 3w) \/ (i = 4w) \/ (i = 5w) \/
    (i = 6w) \/ (i = 7w) \/ (i = 8w) \/ (i = 9w) \/ (i = 10w) \/ (i = 11w) \/
    (i = 12w) \/ (i = 13w) \/ (i = 14w) \/ (i = 15w)
Proof
  blastLib.BBLAST_TAC
QED

Theorem MEM8_fupd_id:
  !s. s with MEM8 := s.MEM8 = s
Proof
  simp [riscv_state_component_equality]
QED

(* A state transformer that commutes with replacing the memory leaves the
   memory unchanged. *)
Theorem MEM8_comm_frame:
  (!s m. f (s with MEM8 := m) = f s with MEM8 := m) ==> !s. (f s).MEM8 = s.MEM8
Proof
  rpt strip_tac
  \\ first_x_assum (qspecl_then [`s`, `s.MEM8`] mp_tac)
  \\ simp [MEM8_fupd_id]
  \\ disch_then (fn th => once_rewrite_tac [th])
  \\ simp []
QED

Theorem MEM8_comm_pair_frame:
  (!s m. f (s with MEM8 := m) = (FST (f s), SND (f s) with MEM8 := m)) ==>
  !s. (SND (f s)).MEM8 = s.MEM8
Proof
  rpt strip_tac
  \\ first_x_assum (qspecl_then [`s`, `s.MEM8`] mp_tac)
  \\ simp [MEM8_fupd_id]
  \\ disch_then (fn th => once_rewrite_tac [th])
  \\ simp []
QED

local
  val sty = ``:riscv_state``
  fun occurs ty = ty = sty orelse
                  (case Lib.total dest_type ty of
                     SOME (_, args) => List.exists occurs args
                   | NONE => false)
  val defs = DB.definitions "riscv"
  fun lhs_const th = fst (strip_comb (lhs (snd (strip_forall (concl th)))))
  val name = fst o dest_const
  fun def_of c =
    Option.map snd
      (List.find (fn (_, th) =>
                    case Lib.total lhs_const th of
                      SOME t => name t = name c
                    | NONE => false) defs)
  val mem8 = ["recordtype.riscv_state.seldef.MEM8",
              "recordtype.riscv_state.seldef.MEM8_fupd"]
  fun callees th =
    Lib.op_mk_set aconv
      (List.filter (fn t => #Thy (dest_thy_const t) = "riscv")
         (find_terms is_const (rhs (snd (strip_forall (concl th))))))
  fun reach known [] = known
    | reach known (c :: rest) =
        if List.exists (fn d => name d = name c) known then reach known rest
        else case def_of c of
               NONE => reach (c :: known) rest
             | SOME th => reach (c :: known) (rest @ callees th)
  val reachable =
    reach [] [prim_mk_const {Name = "Next", Thy = "riscv"}]
  (* the state functions reachable from Next, at their most general type *)
  val state_fns =
    Lib.op_mk_set (fn a => fn b => name a = name b)
      (List.mapPartial
         (fn c =>
            if String.isPrefix "recordtype." (name c) orelse
               String.isSuffix "_CASE" (name c) orelse
               String.isSuffix "_case" (name c)
            then NONE
            else case def_of c of
                   SOME th => let val g = lhs_const th
                              in if occurs (type_of g) then SOME g else NONE end
                 | NONE => NONE) reachable)
  fun touches c =
    let
      fun go seen [] = false
        | go seen (d :: rest) =
            if Lib.mem (name d) seen then go seen rest
            else if Lib.mem (name d) mem8 then true
            else case def_of d of
                   NONE => go (name d :: seen) rest
                 | SOME th => go (name d :: seen) (rest @ callees th)
    in
      go [] [c]
    end
  val (touching, inert) = List.partition touches state_fns
  val expected_touching =
    [(* memory *)
     "MEM", "write'MEM", "rawReadData", "rawWriteData", "rawReadInst",
     (* the core-local interruptor *)
     "mtime", "mtimecmp", "msip", "read_mip", "checkInterrupts", "CSRMap",
     "CSR", "writeCSR", "accessCSR",
     (* address translation, which reads page-table entries *)
     "ptwLevel", "ptwStep", "translateAddr", "fetchAddr", "dataAddr",
     (* instructions *)
     "dfn'LB", "dfn'LBU", "dfn'LH", "dfn'LHU", "dfn'LW", "dfn'LWU", "dfn'LD",
     "dfn'SB", "dfn'SH", "dfn'SW", "dfn'SD",
     "dfn'LR_W", "dfn'LR_D", "dfn'SC_W", "dfn'SC_D",
     "dfn'AMOSWAP_W", "dfn'AMOSWAP_D", "dfn'AMOADD_W", "dfn'AMOADD_D",
     "dfn'AMOXOR_W", "dfn'AMOXOR_D", "dfn'AMOAND_W", "dfn'AMOAND_D",
     "dfn'AMOOR_W", "dfn'AMOOR_D", "dfn'AMOMIN_W", "dfn'AMOMIN_D",
     "dfn'AMOMAX_W", "dfn'AMOMAX_D", "dfn'AMOMINU_W", "dfn'AMOMINU_D",
     "dfn'AMOMAXU_W", "dfn'AMOMAXU_D",
     "dfn'FLW", "dfn'FSW", "dfn'FLD", "dfn'FSD",
     "dfn'CSRRW", "dfn'CSRRS", "dfn'CSRRC", "dfn'CSRRWI", "dfn'CSRRSI",
     "dfn'CSRRCI", "dfn'WFI",
     (* fetch and the step *)
     "Fetch", "Run", "fetchAndExecute", "Next"]
  val touching_names = map name touching
  val () =
    if Lib.set_eq touching_names expected_touching then ()
    else raise ERR "classification"
           ("the functions that touch memory are not the expected ones: " ^
            "unexpected [" ^
            String.concatWith ", "
              (Lib.set_diff touching_names expected_touching) ^
            "], missing [" ^
            String.concatWith ", "
              (Lib.set_diff expected_touching touching_names) ^ "]")
  (* the order of the call graph *)
  fun deps c =
    case def_of c of
      NONE => []
    | SOME th => List.filter (fn d => name d <> name c andalso
                                      List.exists (fn e => name e = name d) inert)
                             (callees th)
  fun topo done [] = rev done
    | topo done todo =
        let
          val (ready, later) =
            List.partition
              (fn c => List.all (fn d => List.exists (fn e => name e = name d)
                                           done) (deps c)) todo
        in
          if null ready then raise ERR "topo" "cycle" else
          topo (rev ready @ done) later
        end
  val order = topo [] inert
  val m = mk_var ("m", ``:word64 -> word8``)
  val s = mk_var ("s", sty)
  fun with_mem st = ``^st with MEM8 := ^m``
  (* the goal for function c, from the left-hand side of its definition *)
  fun goal c =
    let
      val th = valOf (def_of c)
      val (_, dargs) = strip_comb (lhs (snd (strip_forall (concl th))))
      val (args, rty) = strip_fun (type_of c)
      fun app st =
        case (args, dargs) of
          ([_], _) => mk_comb (c, st)
        | ([_, _], [d]) => mk_comb (mk_comb (c, d), st)
        | _ => raise ERR "goal" (name c)
      val l = app (with_mem s)
      val r0 = app s
      val r =
        if rty = sty then with_mem r0
        else if occurs rty then
          pairSyntax.mk_pair (pairSyntax.mk_fst r0,
                              with_mem (pairSyntax.mk_snd r0))
        else r0
      val g = mk_eq (l, r)
    in
      list_mk_forall (free_vars g, g)
    end
  val lemmas = ref ([] : thm list)
  fun tacA def =
    rpt gen_tac
    \\ simp ([def, MEM8_COND_UP, UNCURRY_FST_SND] @ !lemmas)
    \\ rpt (CASE_TAC \\ simp ([MEM8_COND_UP, UNCURRY_FST_SND] @ !lemmas))
  fun tacB def =
    rw [def] \\ fs (!lemmas) \\ rpt (CASE_TAC \\ fs (!lemmas))
  fun tacC def =
    rpt gen_tac
    \\ (fn g as (_, w) =>
          let
            val i = hd (List.filter (fn v => type_of v = ``:word4``)
                          (free_vars w))
          in
            strip_assume_tac (SPEC i word4_cases) g
          end)
    \\ simp ([def, MEM8_COND_UP, UNCURRY_FST_SND] @ !lemmas)
  fun tac def = FIRST (map (fn t => t def \\ NO_TAC) [tacA, tacB, tacC])
  fun prove_one c =
    let
      val th = Q.prove (`^(goal c)`, tac (valOf (def_of c)))
    in
      lemmas := th :: !lemmas;
      save_thm (name c ^ "_MEM8", th)
    end
in
  val inert_names = map name order
  val inert_MEM8 = map prove_one order
  val touching_names = touching_names
end

val () =
  print ("riscv_footprint: " ^ Int.toString (length inert_names) ^
         " state functions reachable from Next commute with memory; " ^
         Int.toString (length touching_names) ^ " touch it\n")

(* Every state transformer among them leaves procID unchanged. *)
local
  val sty = ``:riscv_state``
  fun occurs ty = ty = sty orelse
                  (case Lib.total dest_type ty of
                     SOME (_, args) => List.exists occurs args
                   | NONE => false)
  fun lhs_of th = lhs (snd (strip_forall (concl th)))
  fun def_named nm =
    snd (valOf (List.find (fn (_, th) =>
                  (fst (dest_const (fst (strip_comb (lhs_of th)))) = nm)
                  handle HOL_ERR _ => false) (DB.definitions "riscv")))
  val procID_COND = Q.prove (
    `!b x y. (if b then x else y).procID = if b then x.procID else y.procID`,
    rw [])
  val lemmas = ref ([] : thm list)
  fun goal mth =
    let
      val st = mk_var ("s", sty)
      val (f, args) = strip_comb (lhs_of mth)
      val l = list_mk_comb (f, butlast args @ [st])
      val p = if type_of l = sty then l else pairSyntax.mk_snd l
      val g = ``^p.procID = ^st.procID``
    in
      list_mk_forall (free_vars g, g)
    end
  fun tacA def =
    rpt gen_tac
    \\ simp ([def, procID_COND, UNCURRY_FST_SND] @ !lemmas)
    \\ rpt (CASE_TAC \\ simp ([procID_COND, UNCURRY_FST_SND] @ !lemmas))
  fun tacC def =
    rpt gen_tac
    \\ (fn g as (_, w) =>
          let
            val i = hd (List.filter (fn v => type_of v = ``:word4``)
                          (free_vars w))
          in
            strip_assume_tac (SPEC i word4_cases) g
          end)
    \\ simp ([def, procID_COND, UNCURRY_FST_SND] @ !lemmas)
  fun prove_one (nm, mth) =
    let
      val def = def_named nm
      val th = Q.prove (`^(goal mth)`,
                        FIRST (map (fn t => t def \\ NO_TAC) [tacA, tacC]))
    in
      lemmas := th :: !lemmas;
      save_thm (nm ^ "_procID", th)
    end
in
  val inert_procID =
    map prove_one
      (List.filter (fn (_, th) => occurs (type_of (lhs_of th)))
         (ListPair.zip (inert_names, inert_MEM8)))
end
