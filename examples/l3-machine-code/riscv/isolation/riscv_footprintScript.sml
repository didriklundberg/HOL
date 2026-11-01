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

Theorem MEM8_of_upd:
  !s m. (s with MEM8 := m).MEM8 = m
Proof
  simp []
QED

Theorem MEM8_upd_eq:
  !s f g. (s with MEM8 := f = s with MEM8 := g) <=> (f = g)
Proof
  rw [riscv_state_component_equality]
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

(* ------------------------------------------------------------------------
   3. Memory primitives

   MEM8 maps a byte address to a byte.  MEM and write'MEM read and write an
   aligned doubleword of it (the L3 component MEM), and every other access
   goes through them: rawReadData reads the 8 bytes from an address,
   rawWriteData writes the low n of them, and rawReadInst reads an
   instruction parcel.  The theorems below describe each byte by byte, for
   every alignment, so that no later lemma needs an alignment hypothesis
   for the physical address.
   ------------------------------------------------------------------------ *)

(* An address is a doubleword index and an offset in the doubleword. *)
Theorem addr_split[local]:
  !a : word64.
    a = ((w2w ((63 >< 3) a : 61 word) : word64) << 3) + w2w ((2 >< 0) a : word3)
Proof
  blastLib.BBLAST_TAC
QED

Theorem addr_parts[local]:
  !(i : 61 word) (j : word3).
    ((63 >< 3) (((w2w i : word64) << 3) + w2w j) = i) /\
    ((2 >< 0) (((w2w i : word64) << 3) + w2w j) = j)
Proof
  blastLib.BBLAST_TAC
QED

Theorem next_dword[local]:
  !i : 61 word. ((w2w (i + 1w) : word64) << 3) = ((w2w i : word64) << 3) + 8w
Proof
  blastLib.BBLAST_TAC
QED

Theorem dword_succ_ne[local]:
  !i : 61 word. i + 1w <> i
Proof
  blastLib.BBLAST_TAC
QED

Theorem w2w_offset[local]:
  !k. k < 8 ==>
      (w2w (n2w k : word3) : word64 = n2w k) /\ (w2n (n2w k : word3) = k)
Proof
  rw [wordsTheory.w2w_def, wordsTheory.w2n_n2w]
QED

local
  fun is_mem8 t =
    case strip_comb t of
      (c, [_, _]) => is_const c andalso
                     fst (dest_const c) = "recordtype.riscv_state.seldef.MEM8"
    | _ => false
in
  (* replace every byte s.MEM8 a of the goal by a variable *)
  fun gen_mem8_tac (g as (_, w)) =
    let
      val ts = Lib.op_mk_set aconv (find_terms is_mem8 w)
    in
      MAP_EVERY (fn t => SPEC_TAC (t, genvar (type_of t))) ts g
    end
end

val num_ss =
  std_ss ++ numSimps.REDUCE_ss ++ wordsLib.SIZES_ss ++
  rewrites [wordsTheory.word_len_def]

(* write'MEM sets the 8 bytes of doubleword i, byte k of the doubleword to
   byte k of v (little-endian). *)
Theorem write'MEM_bytes:
  !v i s x.
    (write'MEM (v, i) s).MEM8 x =
    if (63 >< 3) x = i then (7 >< 0) (v >>> (8 * w2n ((2 >< 0) x : word3)))
    else s.MEM8 x
Proof
  rw [write'MEM_def, combinTheory.APPLY_UPDATE_THM]
  \\ wordsLib.Cases_on_word_value `(2 >< 0) x : word3`
  \\ rpt (qpat_x_assum `_` mp_tac)
  \\ blastLib.BBLAST_TAC
QED

Theorem write'MEM_only_MEM8:
  !v i s. write'MEM (v, i) s = s with MEM8 := (write'MEM (v, i) s).MEM8
Proof
  rw [write'MEM_def, riscv_state_component_equality]
QED

(* rawReadData reads the 8 bytes from its address, at every alignment. *)
val rawReadData_dword = Q.prove (
    `!i j s.
       j < 8 ==>
       (rawReadData (((w2w (i : 61 word) : word64) << 3) + w2w (n2w j : word3)) s =
        let a = ((w2w i : word64) << 3) + w2w (n2w j : word3) in
          s.MEM8 (a + 7w) @@ s.MEM8 (a + 6w) @@ s.MEM8 (a + 5w) @@
          s.MEM8 (a + 4w) @@ s.MEM8 (a + 3w) @@ s.MEM8 (a + 2w) @@
          s.MEM8 (a + 1w) @@ s.MEM8 a)`,
    rpt strip_tac
    \\ `(j = 0) \/ (j = 1) \/ (j = 2) \/ (j = 3) \/ (j = 4) \/ (j = 5) \/
        (j = 6) \/ (j = 7)` by decide_tac
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ simp_tac num_ss [rawReadData_def, MEM_def, LET_THM, addr_parts,
                        next_dword, w2w_offset]
    \\ simp_tac num_ss [GSYM wordsTheory.WORD_ADD_ASSOC,
                        wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_0]
    \\ gen_mem8_tac
    \\ blastLib.BBLAST_TAC)

Theorem rawReadData_bytes:
  !a s.
    rawReadData a s =
    s.MEM8 (a + 7w) @@ s.MEM8 (a + 6w) @@ s.MEM8 (a + 5w) @@
    s.MEM8 (a + 4w) @@ s.MEM8 (a + 3w) @@ s.MEM8 (a + 2w) @@
    s.MEM8 (a + 1w) @@ s.MEM8 a
Proof
  rpt gen_tac
  \\ qspecl_then [`(63 >< 3) a`, `w2n ((2 >< 0) a : word3)`, `s`] mp_tac
                 rawReadData_dword
  \\ simp_tac std_ss [wordsTheory.n2w_w2n, LET_THM, GSYM addr_split]
  \\ disch_then irule
  \\ assume_tac (INST_TYPE [alpha |-> ``:3``] wordsTheory.w2n_lt)
  \\ fs [wordsTheory.dimword_def]
QED

(* rawWriteData writes the low n bytes of its data to the n bytes from its
   address, little-endian, and leaves every other byte as it was: also the
   other bytes of the doubleword(s) it rewrites.  n is the width of every
   store, 1, 2, 4 or 8. *)
fun is_w2n_sub t =
    case Lib.total wordsSyntax.dest_w2n t of
      SOME u =>
        (case Lib.total wordsSyntax.dest_word_sub u of
           SOME (x, y) =>
             wordsSyntax.is_n2w x andalso wordsSyntax.is_n2w y andalso
             numSyntax.is_numeral (rand x) andalso numSyntax.is_numeral (rand y)
         | NONE => false)
    | NONE => false
fun w2n_sub_conv t = if is_w2n_sub t then EVAL t else NO_CONV t
val wd_dword_step = Q.prove (
    `!a : word64 k.
       k < 8 ==>
       ((63 >< 3) (a + n2w k) : 61 word = (63 >< 3) a) \/
       ((63 >< 3) (a + n2w k) : 61 word = (63 >< 3) a + 1w)`,
    rpt strip_tac
    \\ `(k = 0) \/ (k = 1) \/ (k = 2) \/ (k = 3) \/ (k = 4) \/ (k = 5) \/
        (k = 6) \/ (k = 7)` by decide_tac
    \\ rw []
    \\ blastLib.BBLAST_TAC)
val wd_in_range_dword = Q.prove (
    `!a n x.
       in_range a n x /\ n <= 8 ==>
       ((63 >< 3) x : 61 word = (63 >< 3) a) \/
       ((63 >< 3) x : 61 word = (63 >< 3) a + 1w)`,
    REWRITE_TAC [in_range_def]
    \\ rpt strip_tac
    \\ `x = a + n2w (w2n (x - a))`
       by simp_tac std_ss [wordsTheory.n2w_w2n, wordsTheory.WORD_SUB_ADD2]
    \\ pop_assum SUBST1_TAC
    \\ irule wd_dword_step
    \\ decide_tac)
val wd_far = Q.prove (
    `!i ix j jx n.
       j < 8 /\ ix <> i /\ ix <> i + 1w /\ n <= 8 ==>
       ~in_range (((w2w (i : 61 word) : word64) << 3) + n2w j) n
                 (((w2w ix : word64) << 3) + w2w (jx : word3))`,
    rpt strip_tac
    \\ drule_all wd_in_range_dword
    \\ `n2w j : word64 = w2w (n2w j : word3)` by simp [w2w_offset]
    \\ pop_assum SUBST1_TAC
    \\ simp [addr_parts])
fun wd_goal j n =
    let
      val jt = numSyntax.term_of_int j
      val nt = numSyntax.term_of_int n
    in
      ``!i (ix : 61 word) k s d.
          k < 8 ==>
          ((rawWriteData (((w2w (i : 61 word) : word64) << 3) +
                          w2w (n2w ^jt : word3), d, ^nt) s).MEM8
             (((w2w ix : word64) << 3) + w2w (n2w k : word3)) =
           if in_range (((w2w i : word64) << 3) + w2w (n2w ^jt : word3)) ^nt
                       (((w2w ix : word64) << 3) + w2w (n2w k : word3))
           then
             (7 >< 0)
               (d >>> (8 * w2n ((((w2w ix : word64) << 3) +
                                 w2w (n2w k : word3)) -
                                (((w2w i : word64) << 3) +
                                 w2w (n2w ^jt : word3)))))
           else s.MEM8 (((w2w ix : word64) << 3) + w2w (n2w k : word3)))``
    end
fun wd_k_cases_tac g =
    (qpat_x_assum `k < 8`
       (fn th => `(k = 0) \/ (k = 1) \/ (k = 2) \/ (k = 3) \/ (k = 4) \/
                  (k = 5) \/ (k = 6) \/ (k = 7)` by (assume_tac th \\ decide_tac))
     \\ pop_assum (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC)) g
val wd_dword_ss =
    [MEM_def, w2w_offset, LET_THM, addr_parts, next_dword, dword_succ_ne,
     GSYM wordsTheory.WORD_ADD_ASSOC, wordsTheory.word_add_n2w,
     wordsTheory.WORD_ADD_0, wordsTheory.WORD_SUB_PLUS,
     wordsTheory.WORD_ADD_SUB2, in_range_def]
val wd_tac =
    rpt gen_tac
    \\ strip_tac
    \\ simp_tac num_ss [rawWriteData_def, LET_THM, addr_parts, w2w_offset,
                        write'MEM_bytes]
    \\ Cases_on `ix = i`
    >- (pop_assum SUBST_ALL_TAC
        \\ wd_k_cases_tac
        \\ simp_tac num_ss wd_dword_ss
        \\ CONV_TAC (DEPTH_CONV w2n_sub_conv)
        \\ simp_tac num_ss []
        \\ gen_mem8_tac
        \\ blastLib.BBLAST_TAC)
    \\ Cases_on `ix = i + 1w`
    >- (pop_assum SUBST_ALL_TAC
        \\ wd_k_cases_tac
        \\ simp_tac num_ss wd_dword_ss
        \\ CONV_TAC (DEPTH_CONV w2n_sub_conv)
        \\ simp_tac num_ss []
        \\ gen_mem8_tac
        \\ blastLib.BBLAST_TAC)
    \\ asm_simp_tac num_ss [wd_far]
val rawWriteData_cases =
    List.concat
      (List.map (fn n => List.map (fn j => Q.prove (`^(wd_goal j n)`, wd_tac))
                           [0, 1, 2, 3, 4, 5, 6, 7]) [1, 2, 4, 8])
val rawWriteData_dword = Q.prove (
    `!i j (ix : 61 word) jx d n s.
       ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) ==>
       ((rawWriteData (((w2w (i : 61 word) : word64) << 3) + w2w (j : word3),
                       d, n) s).MEM8
          (((w2w ix : word64) << 3) + w2w (jx : word3)) =
        if in_range (((w2w i : word64) << 3) + w2w j) n
                    (((w2w ix : word64) << 3) + w2w jx)
        then
          (7 >< 0)
            (d >>> (8 * w2n ((((w2w ix : word64) << 3) + w2w jx) -
                             (((w2w i : word64) << 3) + w2w j))))
        else s.MEM8 (((w2w ix : word64) << 3) + w2w jx))`,
    rpt gen_tac
    \\ strip_tac
    \\ `jx = n2w (w2n jx)` by simp []
    \\ pop_assum SUBST1_TAC
    \\ `w2n jx < 8`
       by (assume_tac (INST_TYPE [alpha |-> ``:3``] wordsTheory.w2n_lt)
           \\ fs [wordsTheory.dimword_def])
    \\ qabbrev_tac `k = w2n jx`
    \\ wordsLib.Cases_on_word_value `j`
    \\ rpt BasicProvers.VAR_EQ_TAC
    \\ asm_simp_tac std_ss rawWriteData_cases)

Theorem rawWriteData_bytes:
  !a d n s x.
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) ==>
    ((rawWriteData (a, d, n) s).MEM8 x =
     if in_range a n x then (7 >< 0) (d >>> (8 * w2n (x - a)))
     else s.MEM8 x)
Proof
  rpt strip_tac
  \\ qspecl_then [`(63 >< 3) a : 61 word`, `(2 >< 0) a : word3`,
                  `(63 >< 3) x : 61 word`, `(2 >< 0) x : word3`,
                  `d`, `n`, `s`] mp_tac rawWriteData_dword
  \\ asm_simp_tac std_ss [GSYM addr_split]
QED

Theorem rawWriteData_only_MEM8:
  !a d n s. rawWriteData (a, d, n) s = s with MEM8 := (rawWriteData (a, d, n) s).MEM8
Proof
  rw [rawWriteData_def, write'MEM_def, LET_THM, riscv_state_component_equality]
QED

Theorem rawWriteData_eq:
  !a d n s.
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) ==>
    (rawWriteData (a, d, n) s =
     s with MEM8 :=
       (\x. if in_range a n x then (7 >< 0) (d >>> (8 * w2n (x - a)))
            else s.MEM8 x))
Proof
  rpt strip_tac
  \\ once_rewrite_tac [rawWriteData_only_MEM8]
  \\ simp_tac std_ss [MEM8_upd_eq, FUN_EQ_THM]
  \\ asm_simp_tac std_ss [rawWriteData_bytes]
QED

(* So rawWriteData changes at most the n bytes from its address, and when
   the memory is replaced, the result is the same outside those bytes as
   the replacement. *)
Theorem rawWriteData_frame:
  !a d n s x.
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\ ~in_range a n x ==>
    ((rawWriteData (a, d, n) s).MEM8 x = s.MEM8 x)
Proof
  rpt strip_tac \\ simp [rawWriteData_bytes]
QED

Theorem rawWriteData_MEM8:
  !a d n s m.
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) ==>
    (rawWriteData (a, d, n) (s with MEM8 := m) =
     rawWriteData (a, d, n) s with
     MEM8 := (\x. if in_range a n x then (rawWriteData (a, d, n) s).MEM8 x
                  else m x))
Proof
  rpt strip_tac
  \\ simp [rawWriteData_eq, riscv_state_component_equality, FUN_EQ_THM]
  \\ rw []
QED

(* The parts of rawReadData that loads use depend only on the bytes they
   load. *)
Theorem in_range_add:
  !a n k. k < n /\ n <= 18446744073709551616 ==> in_range a n (a + n2w k)
Proof
  rw [in_range_def]
  \\ `k < 18446744073709551616` by decide_tac
  \\ simp []
QED

(* replace every byte, of the state or of a replacement memory, by a
   variable *)
local
  fun is_byte t =
    type_of t = ``:word8`` andalso is_comb t andalso
    (is_var (rator t) orelse
     (case strip_comb t of
        (c, [_, _]) => is_const c andalso
                       fst (dest_const c) = "recordtype.riscv_state.seldef.MEM8"
      | _ => false))
in
  fun gen_bytes_tac (g as (_, w)) =
    let
      val ts = Lib.op_mk_set aconv (find_terms is_byte w)
    in
      MAP_EVERY (fn t => SPEC_TAC (t, genvar (type_of t))) ts g
    end
end

fun bytes_tac n =
    rpt strip_tac
    \\ simp_tac std_ss [rawReadData_bytes, MEM8_of_upd]
    \\ MAP_EVERY
         (fn k =>
            let
              val a = if k = 0 then ``pa : word64``
                      else ``pa + n2w ^(numSyntax.term_of_int k) : word64``
            in
              sg `m ^a = s.MEM8 ^a`
              >- (first_x_assum irule
                  \\ simp [in_range_def, wordsTheory.WORD_ADD_SUB2])
              \\ pop_assum SUBST1_TAC
            end) (List.tabulate (n, I))
    \\ asm_simp_tac std_ss []
    \\ gen_bytes_tac
    \\ blastLib.BBLAST_TAC

Theorem rawReadData_agree_1:
  !pa m s.
    (!x. in_range pa 1 x ==> (m x = s.MEM8 x)) ==>
    ((7 >< 0) (rawReadData pa (s with MEM8 := m)) : word8 =
     (7 >< 0) (rawReadData pa s))
Proof
  bytes_tac 1
QED

Theorem rawReadData_agree_2:
  !pa m s.
    (!x. in_range pa 2 x ==> (m x = s.MEM8 x)) ==>
    ((15 >< 0) (rawReadData pa (s with MEM8 := m)) : word16 =
     (15 >< 0) (rawReadData pa s))
Proof
  bytes_tac 2
QED

Theorem rawReadData_agree_4:
  !pa m s.
    (!x. in_range pa 4 x ==> (m x = s.MEM8 x)) ==>
    ((31 >< 0) (rawReadData pa (s with MEM8 := m)) : word32 =
     (31 >< 0) (rawReadData pa s))
Proof
  bytes_tac 4
QED

Theorem rawReadData_agree_8:
  !pa m s.
    (!x. in_range pa 8 x ==> (m x = s.MEM8 x)) ==>
    (rawReadData pa (s with MEM8 := m) = rawReadData pa s)
Proof
  bytes_tac 8
QED

(* rawReadInst reads the low 2 bits of the byte at its address, and then 2
   or 4 bytes, and sets Skip to the length of the instruction. *)
Theorem rawReadInst_eq:
  !a s.
    rawReadInst a s =
    if word_bit 0 (s.MEM8 a) /\ word_bit 1 (s.MEM8 a) then
      (Word (s.MEM8 (a + 3w) @@ s.MEM8 (a + 2w) @@ s.MEM8 (a + 1w) @@ s.MEM8 a),
       write'Skip 4w s)
    else (Half (s.MEM8 (a + 1w) @@ s.MEM8 a), write'Skip 2w s)
Proof
  rw [rawReadInst_def, boolify8_def, write'Skip_def]
  \\ fs [boolify8_def]
QED

(* The state transformers that do not touch memory leave it unchanged:
   f_MEM8_frame, from f_MEM8 by MEM8_comm_frame. *)
local
  val sty = ``:riscv_state``
  fun lhs_of th = lhs (snd (strip_forall (concl th)))
  fun frame (nm, th) =
    let
      val l = lhs_of th
      val (f, args) = strip_comb l
      val sm = List.last args        (* s with MEM8 := m, that is *)
      val st = rand sm               (* MEM8_fupd (K m) s *)
      val m = rand (rand (rator sm))
      val comm = GEN st (GEN m (SPEC_ALL th))
      val th' =
        if type_of l = sty then MATCH_MP MEM8_comm_frame comm
        else MATCH_MP MEM8_comm_pair_frame comm
    in
      SOME (save_thm (nm ^ "_MEM8_frame", GEN_ALL th'))
    end
in
  val inert_frames =
    List.mapPartial frame
      (List.filter (fn (_, th) =>
                      let val ty = type_of (lhs_of th)
                      in ty = sty orelse
                         (case Lib.total pairSyntax.dest_prod ty of
                            SOME (_, b) => b = sty
                          | NONE => false)
                      end)
         (ListPair.zip (inert_names, inert_MEM8)))
end

(* ML names for the generated lemmas that the proofs below use *)
fun gen_thm nm = DB.fetch "-" nm
val effectivePrivilege_MEM8 = gen_thm "effectivePrivilege_MEM8"
val curPrivilege_MEM8 = gen_thm "curPrivilege_MEM8"
val pmpCheck_MEM8 = gen_thm "pmpCheck_MEM8"
val MCSR_MEM8 = gen_thm "MCSR_MEM8"
val GPR_MEM8 = gen_thm "GPR_MEM8"
val PC_MEM8 = gen_thm "PC_MEM8"
val haveRVC_MEM8 = gen_thm "haveRVC_MEM8"
val read_xepc_MEM8 = gen_thm "read_xepc_MEM8"
val raise'exception_MEM8 = gen_thm "raise'exception_MEM8"
val raise'exception_procID = gen_thm "raise'exception_procID"
val write'CSR_MEM8 = gen_thm "write'CSR_MEM8"
val write'CSR_procID = gen_thm "write'CSR_procID"
val write'CSR_MEM8_frame = gen_thm "write'CSR_MEM8_frame"
val Delta_MEM8 = gen_thm "Delta_MEM8"
val write'Delta_MEM8 = gen_thm "write'Delta_MEM8"
val write'Delta_procID = gen_thm "write'Delta_procID"
val write'Delta_MEM8_frame = gen_thm "write'Delta_MEM8_frame"
val checkCSROp_MEM8 = gen_thm "checkCSROp_MEM8"
val signalException_MEM8 = gen_thm "signalException_MEM8"
val write'GPR_MEM8 = gen_thm "write'GPR_MEM8"

(* ------------------------------------------------------------------------
   4. Alignment, address translation and the PMP check of an access
   ------------------------------------------------------------------------ *)

(* The alignment tests of the load and store instructions are natural
   alignment (U §2.6, P §3.6.4). *)
Theorem align_tests:
  !v : word64.
    (w2n v MOD 1 = 0) /\
    ((w2n v MOD 2 = 0) <=> ~word_bit 0 v) /\
    ((w2n v MOD 4 = 0) <=> ((1 >< 0) v = 0w : word2)) /\
    ((w2n v MOD 8 = 0) <=> ((2 >< 0) v = 0w : word3))
Proof
  gen_tac
  \\ `!k. (w2n v MOD 2 ** k = 0) <=> (v && n2w (2 ** k - 1) = 0w)`
     by (gen_tac \\ simp [GSYM aligned_w2n, aligned_bitwise_and])
  \\ rpt conj_tac
  >- simp []
  \\ first_x_assum
       (fn th => map_every (fn k => assume_tac
                              (SIMP_RULE (srw_ss()) [] (Q.SPEC k th)))
                           [`1`, `2`, `3`])
  \\ fs []
  \\ blastLib.BBLAST_TAC
QED

(* translateAddr is the identity when translation is off (P §12.1.11
   p.126; design-smode.md §1.2 [S1]): for privilege M, which it tests
   first, and when satp.MODE is not Sv39, Sv48 or Sv57 (Bare). *)
Theorem translateAddr_off:
  !va ft ac p s.
    (p = Machine) \/ satp_bare s ==>
    (translateAddr (va, ft, ac, p) s = TR_Address va)
Proof
  rpt gen_tac
  \\ strip_tac
  >- simp [translateAddr_def]
  \\ fs [satp_bare_def]
  \\ simp [translateAddr_def, SCSR_def]
QED

(* So an explicit data access (P §3.7 p.70, §3.1.6.4 p.35, [D22]) and a
   fetch parcel (P §3.7.1 p.72) are checked by the PMP at their virtual
   address, with the effective and the current privilege. *)
Theorem dataAddr_off:
  !va n kind s.
    (effectivePrivilege () s = Machine) \/ satp_bare s ==>
    (dataAddr (va, n, kind) s =
     if pmpCheck (va, n, kind, effectivePrivilege () s) s then TR_Address va
     else TR_Fault (accessFault (Data, if kind = PMP_Read then Read else Write)))
Proof
  rpt gen_tac \\ strip_tac \\ simp [dataAddr_def, translateAddr_off]
QED

Theorem fetchAddr_off:
  !va s.
    (curPrivilege () s = Machine) \/ satp_bare s ==>
    (fetchAddr va s =
     if pmpCheck (va, 2, PMP_Execute, curPrivilege () s) s then TR_Address va
     else TR_Fault Fetch_Fault)
Proof
  rpt gen_tac \\ strip_tac \\ simp [fetchAddr_def, translateAddr_off]
QED

(* Whatever the translation, the physical address that dataAddr and
   fetchAddr give has passed the PMP check (design-privileged.md §5.4,
   §5.6.3; design-smode.md §3.11). *)
Theorem dataAddr_pmpCheck:
  !va n kind s pa.
    (dataAddr (va, n, kind) s = TR_Address pa) ==>
    pmpCheck (pa, n, kind, effectivePrivilege () s) s
Proof
  rpt gen_tac
  \\ strip_tac
  \\ fs [dataAddr_def, LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs []
  \\ rw []
  \\ fs []
QED

Theorem fetchAddr_pmpCheck:
  !va s pa.
    (fetchAddr va s = TR_Address pa) ==>
    pmpCheck (pa, 2, PMP_Execute, curPrivilege () s) s
Proof
  rpt gen_tac
  \\ strip_tac
  \\ fs [fetchAddr_def, LET_THM]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ fs []
  \\ rw []
  \\ fs []
QED

(* With translation off they read no memory. *)
Theorem satp_bare_MEM8:
  !s m. satp_bare (s with MEM8 := m) <=> satp_bare s
Proof
  simp [satp_bare_def]
QED

Theorem dataAddr_off_MEM8:
  !va n kind s m.
    (effectivePrivilege () s = Machine) \/ satp_bare s ==>
    (dataAddr (va, n, kind) (s with MEM8 := m) = dataAddr (va, n, kind) s)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp [dataAddr_def, effectivePrivilege_MEM8, pmpCheck_MEM8,
           satp_bare_MEM8, translateAddr_off]
QED

Theorem fetchAddr_off_MEM8:
  !va s m.
    (curPrivilege () s = Machine) \/ satp_bare s ==>
    (fetchAddr va (s with MEM8 := m) = fetchAddr va s)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp [fetchAddr_def, curPrivilege_MEM8, pmpCheck_MEM8, satp_bare_MEM8,
           translateAddr_off]
QED

(* ------------------------------------------------------------------------
   5. The core-local interruptor

   mtime, mtimecmp and msip are memory words in this model ([D67]).  Their
   readers depend on memory only at the bytes clint_byte names.
   ------------------------------------------------------------------------ *)

(* The replacement memory m agrees with the memory of s on the CLINT bytes
   of the hart s.procID. *)
Definition clint_agree_def:
  clint_agree s m <=> !x. clint_byte s.procID x ==> (m x = s.MEM8 x)
End

val side_ss =
  [in_range_def, wordsTheory.WORD_SUB_REFL, wordsTheory.WORD_ADD_SUB2,
   wordsTheory.w2n_n2w, wordsTheory.word_0_n2w]

(* prove m t = s.MEM8 t for every byte m t of the goal, from an assumption
   !x. P x ==> (m x = s.MEM8 x) and the tactic side for P t *)
fun agree_tac side (g as (_, w)) =
  let
    val ts = Lib.op_mk_set aconv
               (find_terms (fn t => is_comb t andalso is_var (rator t) andalso
                                    fst (dest_var (rator t)) = "m" andalso
                                    type_of t = ``:word8``) w)
    fun one t =
      let
        val st = mk_var ("s", ``:riscv_state``)
        val e = mk_eq (t, ``^st.MEM8 ^(rand t)``)
      in
        sg `^e` >- (first_assum irule \\ side) \\ pop_assum SUBST1_TAC
      end
  in
    MAP_EVERY one ts g
  end

Theorem MEM_agree:
  !i m s.
    (!x. in_range ((w2w (i : 61 word) : word64) << 3) 8 x ==> (m x = s.MEM8 x)) ==>
    (MEM i (s with MEM8 := m) = MEM i s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [MEM_def, LET_THM, MEM8_of_upd]
  \\ agree_tac (simp_tac num_ss side_ss)
  \\ simp_tac std_ss []
QED

Theorem mtime_addr[local]:
  (w2w ((63 >< 3) (CLINT_BASE + 49144w : word64) : 61 word) : word64) << 3 =
  CLINT_BASE + 0xBFF8w
Proof
  simp_tac std_ss [CLINT_BASE_def] \\ EVAL_TAC
QED

Theorem mtimecmp_addr[local]:
  !h : word8.
    (w2w ((63 >< 3) (CLINT_BASE + 16384w + 8w * w2w h : word64) : 61 word)
       : word64) << 3 =
    CLINT_BASE + 0x4000w + 8w * w2w h
Proof
  simp [CLINT_BASE_def] \\ blastLib.BBLAST_TAC
QED

Theorem mtime_CLINT:
  !s m. clint_agree s m ==> (mtime () (s with MEM8 := m) = mtime () s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [mtime_def]
  \\ irule MEM_agree
  \\ simp_tac std_ss [mtime_addr]
  \\ rpt strip_tac
  \\ fs [clint_agree_def, clint_byte_def, CLINT_BASE_def]
QED

Theorem mtimecmp_CLINT:
  !s m.
    clint_agree s m ==>
    (mtimecmp s.procID (s with MEM8 := m) = mtimecmp s.procID s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [mtimecmp_def]
  \\ irule MEM_agree
  \\ simp_tac std_ss [mtimecmp_addr]
  \\ rpt strip_tac
  \\ fs [clint_agree_def, clint_byte_def]
QED

Theorem msip_CLINT:
  !s m.
    clint_agree s m ==> (msip s.procID (s with MEM8 := m) = msip s.procID s)
Proof
  rw [msip_def, clint_agree_def, clint_byte_def] \\ metis_tac []
QED

Theorem read_mip_CLINT:
  !s m. clint_agree s m ==> (read_mip () (s with MEM8 := m) = read_mip () s)
Proof
  rpt strip_tac
  \\ asm_simp_tac (srw_ss())
       [read_mip_def, MCSR_MEM8, mtimecmp_CLINT, mtime_CLINT, msip_CLINT]
QED

(* So whether an interrupt is taken depends on memory only through the
   CLINT bytes (P §3.1.9 p.44-45, §3.2.1 p.59). *)
Theorem checkInterrupts_CLINT:
  !s m.
    clint_agree s m ==>
    (checkInterrupts () (s with MEM8 := m) = checkInterrupts () s)
Proof
  rpt strip_tac
  \\ asm_simp_tac (srw_ss())
       [checkInterrupts_def, read_mip_CLINT, MCSR_MEM8, curPrivilege_MEM8]
QED

(* The CSR reads: time is mtime (0xC01), mip (0x344) and sip (0x144)
   include read_mip. *)
Theorem CSRMap_CLINT:
  !s m csr.
    clint_agree s m ==>
    (CSRMap csr (s with MEM8 := m) =
     (FST (CSRMap csr s), SND (CSRMap csr s) with MEM8 := m))
Proof
  rpt strip_tac
  \\ asm_simp_tac (srw_ss())
       [CSRMap_def, read_mip_CLINT, mtime_CLINT, MCSR_MEM8, read_xepc_MEM8,
        raise'exception_MEM8]
  \\ rpt (CASE_TAC
          \\ asm_simp_tac (srw_ss())
               [read_mip_CLINT, mtime_CLINT, MCSR_MEM8, read_xepc_MEM8,
                raise'exception_MEM8])
QED

Theorem clint_agree_self:
  !s. clint_agree s s.MEM8
Proof
  simp [clint_agree_def]
QED

Theorem CSRMap_frame:
  !s csr.
    ((SND (CSRMap csr s)).MEM8 = s.MEM8) /\
    ((SND (CSRMap csr s)).procID = s.procID)
Proof
  rpt gen_tac
  \\ conj_tac
  >- (qspecl_then [`s`, `s.MEM8`, `csr`] mp_tac CSRMap_CLINT
      \\ simp [clint_agree_self, MEM8_fupd_id]
      \\ disch_then (fn th => once_rewrite_tac [th])
      \\ simp [])
  \\ simp [CSRMap_def]
  \\ rpt (CASE_TAC \\ simp [raise'exception_procID])
QED

Theorem clint_agree_frame:
  !s t m.
    (t.procID = s.procID) /\ (t.MEM8 = s.MEM8) ==>
    (clint_agree t m <=> clint_agree s m)
Proof
  simp [clint_agree_def]
QED

Theorem writeCSR_CLINT:
  !s m csr v.
    clint_agree s m ==>
    (writeCSR (csr, v) (s with MEM8 := m) = writeCSR (csr, v) s with MEM8 := m)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [writeCSR_def, LET_THM, UNCURRY_FST_SND, write'CSR_MEM8,
                      Delta_MEM8, write'Delta_MEM8]
  \\ qmatch_goalsub_abbrev_tac `CSR csr (t with MEM8 := m)`
  \\ `clint_agree t m`
     by (qunabbrev_tac `t`
         \\ irule (iffRL clint_agree_frame)
         \\ qexists_tac `s`
         \\ simp [write'Delta_procID, write'CSR_procID, write'Delta_MEM8_frame,
                  write'CSR_MEM8_frame])
  \\ simp [CSR_def, CSRMap_CLINT, write'Delta_MEM8]
QED

Theorem accessCSR_CLINT:
  !s m op rd f src csr.
    clint_agree s m ==>
    (accessCSR (op, rd, f, src, csr) (s with MEM8 := m) =
     accessCSR (op, rd, f, src, csr) s with MEM8 := m)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [accessCSR_def, LET_THM, UNCURRY_FST_SND, checkCSROp_MEM8]
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [signalException_MEM8, CSR_def, CSRMap_CLINT]
  \\ `clint_agree (SND (CSRMap csr s)) m`
     by (irule (iffRL clint_agree_frame) \\ qexists_tac `s` \\ simp [CSRMap_frame])
  \\ IF_CASES_TAC
  \\ asm_simp_tac std_ss [writeCSR_CLINT, MCSR_MEM8, write'GPR_MEM8]
QED

Theorem dfn'WFI_CLINT:
  !s m. clint_agree s m ==> (dfn'WFI (s with MEM8 := m) = dfn'WFI s with MEM8 := m)
Proof
  rpt strip_tac
  \\ asm_simp_tac std_ss [dfn'WFI_def, curPrivilege_MEM8, MCSR_MEM8, read_mip_CLINT,
                          signalException_MEM8]
  \\ rpt (CASE_TAC \\ asm_simp_tac std_ss [signalException_MEM8, MEM8_COND_UP])
QED
