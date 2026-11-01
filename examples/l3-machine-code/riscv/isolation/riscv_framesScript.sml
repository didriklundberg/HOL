(* ------------------------------------------------------------------------
   Field frames of the RISC-V L3 model: for every function on the way from
   the step function Next, the fields of the state that it never updates.

   Like section 2 of riscv_footprintScript.sml, the build computes from the
   definitions in riscvTheory which fields each function updates, directly
   or through a callee, and proves for every state function f the frame

     f_frame:  !args s. ((f args s).F = s.F) /\ ...

   (with SND (f args s) for a function that also returns a value) for each
   field F of frame_fields that f does not update.  The frames of Next,
   fetchAndExecute and Run are not generated: riscv_isolationTheory states
   what they change.

   It also proves that the functions that Next calls before running the
   instruction (Fetch and checkInterrupts) commute with the reset of log
   and c_minstret_written with which Next starts: f_LM.
   ------------------------------------------------------------------------ *)
Theory riscv_frames
Ancestors
  riscv riscv_footprint
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

val ERR = mk_HOL_ERR "riscv_framesTheory"

(* ------------------------------------------------------------------------
   1. The call graph and the fields that each function updates
   ------------------------------------------------------------------------ *)

val sty = ``:riscv_state``
fun occurs ty = ty = sty orelse
                (case Lib.total dest_type ty of
                   SOME (_, args) => List.exists occurs args
                 | NONE => false)
val defs = DB.definitions "riscv"
fun lhs_of th = lhs (snd (strip_forall (concl th)))
fun lhs_const th = fst (strip_comb (lhs_of th))
val name = fst o dest_const
val def_tab =
  List.foldl (fn ((_, th), tab) =>
                case Lib.total lhs_const th of
                  SOME c => Redblackmap.insert (tab, name c, th)
                | NONE => tab) (Redblackmap.mkDict String.compare) defs
fun def_of_name n = Redblackmap.peek (def_tab, n)
fun callees th =
  Lib.mk_set
    (map name (List.filter (fn t => #Thy (dest_thy_const t) = "riscv")
       (find_terms is_const (rhs (snd (strip_forall (concl th)))))))
fun reach_from roots =
  let
    fun reach seen [] = seen
      | reach seen (n :: rest) =
          if Binaryset.member (seen, n) then reach seen rest
          else case def_of_name n of
                 NONE => reach (Binaryset.add (seen, n)) rest
               | SOME th => reach (Binaryset.add (seen, n)) (callees th @ rest)
  in
    Binaryset.listItems (reach (Binaryset.empty String.compare) roots)
  end
val reachable = reach_from ["Next"]
fun is_state_fn_name n =
  not (String.isPrefix "recordtype." n) andalso
  not (String.isSuffix "_CASE" n) andalso
  not (String.isSuffix "_case" n) andalso
  (case def_of_name n of
     SOME th => occurs (type_of (lhs_const th))
   | NONE => false)
val state_fns = List.filter is_state_fn_name reachable

val fld_prefix = "recordtype.riscv_state.seldef."

(* the fields whose update (F_fupd) a definition mentions *)
fun direct_upds n =
  case def_of_name n of
    NONE => []
  | SOME th =>
      List.mapPartial
        (fn c => if String.isPrefix fld_prefix c andalso
                    String.isSuffix "_fupd" c
                 then SOME (String.substring (c, size fld_prefix,
                                              size c - size fld_prefix - 5))
                 else NONE) (callees th)

(* the fields that a function updates, directly or through a callee *)
val upd_tab =
  let
    val init =
      List.foldl (fn (n, t) => Redblackmap.insert (t, n, Lib.mk_set (direct_upds n)))
                 (Redblackmap.mkDict String.compare) reachable
    fun step t =
      List.foldl
        (fn (n, (t', ch)) =>
           let
             val cur = Redblackmap.find (t', n)
             val cs = case def_of_name n of SOME th => callees th | NONE => []
             val new = List.foldl (fn (c, acc) =>
                          case Redblackmap.peek (t', c) of
                            SOME u => Lib.union u acc
                          | NONE => acc) cur cs
           in
             if length new > length cur then (Redblackmap.insert (t', n, new), true)
             else (t', ch)
           end) (t, false) reachable
    fun fix t = case step t of (t', true) => fix t' | (t', false) => t'
  in
    fix init
  end
fun upds n = Redblackmap.find (upd_tab, n)

(* The classification that the frames rely on, checked: these are the only
   functions reachable from Next that update the control state that U-mode
   must not change (riscv_isolationTheory). *)
val () =
  let
    fun updaters fld = List.filter (fn n => Lib.mem fld (upds n)) state_fns
    fun check (fld, expected) =
      if Lib.set_eq (updaters fld) expected then ()
      else raise ERR "classification"
             ("the functions that update " ^ fld ^ " are not the expected ones: " ^
              "unexpected [" ^
              String.concatWith ", " (Lib.set_diff (updaters fld) expected) ^
              "], missing [" ^
              String.concatWith ", " (Lib.set_diff expected (updaters fld)) ^ "]")
  in
    List.app check
      [("c_privilege", ["setPrivilege", "mret", "sret", "takeTrap", "Next"]),
       ("c_PC", ["write'PC", "mret", "sret", "takeTrap", "Next"]),
       ("procID", []), ("totalCore", []),
       ("c_ReserveLoad", ["write'ReserveLoad", "dfn'LR_W", "dfn'LR_D",
                          "dfn'SC_W", "dfn'SC_D", "Run", "fetchAndExecute",
                          "Next"]),
       ("c_SCSR", ["write'CSRMap", "write'CSR", "writeCSR", "accessCSR",
                   "dfn'CSRRW", "dfn'CSRRS", "dfn'CSRRC", "dfn'CSRRWI",
                   "dfn'CSRRSI", "dfn'CSRRCI", "write'SCSR", "Run", "takeTrap",
                   "fetchAndExecute", "Next"])]
  end

(* ------------------------------------------------------------------------
   2. The frames
   ------------------------------------------------------------------------ *)

val frame_fields =
  ["procID", "totalCore", "c_privilege", "c_PC", "c_SCSR", "c_MCSR", "c_fpr",
   "c_UCSR", "c_ReserveLoad", "c_NextFetch", "c_gpr", "MEM8"]

fun field_sel fld = prim_mk_const {Name = fld_prefix ^ fld, Thy = "riscv"}
fun sel fld st = mk_comb (field_sel fld, st)

fun deps n =
  case def_of_name n of
    NONE => []
  | SOME th => List.filter (fn d => d <> n andalso Lib.mem d state_fns) (callees th)
fun topo done [] = rev done
  | topo done todo =
      let
        val (ready, later) =
          List.partition (fn c => List.all (fn d => Lib.mem d done) (deps c)) todo
      in
        if null ready then raise ERR "topo" "cycle" else topo (rev ready @ done) later
      end
val order = topo [] state_fns

val cond_lemmas =
  map (fn fld =>
         let
           val b = mk_var ("b", bool)
           val x = mk_var ("x", sty)
           val y = mk_var ("y", sty)
           val g = mk_eq (sel fld (mk_cond (b, x, y)), mk_cond (b, sel fld x, sel fld y))
         in
           Q.prove (`^g`, rw [])
         end) frame_fields

Theorem SND_COND[local]:
  !b x y. SND (if b then x else y) = if b then SND x else SND y
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

(* the application of f to its arguments and the state s, as in its
   definition *)
fun applied n s =
  let
    val th = valOf (def_of_name n)
    val c = lhs_const th
    val (_, dargs) = strip_comb (lhs_of th)
    val (args, rty) = strip_fun (type_of c)
    val app =
      case (args, dargs) of
        ([_], _) => mk_comb (c, s)
      | ([_, _], [d]) => mk_comb (mk_comb (c, d), s)
      | _ => raise ERR "applied" n
  in
    (app, rty)
  end

val not_framed = ["Next", "fetchAndExecute", "Run"]

fun frame_goal n =
  let
    val s = mk_var ("s", sty)
    val (app, rty) = applied n s
    val st = if rty = sty then SOME app
             else if occurs rty then SOME (pairSyntax.mk_snd app) else NONE
    val flds = List.filter (fn f => not (Lib.mem f (upds n))) frame_fields
  in
    case (st, flds) of
      (SOME t, _ :: _) =>
        let val g = list_mk_conj (map (fn f => mk_eq (sel f t, sel f s)) flds)
        in SOME (list_mk_forall (free_vars g, g)) end
    | _ => NONE
  end

local
  val frames = ref ([] : thm list)
  fun tacA def =
    rpt gen_tac
    \\ simp ([def, SND_COND, UNCURRY_FST_SND] @ cond_lemmas @ !frames)
    \\ rpt (CASE_TAC \\ simp ([SND_COND, UNCURRY_FST_SND] @ cond_lemmas @ !frames))
  fun tacC def =
    rpt gen_tac
    \\ (fn g as (_, w) =>
          case List.filter (fn v => type_of v = ``:word4``) (free_vars w) of
            i :: _ => strip_assume_tac (SPEC i word4_cases) g
          | [] => raise ERR "tacC" "no word4 variable")
    \\ simp ([def, SND_COND, UNCURRY_FST_SND] @ cond_lemmas @ !frames)
  fun tac def = FIRST (map (fn t => t def \\ NO_TAC) [tacA, tacC])
  fun prove_one n =
    if Lib.mem n not_framed then NONE
    else
      case frame_goal n of
        NONE => NONE
      | SOME g =>
          let
            val th = Q.prove (`^g`, tac (valOf (def_of_name n)))
          in
            frames := th :: !frames;
            SOME (n, save_thm (n ^ "_frame", th))
          end
in
  val frame_thms = List.mapPartial prove_one order
end

val () =
  print ("riscv_frames: " ^ Int.toString (length frame_thms) ^
         " frames of the " ^ Int.toString (length state_fns) ^
         " state functions reachable from Next\n")

(* ------------------------------------------------------------------------
   3. Fetch and checkInterrupts commute with the reset of log and
      c_minstret_written at the start of Next

   Next first sets log to [] and c_minstret_written of the hart to F; no
   function that Fetch or checkInterrupts calls reads or writes either.
   ------------------------------------------------------------------------ *)

val lm_marks =
  map (fn f => fld_prefix ^ f)
      ["log", "log_fupd", "c_minstret_written", "c_minstret_written_fupd"]

fun mentions_lm n =
  let
    fun go seen [] = false
      | go seen (d :: rest) =
          if Lib.mem d seen then go seen rest
          else if Lib.mem d lm_marks then true
          else case def_of_name d of
                 NONE => go (d :: seen) rest
               | SOME th => go (d :: seen) (rest @ callees th)
  in
    go [] [n]
  end

val lm_fns =
  List.filter (fn n => Lib.mem n (List.filter is_state_fn_name
                                    (reach_from ["Fetch", "checkInterrupts"])))
              order

val () =
  case List.filter mentions_lm lm_fns of
    [] => ()
  | l => raise ERR "lm" ("these read or write log or c_minstret_written: " ^
                         String.concatWith ", " l)

(* One pass per field, f_log for log and f_minstret for c_minstret_written
   (a single field update, so that the simplifier's normalisation of
   record updates cannot reorder the two):

     f x (s with F := v) = f x s with F := v   (and as for f_MEM8) *)
fun comm_pass (fld, v, suffix) =
  let
    val upd_c = prim_mk_const {Name = fld_prefix ^ fld ^ "_fupd", Thy = "riscv"}
    (* st with fld := v *)
    fun with_f st =
      mk_comb (mk_comb (upd_c, combinSyntax.mk_K_1 (v, type_of v)), st)
    val COND_UP =
      let
        val b = mk_var ("b", bool)
        val x = mk_var ("x", sty)
        val y = mk_var ("y", sty)
      in
        Q.prove (`!^b ^x ^y ^v. (if ^b then ^(with_f x) else ^(with_f y)) =
                                ^(with_f (mk_cond (b, x, y)))`, rw [])
      end
    fun goal n =
      let
        val s = mk_var ("s", sty)
        val (app, rty) = applied n s
        val (lapp, _) = applied n (with_f s)
        val r =
          if rty = sty then with_f app
          else if occurs rty then
            pairSyntax.mk_pair (pairSyntax.mk_fst app, with_f (pairSyntax.mk_snd app))
          else app
        val g = mk_eq (lapp, r)
      in
        list_mk_forall (free_vars g, g)
      end
    val lemmas = ref ([] : thm list)
    fun tacA def =
      rpt gen_tac
      \\ simp ([def, COND_UP, UNCURRY_FST_SND] @ !lemmas)
      \\ rpt (CASE_TAC \\ simp ([COND_UP, UNCURRY_FST_SND] @ !lemmas))
    fun tacB def =
      rw [def] \\ fs (!lemmas) \\ rpt (CASE_TAC \\ fs (!lemmas))
    fun tacC def =
      rpt gen_tac
      \\ (fn g as (_, w) =>
            case List.filter (fn v => type_of v = ``:word4``) (free_vars w) of
              i :: _ => strip_assume_tac (SPEC i word4_cases) g
            | [] => raise ERR "tacC" "no word4 variable")
      \\ simp ([def, COND_UP, UNCURRY_FST_SND] @ !lemmas)
    fun tac def = FIRST (map (fn t => t def \\ NO_TAC) [tacA, tacB, tacC])
    fun prove_one n =
      let
        val th = Q.prove (`^(goal n)`, tac (valOf (def_of_name n)))
                 handle e => (print ("riscv_frames: no " ^ suffix ^
                                     " lemma for " ^ n ^ "\n"); raise e)
      in
        lemmas := th :: !lemmas;
        save_thm (n ^ "_" ^ suffix, th)
      end
  in
    map prove_one lm_fns
  end

val log_thms =
  comm_pass ("log", mk_var ("l", ``:(num # string) list``), "log")
val minstret_thms =
  comm_pass ("c_minstret_written", mk_var ("w", ``:word8 -> bool``), "minstret")
