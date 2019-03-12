(* ========================================================================= *)
(* FILE          : rlTruth.sml                                               *)
(* DESCRIPTION   : Estimating of the truth of a formula                      *)
(* AUTHOR        : (c) Thibault Gauthier, University of Innsbruck            *)
(* DATE          : 2018                                                      *)
(* ========================================================================= *)

structure rlTruth :> rlTruth =
struct

(*
  load "mlTreeNeuralNetwork"; load "rlLib"; load "psTermGen";
  load "mlNearestNeighbor"; load "psTermGen";
*)

open HolKernel Abbrev boolLib aiLib rlLib psTermGen

val ERR = mk_HOL_ERR "rlTruth"

(* -------------------------------------------------------------------------
   Ground arithmetic truth
   ------------------------------------------------------------------------- *)

fun eval_ground tm = 
  (string_to_int o term_to_string o rhs o concl o bossLib.EVAL) tm

fun mk_ttset_ground (maxsize,maxvalue) ntarget =
  let
    val cset = [``0``,``$+``,``SUC``,``$*``]
    val tml0 = gen_term_size maxsize (``:num``,cset)
    val tml1 = mapfilter (fn x => (eval_ground x,x)) tml0
    val tmld = dregroup Int.compare tml1
    val nl = List.tabulate (maxvalue + 1, I)
    fun random_true _ =
      let val tml = dfind (random_elem nl) tmld in
        (mk_eq (random_elem tml, random_elem tml), [1.0])
      end
    fun random_false _ =
      let
        val (n1,n2) = pair_of_list (first_n 2 (shuffle nl))
        val tml1 = dfind n1 tmld
        val tml2 = dfind n2 tmld
      in
        (mk_eq (random_elem tml1, random_elem tml2), [0.0])
      end
  in
    (
    List.tabulate (ntarget div 2, random_true) @
    List.tabulate (ntarget div 2, random_false),
    List.tabulate (ntarget div 2, random_true) @
    List.tabulate (ntarget div 2, random_false)
    )
  end

(* -------------------------------------------------------------------------
   Ground arithmetic proof
   ------------------------------------------------------------------------- *)

fun mk_add2 (n1,n2) = mk_add (mk_sucn n1, mk_sucn n2)

fun mk_add3 (n1,n2,n3) =
  [mk_add (mk_add2 (n1,n2), mk_sucn n3),
   mk_add (mk_sucn n1, mk_add2 (n2,n3))]

fun mk_add4 (n1,n2,n3,n4) =
  let 
    val (t1,t2,t3,t4) = (mk_sucn n1,mk_sucn n2,mk_sucn n3,mk_sucn n4)
  in
    map (fn x => (mk_add (t1,x))) (mk_add3 (n2,n3,n4)) @
    map (fn x => (mk_add (x,t4))) (mk_add3 (n1,n2,n3)) @
    [mk_add (mk_add (t1,t2), mk_add (t3,t4))]
  end
 
fun eq_maxsize maxsize tm = mk_eq (tm, mk_sucn maxsize)

fun mk_addsuceq_one maxsize =
  let 
    val l2 = number_partition 2 maxsize
    val tml2 = map (mk_add2 o pair_of_list) l2
    val l3 = number_partition 3 maxsize
    val tml3 = List.concat (map (mk_add3 o triple_of_list) l3)
    val l4 = number_partition 4 maxsize
    val tml4 = List.concat (map (mk_add4 o quadruple_of_list) l4)
  in
    map (eq_maxsize maxsize) (tml2 @ tml3 @ tml4)
  end

fun mk_addsuceq maxsize =
  List.concat (List.tabulate (maxsize - 3, fn x => mk_addsuceq_one (x + 4)))


fun norm tm = PURE_ONCE_REWRITE_CONV [arithmeticTheory.ADD_0,GSYM   arithmeticTheory.ADD_SUC] tm;

fun imin l = hd (dict_sort Int.compare l)

fun depth_diff (tm1,tm2) = 
  let 
    val (oper1,argl1) = strip_comb tm1
    val (oper2,argl2) = strip_comb tm2
  in
    if term_eq oper1 oper2 andalso length argl1 = length argl2
    then 
      let val l = List.mapPartial depth_diff (combine (argl1,argl2)) in
        if null l then NONE else SOME (1 + imin l)
      end
    else SOME 0
  end

fun is_refl tm = let val (a,b) = dest_eq tm in term_eq a b end

fun list_cost tm =
  let val newtm = (rhs o concl) (norm tm) in
    if term_eq newtm tm then raise ERR "total_cost" "" else
    if is_refl newtm then [(newtm,0)] else
      let val cost = 1 + valOf (depth_diff (tm,newtm)) in
        (newtm,cost) :: list_cost newtm
      end
  end

fun total_cost tm = sum_int (map snd (list_cost tm))





end (* struct *)

(*
app load ["rlTruth", "aiLib", "rlLib", "mlTreeNeuralNetwork", "psTermGen"];
open rlTruth aiLib rlLib mlTreeNeuralNetwork psTermGen;

val maxsize = 9; val maxvalue = 4; val ntarget = 10000;
val (trainset,testset) = mk_ttset_ground (maxsize,maxvalue) ntarget;

val operl = mk_fast_set oper_compare (operl_of ``0 + SUC 0 * 0 = 0``);
val randtnn = random_tnn (8,1) operl;
val bsize = 10000;
val schedule = [(10,0.1)];

use_thread_flag := true;
val ncore = 1;
val _ = prepare_train_tnn (ncore,bsize) randtnn (trainset,testset) schedule;
val ncore = 2;
val _ = prepare_train_tnn (ncore,bsize) randtnn (trainset,testset) schedule;
val ncore = 3;
val _ = prepare_train_tnn (ncore,bsize) randtnn (trainset,testset) schedule;

use_thread_flag := false;
val _ = prepare_train_tnn (1,bsize) randtnn (trainset,testset) schedule;
val _ = 
  parmap 3
  (prepare_train_tnn (1,bsize) randtnn (trainset,testset)) 
  [schedule,schedule];

val tm = mk_eq (mk_mult (mk_sucn 2, mk_sucn 2), mk_sucn 4);
infer_tnn tnn tm; (* todo: scale this learning to arbitrary large terms *)

*)





