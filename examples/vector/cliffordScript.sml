(* ========================================================================= *)
(* Geometric algebra.                                                        *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2008                       *)
(* ========================================================================= *)

(* TODO: Clean-up *)
open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;

open hurdUtils vectorTheory binary_expansionTheory;

val _ = new_theory "clifford";

(* ------------------------------------------------------------------------- *)
(* Some basic lemmas, mostly set theory.                                     *)
(* ------------------------------------------------------------------------- *)

Theorem CARD_UNION_LEMMA:
 FINITE s /\ FINITE t /\ FINITE u /\ FINITE v /\
  s INTER t = {} /\ u INTER v = {} /\ s UNION t = u UNION v
  ==> CARD(s) + CARD(t) = CARD(u) + CARD(v)
Proof
 MESON_TAC[CARD_UNION]
QED

Theorem CARD_DIFF_INTER:
 !s t. FINITE s ==> CARD s = CARD(s DIFF t) + CARD(s INTER t)
Proof
 REPEAT STRIP_TAC >>
 CONV_TAC SYM_CONV >>
 MATCH_MP_TAC CARD_UNION_EQ >>
 ASM_REWRITE_TAC[] >>
 SET_TAC[]
QED

Triviality INTER_ACI:
!p q r.
        p INTER q = q INTER p /\
        p INTER q INTER r = q INTER p INTER r /\ p INTER p = p /\
        p INTER p INTER q = p INTER q
Proof
cheat
QED

(* from sets.ml of HOL Light *)
Triviality CARD_UNION_hol_light:
 !(s:'a->bool) t. FINITE(s) /\ FINITE(t) /\ (s INTER t = EMPTY)
         ==> (CARD (s UNION t) = CARD s + CARD t)
Proof
 cheat
QED

Theorem CARD_ADD_SYMDIFF_INTER:
 !s t:'a->bool.
      FINITE s /\ FINITE t
      ==> CARD s + CARD t =
          CARD((s DIFF t) UNION (t DIFF s)) + 2 * CARD(s INTER t)
Proof
 REPEAT STRIP_TAC >>
 SUBST1_TAC(Q.SPEC `t:'a->bool`(MATCH_MP CARD_DIFF_INTER
  (Q.ASSUME `FINITE(s:'a->bool)`))) >>
 SUBST1_TAC(Q.SPEC `s:'a->bool`(MATCH_MP CARD_DIFF_INTER
  (Q.ASSUME `FINITE(t:'a->bool)`))) >>
 `CARD (s DIFF t UNION (t DIFF s)) = CARD (s DIFF t) + CARD (t DIFF s)` suffices_by (
  metis_tac [INTER_COMM, ARITH_PROVE ``c:num = a + b ==> (a + x) + (b + x) = c + 2 * x``]
 ) >>
 MATCH_MP_TAC CARD_UNION_hol_light >>
 fs [FINITE_DIFF] >>
 SET_TAC []
QED

Theorem SYMDIFF_PARITY_LEMMA:
 !s t u. FINITE s /\ FINITE t /\ (s DIFF t) UNION (t DIFF s) = u
         ==> EVEN(CARD u) = (EVEN(CARD s) <=> EVEN(CARD t))
Proof
 ONCE_REWRITE_TAC [GSYM EVEN_ADD] >>
 fs [CARD_ADD_SYMDIFF_INTER] >>
 fs [EVEN_ADD, EVEN_MULT]
QED

(* from pair.ml of HOL Light *)
Triviality FORALL_PAIR_THM:
 !P. (!p. P p) <=> (!p1 p2. P(p1,p2))
Proof
 MESON_TAC [PAIR]
QED

(* TODO: Count from zero? *)
Theorem FINITE_CART_SUBSET_LEMMA:
 !P m n. FINITE {(i,j) | i IN {1 .. m} /\ j IN {1 .. n} /\ P i j}
Proof
 REPEAT STRIP_TAC >>
 MATCH_MP_TAC SUBSET_FINITE_I >>
 qexists_tac `{(i,j) | i IN {1 .. m} /\ j IN {1 .. n}}` >>
 fs [SUBSET_DEF, cardinalTheory.FINITE_PRODUCT, FINITE_NUMSEG,
     FORALL_PAIR_THM, cardinalTheory.IN_ELIM_PAIR_THM]
QED

(* ------------------------------------------------------------------------- *)
(* Index type for "multivectors" (k-vectors for all k <= N).                 *)
(* ------------------------------------------------------------------------- *)

(* TODO: It seems the new_type_definition of HOL4 forces this to strictly
 *       adhere to the form ?x. P x, hence the lambda *)
Theorem multivector_tybij_th:
 ?s. (\s'. s' SUBSET (count $ dimindex(:'N))) s
Proof
 MESON_TAC [EMPTY_SUBSET]
QED

val multivector_TY_DEF = new_type_definition ("multivector", multivector_tybij_th);

val multivector_tybij =
 define_new_type_bijections
  {name="multivector_tybij",
   ABS="mk_multivector",
   REP="dest_multivector",
   tyax=multivector_TY_DEF};

Theorem MULTIVECTOR_IMAGE:
 univ(:('N)multivector) = IMAGE (mk_multivector:(num -> bool) -> 'N multivector) {s | s SUBSET (count $ dimindex(:'N))}
Proof
 fs [EXTENSION, IN_UNIV, IN_IMAGE] >>
 MESON_TAC [multivector_tybij]
QED

(* from sets.ml *)
(* TODO: Put in cardinalTheory? *)
Triviality HAS_SIZE_POWERSET:
 !(s:'a->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 ** n)
Proof
(*
 REPEAT STRIP_TAC >> SUBGOAL_THEN
  `{t | t SUBSET s} =
   {f | (!x:A. x IN s ==> f(x) IN UNIV) /\ (!x. ~(x IN s) ==> (f x = F))}`
 SUBST1_TAC >| [
  REWRITE_TAC[EXTENSION, IN_ELIM_THM, IN_UNIV, SUBSET, IN, CONTRAPOS_THM];
  MATCH_MP_TAC HAS_SIZE_FUNSPACE >> ASM_REWRITE_TAC[] >>
  CONV_TAC HAS_SIZE_CONV >> MAP_EVERY EXISTS_TAC [`T`; `F`] >>
  REWRITE_TAC[EXTENSION; IN_UNIV; IN_INSERT; NOT_IN_EMPTY] >>
  CONV_TAC TAUT]
*)
cheat
QED

(* TODO: Translate count to numseg *)
Triviality COUNT_NUMSEG:
 !n. count n = if n = 0 then {} else {0 .. n - 1}
Proof
 fs [count_def, NUMSEG_LT]
QED

Triviality NUMSEG_COUNT_dimindex:
 {0 .. dimindex (:'N) − 1} = count (dimindex (:'N))
Proof
 cheat
QED

Triviality count_dimindex_HAS_SIZE:
 count (dimindex (:'N)) HAS_SIZE dimindex (:'N)
Proof
 cheat
QED

Theorem HAS_SIZE_MULTIVECTOR:
 univ(:('N)multivector) HAS_SIZE (2 ** dimindex(:'N))
Proof
 REWRITE_TAC [MULTIVECTOR_IMAGE]
 >> match_mp_tac HAS_SIZE_IMAGE_INJ
 >> conj_tac
 >- (fs [NUMSEG_COUNT_dimindex] >> metis_tac [multivector_tybij])
 >> irule HAS_SIZE_POWERSET
 >> fs [count_dimindex_HAS_SIZE]
QED

Theorem FINITE_MULTIVECTOR:
 FINITE univ(:('N)multivector)
Proof
 MESON_TAC [HAS_SIZE, HAS_SIZE_MULTIVECTOR]
QED

Theorem DIMINDEX_UNIQUE:
 !n. univ(:'a) HAS_SIZE n ==> dimindex(:'a) = n
Proof
 metis_tac [dimindex_def, HAS_SIZE]
QED

Theorem DIMINDEX_MULTIVECTOR:
 dimindex(:('N)multivector) = 2 EXP dimindex(:'N)
Proof
 MESON_TAC [DIMINDEX_UNIQUE, HAS_SIZE_MULTIVECTOR]
QED

Theorem DEST_MK_MULTIVECTOR:
 !s. s SUBSET {0 .. dimindex(:'N)-1}
     ==> dest_multivector(mk_multivector s :('N)multivector) = s
Proof
 fs [NUMSEG_COUNT_dimindex, GSYM multivector_tybij]
QED

Theorem FORALL_MULTIVECTOR:
 !P. (!s. s SUBSET {0 .. dimindex(:'N)-1} ==> P(mk_multivector s)) <=>
     (!m:('N)multivector. P m)
Proof
 gen_tac
 >> EQ_TAC
 >- (rpt strip_tac >>
     MP_TAC (Q.ISPEC `m:('N)multivector` (REWRITE_RULE [EXTENSION] MULTIVECTOR_IMAGE)) >>
     fs [NUMSEG_COUNT_dimindex, IN_UNIV, IN_IMAGE] >>
     metis_tac [])
 >> fs []
QED

(* ------------------------------------------------------------------------- *)
(* The bijections we use for indexing.                                       *)
(*                                                                           *)
(* Note that we need a *single* bijection over the entire space that also    *)
(* works for the various subsets. Hence the tedious explicit construction.   *)
(* ------------------------------------------------------------------------- *)

(* setcode and codeset become super simple for zero-indexed FCPs *)
Definition setcode_def:
 setcode s = binarysum s
End

Definition codeset_def:
 codeset n = bitset n
End

Theorem CODESET_SETCODE_BIJECTIONS:
 !n.
 (!i. i IN {0 .. (2 ** n)-1}
      ==> codeset i SUBSET {0 .. (n-1)} /\ setcode(codeset i) = i) /\
 (!s. s SUBSET ({0 .. (n-1)})
      ==> (setcode s) IN {0 .. (2 ** n)-1} /\ codeset(setcode s) = s)
Proof
(*
  REWRITE_TAC[codeset; setcode; ADD_SUB2; GSYM IMAGE_o; o_DEF; PRE] THEN
  REWRITE_TAC[SET_RULE `IMAGE (\x. x) s = s`] THEN CONJ_TAC THEN GEN_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_NUMSEG] THEN
    SIMP_TAC[ARITH_RULE `1 <= i ==> (1 + b = i <=> b = i - 1)`] THEN
    REWRITE_TAC[ARITH_RULE `1 <= SUC n /\ SUC n <= k <=> n < k`] THEN
    DISCH_THEN(MP_TAC o MATCH_MP
     (ARITH_RULE `1 <= i /\ i <= t ==> i - 1 < t`)) THEN
    MESON_TAC[BITSET_BOUND; BINARYSUM_BITSET];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o ISPEC `PRE` o MATCH_MP IMAGE_SUBSET) THEN
  REWRITE_TAC[IN_NUMSEG; SUBSET] THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `x < n ==> 1 <= 1 + x /\ 1 + x <= n`) THEN
    MATCH_MP_TAC BINARYSUM_BOUND THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[IN_IMAGE; IN_NUMSEG] THEN ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE SUC (IMAGE PRE s)` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_IMAGE; FINITE_SUBSET; FINITE_NUMSEG; BITSET_BINARYSUM];
    ALL_TAC] THEN
  UNDISCH_TAC `s SUBSET 1..n` THEN
  REWRITE_TAC[SUBSET; EXTENSION; IN_IMAGE; IN_NUMSEG] THEN
  MESON_TAC[ARITH_RULE `1 <= n ==> SUC(PRE n) = n`]
*)
cheat
QED

Theorem FORALL_SETCODE:
 !n P. (!s. s SUBSET ({0 .. (n-1)}) ==> P(setcode s)) <=> (!i. i IN {0 .. (2 EXP n)-1} ==> P i)
Proof
 MESON_TAC [CODESET_SETCODE_BIJECTIONS, SUBSET_DEF]
QED

Theorem SETCODE_BOUNDS:
 !s n. s SUBSET {0 .. n-1} ==> setcode s IN ({0 .. (2 EXP n)-1})
Proof
 MESON_TAC [CODESET_SETCODE_BIJECTIONS]
QED

(* ------------------------------------------------------------------------- *)
(* Indexing directly via subsets.                                            *)
(* ------------------------------------------------------------------------- *)
(* HOL Light:
parse_as_infix("$$",(25,"left"));;

let sindex = new_definition
  `(x:real^(N)multivector)$$s = x$(setcode s)`;;
*)
val sindex_def = new_infixl_definition("sindex", “($sindex:real['N multivector] -> (num -> bool) -> real) x s = x ' (setcode s)”, 500);
(* Since "$" of HOL Light is called "'" in HOL4, "$$" is translated to "''" *)
val () = set_fixity "''" (Infixl 2000);
val () = overload_on ("''", ``$sindex:real['N multivector] -> (num -> bool) -> real``);
(* Overload "''" = “$sindex:real['N multivector] -> (num -> bool) -> real”; *)

(* EVERYTHING TODO BELOW THIS POINT *)
(* HOL Light:
parse_as_binder "lambdas";;

let lambdas = new_definition
 `(lambdas) (g:(num->bool)->real) =
    (lambda i. g(codeset i)):real^(N)multivector`;;
*)
(* TODO: What is best used in HOL4 to set up a new binder? *)
(*

boolSyntax.new_binder("lambdas", “:((num -> bool) -> real) -> real['N multivector]”); ?

val _ = term_grammar.add_binder("lambdas", std_binder_precedence);
val lambdas_def = new_binder_definition("lambdas_def", “lambdas (g:(num -> bool) -> real) =
  (FCP i. g (codeset i)):real['N multivector]”);
*)

(* This seems to set up "FCPs" as a binder automatically... *)
boolSyntax.new_binder("FCPs", “:((num -> bool) -> real) -> real['N multivector]”);

Definition FCPs_def:
 (FCPs) (g:(num -> bool) -> real) =
  (FCP i. g (codeset i)):real['N multivector]
End

(* ------------------------------------------------------------------------- *)
(* Crucial properties.                                                       *)
(* ------------------------------------------------------------------------- *)

Triviality SUB_LESS_dimindex:
!i.
 i <= 2 ** dimindex (:'N) - 1 ==>
 i < 2 ** dimindex (:'N)
Proof
fs [GSYM DIMINDEX_MULTIVECTOR]
>> rpt strip_tac
>> Cases_on ‘i = dimindex (:'N multivector) - 1’
>> (fs [])
QED

Theorem MULTIVECTOR_EQ:
 !x y:real['N multivector].
 x = y <=> !s. s SUBSET ({0 .. dimindex(:'N)-1}) ==> (x '' s) = (y '' s)
Proof
fs [CART_EQ, NUMSEG_COUNT_dimindex]
>> fs [sindex_def]
>> fs [GSYM NUMSEG_COUNT_dimindex, FORALL_SETCODE]
>> fs [DIMINDEX_MULTIVECTOR]
>> metis_tac [SUB_LESS_OR, SUB_LESS_dimindex]
QED

Theorem MULTIVECTOR_BETA:
 !g s. s SUBSET ({0 .. dimindex(:'N)-1})
         ==> ((FCPs) g :real['N multivector]) '' s = g s
Proof
(*
  SIMP_TAC[sindex; lambdas; LAMBDA_BETA; SETCODE_BOUNDS;
           DIMINDEX_MULTIVECTOR; GSYM IN_NUMSEG] THEN
  MESON_TAC[CODESET_SETCODE_BIJECTIONS]
*)
fs[sindex_def]
>> fs [FCPs_def]
>> fs [FCP_BETA] (* TODO: This should be made to work with some fixing... *)
>> fs [SETCODE_BOUNDS]
>> cheat
QED

Theorem MULTIVECTOR_UNIQUE:
 !m:real['N multivector] g.
        (!s. s SUBSET {0 .. dimindex(:'N)-1} ==> m '' s = g s)
        ==> (FCPs) g = m
Proof
fs[MULTIVECTOR_EQ, MULTIVECTOR_BETA]
QED

Theorem MULTIVECTOR_ETA:
 !m. (FCPs s. m '' s) = m
Proof
fs[MULTIVECTOR_EQ, MULTIVECTOR_BETA]
QED

(* ------------------------------------------------------------------------- *)
(* Also componentwise operations; they all work in this style.               *)
(* ------------------------------------------------------------------------- *)

Theorem MULTIVECTOR_ADD_COMPONENT:
 !x y:real['N multivector] s.
      s SUBSET {0 .. dimindex(:'N)-1} ==> (x + y) '' s = x '' s + y '' s
Proof
rpt strip_tac
>> IMP_RES_TAC SETCODE_BOUNDS
>> fs[sindex_def, VECTOR_ADD_COMPONENT, DIMINDEX_MULTIVECTOR, SUB_LESS_dimindex]
QED

Theorem MULTIVECTOR_MUL_COMPONENT:
 !c x:real['N multivector] s.
      s SUBSET {0 .. dimindex(:'N)-1} ==> (c * x) '' s = c * x '' s
Proof
rpt strip_tac
>> IMP_RES_TAC SETCODE_BOUNDS
>> fs[sindex_def, VECTOR_MUL_COMPONENT, DIMINDEX_MULTIVECTOR, SUB_LESS_dimindex]
QED

Theorem MULTIVECTOR_VEC_COMPONENT:
 !k s. s SUBSET {0 .. dimindex(:'N)-1} ==> (vec k :real['N multivector]) '' s = &k
Proof
rpt strip_tac
>> IMP_RES_TAC SETCODE_BOUNDS
>> fs[sindex_def, VEC_COMPONENT, DIMINDEX_MULTIVECTOR, SUB_LESS_dimindex]
QED

Theorem MULTIVECTOR_VSUM_COMPONENT:
 !f:'a->real['N multivector] t s.
        s SUBSET {0 .. dimindex(:'N)-1}
        ==> (vsum t f) '' s = sum t (\x. (f x) '' s)
Proof
rpt strip_tac
>> IMP_RES_TAC SETCODE_BOUNDS
>> fs[vsum_def, sindex_def]
>> fs[FCP_BETA, GSYM IN_NUMSEG,
      DIMINDEX_MULTIVECTOR, SUB_LESS_dimindex]
QED

Theorem MULTIVECTOR_VSUM:
 !t f. vsum t f = FCPs s. sum t (\x. (f x) '' s)
Proof
fs[MULTIVECTOR_EQ, MULTIVECTOR_BETA, MULTIVECTOR_VSUM_COMPONENT]
QED

(* ------------------------------------------------------------------------- *)
(* Basis vectors indexed by subsets of {1 .. N}.                             *)
(* ------------------------------------------------------------------------- *)

Definition mbasis_def:
 mbasis i = FCPs s. if i = s then &1 else &0
End

Theorem MBASIS_COMPONENT:
 !s t. s SUBSET {0 .. dimindex(:'N)-1}
         ==> (mbasis t :real['N multivector]) '' s = if s = t then &1 else &0
Proof
 simp[mbasis_def, MULTIVECTOR_BETA]
 >> metis_tac[]
QED

Theorem MBASIS_EQ_0:
  !s. (mbasis s :real['N multivector] = vec 0) <=>
      ~(s SUBSET {0 .. dimindex(:'N)-1})
Proof
  simp[MULTIVECTOR_EQ, MBASIS_COMPONENT, MULTIVECTOR_VEC_COMPONENT]
  >> metis_tac[prove (“~(&1:real = &0)”, simp[])]
QED

Theorem MBASIS_NONZERO:
  !s. s SUBSET {0 .. dimindex(:'N)-1} ==> ~(mbasis s :real['N multivector] = vec 0)
Proof
  REWRITE_TAC[MBASIS_EQ_0]
QED

Theorem MBASIS_EXPANSION:
  !x:real['N multivector].
       vsum {s | s SUBSET {0 .. dimindex(:'N)-1}} (\s. x '' s * mbasis s) = x
Proof
  simp[MULTIVECTOR_EQ, MULTIVECTOR_VSUM_COMPONENT,
       MULTIVECTOR_MUL_COMPONENT, MBASIS_COMPONENT] >>
  rpt strip_tac >>
  GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) empty_rewrites [EQ_SYM_EQ] >>
  fs[prove(“x:real * (if p then &1 else &0) = if p then x else &0”, CASE_TAC >> (simp[])),
     SUM_DELTA]
QED

(* TODO:

Use span definition from real_topologyTheory:

Theorem SPAN_MBASIS:
  span {mbasis s :real['N multivector] | s SUBSET {0 .. dimindex(:'N)-1}} = UNIV
Proof
  REWRITE_TAC[EXTENSION; IN_UNIV] THEN X_GEN_TAC `x:real^(N)multivector` THEN
  GEN_REWRITE_TAC LAND_CONV [GSYM MBASIS_EXPANSION] THEN
  MATCH_MP_TAC SPAN_VSUM THEN
  SIMP_TAC[FINITE_NUMSEG; FINITE_POWERSET; IN_ELIM_THM] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SPAN_MUL THEN
  MATCH_MP_TAC SPAN_SUPERSET THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_MESON_TAC[]
QED

*)

val _ = export_theory ();
val _ = html_theory "clifford";
