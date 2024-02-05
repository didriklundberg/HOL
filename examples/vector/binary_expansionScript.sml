(* ========================================================================= *)
(* Binary expansions as a bijection between numbers and finite sets.         *)
(* ========================================================================= *)

(* TODO: Clean-up *)
open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory
     simpLib;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;

val _ = new_theory "binary_expansion";

(* from LT_POW2_REFL in arith.ml of HOL Light *)
Triviality LESS_POW2_REFL:
 !n. n < 2 EXP n
Proof
 Induct >> (
  fs [EXP]
 )
QED

(* from int.ml of HOL Light *)
Triviality BINARY_INDUCT:
 !P. P (0:num) /\ (!n. P n ==> P(2 * n) /\ P(2 * n + 1)) ==> !n. P n
Proof
 ntac 2 strip_tac >>
 match_mp_tac COMPLETE_INDUCTION >>
 gen_tac >>
 Q.SUBGOAL_THEN `n = 0 \/ n DIV 2 < n /\ (n = 2 * (n DIV 2) \/ n = 2 * (n DIV 2) + 1)`
  STRIP_ASSUME_TAC >- (
  ASSUME_TAC (Q.SPEC `n` EVEN_OR_ODD) >>
  fs [] >| [
   Cases_on `n` >> (
    fs [EVEN, GSYM ODD_EVEN]
   ),

   ALL_TAC
  ] >> (
   fs [ODD_EXISTS, ADD1]
  )
 ) >> (
  metis_tac []
 )
QED

(* from arith.ml of HOL Light *)
Triviality DIV_UNIQ:
 !m n q r. (m = q * n + r) /\ r < n ==> (m DIV n = q)
Proof
 metis_tac [DIVMOD_UNIQ]
QED

Theorem BOUNDED_FINITE:
 !s. (!x:num. x IN s ==> x <= n) ==> FINITE s
Proof
 rpt strip_tac >>
 match_mp_tac SUBSET_FINITE_I >>
 qexists_tac `{0 .. n}` >>
 fs [SUBSET_DEF, FINITE_NUMSEG]
QED

Theorem EVEN_NSUM:
 !s. FINITE s /\ (!i. i IN s ==> EVEN(f i)) ==> EVEN(nsum s f)
Proof
 rewrite_tac [cardinalTheory.CONJ_EQ_IMP] >> (* TODO: Is there a better counterpart to IMP_CONJ? *)
 match_mp_tac (SIMP_RULE std_ss [] (Q.ISPEC `\s. (!i. i IN s ==> EVEN (f i)) ==> EVEN (nsum s f)` FINITE_INDUCT)) >> (* TODO: Why so hard to match? *)
 fs [NSUM_CLAUSES, EVEN_ADD, IN_INSERT]
QED

(* ------------------------------------------------------------------------- *)
(* The basic bijections.                                                     *)
(* ------------------------------------------------------------------------- *)

Definition bitset_def:
 bitset n = {i | ODD(n DIV (2 EXP i))}
End

Definition binarysum_def:
 binarysum s = nsum s (\i. 2 EXP i)
End

(* ------------------------------------------------------------------------- *)
(* Inverse property in one direction.                                        *)
(* ------------------------------------------------------------------------- *)

Theorem BITSET_BOUND_LEMMA:
 !n i. i IN (bitset n) ==> 2 EXP i <= n
Proof
 fs [bitset_def] >>
 metis_tac [LESS_DIV_EQ_ZERO, ODD, NOT_LESS_EQUAL]
QED

Theorem BITSET_BOUND_WEAK:
 !n i. i IN (bitset n) ==> i < n
Proof
 metis_tac [BITSET_BOUND_LEMMA, LESS_POW2_REFL, LESS_LESS_EQ_TRANS]
QED

Theorem FINITE_BITSET:
 !n. FINITE(bitset n)
Proof
 gen_tac >>
 match_mp_tac SUBSET_FINITE_I >>
 qexists_tac `{0 .. n}` >>
 fs [FINITE_NUMSEG, IN_NUMSEG, SUBSET_DEF] >>
 metis_tac [LESS_IMP_LESS_OR_EQ, BITSET_BOUND_WEAK]
QED

Theorem BITSET_0:
 bitset 0 = {}
Proof
 fs [bitset_def, EXTENSION, NOT_IN_EMPTY, ZERO_DIV, EXP_EQ_0]
QED

Theorem BITSET_STEP:
 (!n. bitset(2 * n) = IMAGE SUC (bitset n)) /\
 (!n. bitset(2 * n + 1) = 0 INSERT (IMAGE SUC (bitset n)))
Proof
 fs [bitset_def, GSPEC_ETA] >>
 conj_tac >> (
  gen_tac >>
  fs [EXTENSION] >>
  Induct_on `x` >- (
   fs [ODD_MULT, ODD_DOUBLE, GSYM ADD1]
  ) >>
  fs [EXP] >>
  subgoal `!m. m DIV (2 * 2 ** x) = m DIV 2 DIV 2 ** x` >- (
   match_mp_tac (GSYM DIV_DIV_DIV_MULT) >>
   fs []
  ) >>
  fs []
 )
QED

Theorem BINARYSUM_BITSET:
 !n. binarysum (bitset n) = n
Proof
 ONCE_REWRITE_TAC [EQ_SYM_EQ] >>
 fs [binarysum_def] >>
 match_mp_tac (SIMP_RULE std_ss [] (Q.ISPEC `\n. (n = nsum (bitset n) (\i. 2 ** i))` BINARY_INDUCT)) >>
 fs [BITSET_0, NSUM_CLAUSES, BITSET_STEP, NSUM_IMAGE,
     FINITE_BITSET, o_DEF, EXP, NSUM_LMUL]
QED

Theorem BITSET_EQ:
 !m n. bitset m = bitset n <=> m = n
Proof
 metis_tac [BINARYSUM_BITSET]
QED

Theorem BITSET_EQ_EMPTY:
 !n. bitset n = {} <=> n = 0
Proof
 metis_tac [BITSET_EQ, BITSET_0]
QED

(* ------------------------------------------------------------------------- *)
(* Inverse property in the other direction.                                  *)
(* ------------------------------------------------------------------------- *)

Theorem BINARYSUM_BOUND_LEMMA:
 !k s. (!i. i IN s ==> i < k) ==> nsum s (\i. 2 EXP i) < 2 EXP k
Proof
 Induct >- (
  (* simp loops due to GSYM NOT_EXISTS_THM *)
  fs [] >>
  SIMP_TAC pure_ss [GSYM NOT_EXISTS_THM, MEMBER_NOT_EMPTY] >>
  fs [NSUM_CLAUSES]
 ) >>
 rpt strip_tac >>
 subgoal `FINITE(s:num->bool)` >- (
  ASM_MESON_TAC [BOUNDED_FINITE, LE_LT]
 ) >>
 match_mp_tac LESS_EQ_LESS_TRANS >>
 qexists_tac `nsum (k INSERT (s DELETE k)) (\i. 2 EXP i)` >>
 conj_tac >| [
  match_mp_tac NSUM_SUBSET >>
  simp [FINITE_INSERT, FINITE_DELETE] >>
  SET_TAC [],

  fs [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] >>
  simp [EXP, ARITH_PROVE ``!a:num b. a + b < 2 * a <=> b < a``] >>
  FIRST_X_ASSUM match_mp_tac >>
  (* TODO: Failure of ASM_SET_TAC [] forces this laborious reasoning... *)
  rpt strip_tac >>
  Cases_on `i = k` >| [
   fs [],

   subgoal `i IN s` >- (
    fs []
   ) >>
   res_tac >>
   fs []
  ]
 ]
QED

Theorem BINARYSUM_DIV_DIVISIBLE:
 !s k. FINITE s /\ (!i. i IN s ==> k <= i)
       ==> nsum s (\i. 2 EXP i) = (2 EXP k) * nsum s (\i. 2 EXP (i - k))
Proof
 simp [cardinalTheory.CONJ_EQ_IMP, RIGHT_FORALL_IMP_THM] >>
 match_mp_tac (SIMP_RULE std_ss [] (Q.ISPEC `\s. !k. (!i. i IN s ==> k <= i) ==>
           nsum s (\i. 2 ** i) = 2 ** k * nsum s (\i. 2 ** (i - k))` FINITE_INDUCT)) >> (* TODO: Why so hard to match? *)
 rpt strip_tac >- (
  fs [NSUM_CLAUSES]
 ) >>
 asm_simp_tac std_ss [NSUM_CLAUSES] >>
 full_simp_tac std_ss [IN_INSERT, LEFT_ADD_DISTRIB] >>
 `2 ** e = 2 ** k * 2 ** (e - k)` suffices_by (
  rpt strip_tac >>
  fs [EQ_ADD_LCANCEL]
 ) >>
 metis_tac [GSYM EXP_ADD, ARITH_PROVE ``!i k:num. i <= k ==> i + (k - i) = k``]
QED

Theorem BINARYSUM_DIV:
 !k s. FINITE s
       ==> (nsum s (\j. 2 EXP j)) DIV (2 EXP k) =
           nsum s (\j. if j < k then 0 else 2 EXP (j - k))
Proof
 rpt strip_tac >>
 match_mp_tac EQ_TRANS >>
 qexists_tac `(nsum {i | i < k /\ i IN s} (\j. 2 EXP j) +
              nsum {i | k <= i /\ i IN s} (\j. 2 EXP j)) DIV (2 EXP k)` >>
 conj_tac >- (
  AP_THM_TAC >>
  AP_TERM_TAC >>
  CONV_TAC SYM_CONV >>
  match_mp_tac NSUM_UNION_EQ >>
  fs [EXTENSION, IN_INTER, IN_UNION, NOT_IN_EMPTY] >>
  conj_tac >> (
   Q.X_GEN_TAC `i:num` >>
   Q.ASM_CASES_TAC `(i:num) IN s` >> (
    ASM_REWRITE_TAC [] >>
    ARITH_TAC
   )
  )
 ) >>
 match_mp_tac DIV_UNIQ >>
 qexists_tac `nsum {i | i < k /\ i IN s} (\j. 2 EXP j)` >>
 simp [BINARYSUM_BOUND_LEMMA] >>
 rewrite_tac [ARITH_PROVE ``!a x y. a + x:num = y + a <=> x = y``] >>
 match_mp_tac EQ_TRANS >>
 qexists_tac `2 EXP k * nsum {i | k <= i /\ i IN s} (\i. 2 EXP (i - k))` >>
 conj_tac >| [
  match_mp_tac BINARYSUM_DIV_DIVISIBLE >>
  simp [] >>
  match_mp_tac SUBSET_FINITE_I >>
  qexists_tac `s:num->bool` >>
  fs [SUBSET_DEF],

  GEN_REWRITE_TAC RAND_CONV empty_rewrites [MULT_SYM] >>
  fs [EQ_MULT_LCANCEL, EXP_EQ_0] >>
  ONCE_REWRITE_TAC [GSYM NSUM_SUPPORT] >>
  fs [support, NEUTRAL_ADD, EXP_EQ_0] >>
  rewrite_tac [ARITH_PROVE ``!p q:num. (if p then 0 else q) = 0 <=> ~p ==> q = 0``] >>
  fs [EXP_EQ_0, NOT_LESS, cardinalTheory.CONJ_ACI] >>
  match_mp_tac NSUM_EQ >>
  simp [ARITH_PROVE ``!k j. k <= j:num ==> ~(j < k)``]
 ]
QED

Theorem BITSET_BINARYSUM:
 !s. FINITE s ==> bitset (binarysum s) = s
Proof
 rpt strip_tac >>
 rewrite_tac [bitset_def, binarysum_def, EXTENSION] >>
 Q.X_GEN_TAC `i:num` >>
 fs [BINARYSUM_DIV] >>
 Cases_on `(i:num) IN s` >> (
  ASM_REWRITE_TAC []
 ) >| [
  FIRST_ASSUM (SUBST1_TAC o MATCH_MP (SIMP_PROVE (std_ss++pred_setLib.PRED_SET_ss) [] ``!i s. i IN s ==> s = i INSERT (s DELETE i)``)) >>
  fs [NSUM_CLAUSES, FINITE_DELETE, IN_DELETE] >>
  fs [ODD_ADD] >>
  rewrite_tac [GSYM EVEN_ODD] >>
  match_mp_tac EVEN_NSUM >>
  fs [] >>
  rpt strip_tac >>
  COND_CASES_TAC >| [
   fs [],

   match_mp_tac EVEN_EXP >>
   fs []
  ],

  rewrite_tac [GSYM EVEN_ODD] >>
  match_mp_tac EVEN_NSUM >>
  fs [] >>
  rpt strip_tac >>
  COND_CASES_TAC >| [
   fs [],

   match_mp_tac EVEN_EXP >>
   fs [] >>
   subgoal `i' <> i` >- (
    ASM_SET_TAC []
   ) >>
   fs []
  ]
 ]
QED

(* ------------------------------------------------------------------------- *)
(* Also, bijections between restricted segments.                             *)
(* ------------------------------------------------------------------------- *)

Theorem BINARYSUM_BOUND:
 !k s. (!i. i IN s ==> i < k) ==> binarysum s < 2 EXP k
Proof
 rewrite_tac [BINARYSUM_BOUND_LEMMA, binarysum_def]
QED

Theorem BITSET_BOUND:
 !n i k. n < 2 EXP k /\ i IN bitset n ==> i < k
Proof
 rpt strip_tac >>
 Q.SUBGOAL_THEN `2 EXP i < 2 EXP k` mp_tac >- (
  metis_tac [BITSET_BOUND_LEMMA, LESS_EQ_LESS_TRANS]
 ) >>
 fs []
QED

Theorem BITSET_BOUND_EQ:
 !n k. n < 2 EXP k <=> (!i. i IN bitset n ==> i < k)
Proof
 metis_tac [BINARYSUM_BOUND, BITSET_BOUND, BINARYSUM_BITSET]
QED

Theorem BINARYSUM_BOUND_EQ:
 !s k. FINITE s ==> (binarysum s < 2 EXP k <=> (!i. i IN s ==> i < k))
Proof
 metis_tac [BINARYSUM_BOUND, BITSET_BOUND, BITSET_BINARYSUM]
QED

val _ = export_theory ();
val _ = html_theory "binary_expansion";
