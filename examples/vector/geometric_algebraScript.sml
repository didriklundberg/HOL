(* ========================================================================= *)
(* Geometric algebra G(P,Q,R) is formalized with the multivector structure   *)
(* (P,Q,R)multivector, which can formulate positive definite, negative       *)
(* definite and zero quadratic forms.                                        *)
(*                                                                           *)
(*        (c) Copyright, Capital Normal University, China, 2018.             *)
(*     Authors: Liming Li, Zhiping Shi, Yong Guan, Guohui Wang, Sha Ma.      *)
(* ========================================================================= *)

(* TODO: Clean-up *)
open HolKernel Parse boolLib bossLib;

open arithmeticTheory combinTheory pred_setTheory pairTheory PairedLambda
     pred_setLib fcpTheory fcpLib tautLib numLib listTheory rich_listTheory;

open realTheory realLib iterateTheory real_sigmaTheory RealArith mesonLib;

open hurdUtils vectorTheory;

open cliffordTheory;

val _ = new_theory "geometric_algebra";

(* ------------------------------------------------------------------------- *)
(* Add some theorems to cliffordScript.sml                                   *)
(* ------------------------------------------------------------------------- *)

Theorem GEOM_MBASIS_LID:
 !x. mbasis{} * x = x
Proof
(*
  MATCH_MP_TAC MBASIS_EXTENSION THEN SIMP_TAC[GEOM_RMUL; GEOM_RADD] THEN
  SIMP_TAC[GEOM_MBASIS; DIFF_EMPTY; EMPTY_DIFF; UNION_EMPTY; EMPTY_SUBSET] THEN
  REWRITE_TAC[SET_RULE `{i,j | i IN {} /\ j IN s /\ i:num > j} = {}`] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow; REAL_MUL_LID; VECTOR_MUL_LID]);;
*)
QED


val _ = export_theory ();
val _ = html_theory "geometric_algebra";
