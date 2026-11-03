(* ------------------------------------------------------------------------
   The PMP check of the RISC-V L3 model (pmpCheck, P §3.7 p.70-74;
   design-privileged.md §5.3-5.4, [D53]) as the isolation theorems use it:

   - the lowest-numbered entry that matches decides (pmpCheck_first,
     pmpCheck_byte_first, P §3.7.1.3 p.73);
   - an access that the check allows is allowed byte by byte
     (pmpCheck_byte) and for every weaker kind (pmpCheck_RW,
     pmp_legal_write_read);
   - the check is a function of the 18 PMP CSR words of the hart, pmpcfg0,
     pmpcfg2 and pmpaddr0-15 (pmpCheck_words, with the word-level
     pmp_check), which is the form in which HolBA's contracts state them;
   - a byte that U-mode may access lies in the region of the
     lowest-numbered entry that matches it, and that entry allows the
     access (pmpCheck_User_entry, pmp_check_User_byte); when every entry is
     OFF or NAPOT, that region is the NAPOT region of the entry's pmpaddr
     word (pmp_check_User_napot, pmpCheck_User_napot).
   ------------------------------------------------------------------------ *)
Theory riscv_pmp
Ancestors
  rich_list riscv riscv_footprint
Libs
  wordsLib blastLib

val _ = ParseExtras.temp_loose_equality ()
val _ = wordsLib.guess_lengths ()

(* ------------------------------------------------------------------------
   1. The chain of entries
   ------------------------------------------------------------------------ *)

(* The verdict of the first entry that has one, and d if none has: the
   shape of pmpCheck, which lets the verdicts of the 16 entries and chains
   them through IS_SOME and THE. *)
Definition pmp_first_def:
  (pmp_first [] (d : bool) = d) /\
  (pmp_first ((e : bool option) :: es) d =
     if IS_SOME e then THE e else pmp_first es d)
End

val GENLIST16 = EVAL ``GENLIST (f : num -> 'a) 16``

Theorem pmpCheck_first:
  !a n kind p s.
    pmpCheck (a, n, kind, p) s =
    pmp_first
      (GENLIST (\i. pmpEntryCheck (n2w i, a, a + n2w (n - 1), kind, p) s) 16)
      (p = Machine)
Proof
  simp_tac std_ss [pmpCheck_def, LET_THM, GENLIST16, pmp_first_def]
QED

(* pmp_first as the rule of P §3.7.1.3 p.73: some entry has a verdict and
   no lower one has, and the verdict is T; or no entry has one and d. *)
Theorem pmp_first_GENLIST:
  !n f d.
    pmp_first (GENLIST f n) d <=>
    (?i. i < n /\ IS_SOME (f i) /\ (!j. j < i ==> (f j = NONE)) /\ THE (f i)) \/
    (!i. i < n ==> (f i = NONE)) /\ d
Proof
  Induct
  >- simp [pmp_first_def]
  \\ rpt gen_tac
  \\ simp_tac std_ss [GENLIST_CONS, pmp_first_def]
  \\ Cases_on `f 0`
  \\ asm_simp_tac (srw_ss()) []
  >- (eq_tac
      \\ rpt strip_tac
      >- (disj1_tac \\ qexists_tac `SUC i` \\ simp [] \\ Cases \\ simp [])
      >- (disj2_tac \\ simp [] \\ Cases \\ simp [])
      >- (disj1_tac
          \\ Cases_on `i`
          \\ gvs []
          \\ qexists_tac `n'`
          \\ simp []
          \\ rpt strip_tac
          \\ `SUC j < SUC n'` by simp []
          \\ metis_tac [])
      \\ disj2_tac
      \\ simp []
      \\ rpt strip_tac
      \\ `SUC i < SUC n` by simp []
      \\ metis_tac [])
  \\ eq_tac
  \\ rpt strip_tac
  >- (disj1_tac \\ qexists_tac `0` \\ simp [])
  >- (Cases_on `i`
      \\ gvs []
      \\ `0 < SUC n'` by simp []
      \\ metis_tac [optionTheory.NOT_SOME_NONE])
  \\ `0 < SUC n` by simp []
  \\ metis_tac [optionTheory.NOT_SOME_NONE]
QED

(* One verdict is below another if a missing verdict stays missing and a
   T stays T; an F may become anything. *)
Definition ent_le_def:
  ent_le (e : bool option) e' <=>
    ((e = NONE) ==> (e' = NONE)) /\ ((e = SOME T) ==> (e' = SOME T))
End

Theorem pmp_first_mono:
  !es es' d d'.
    LIST_REL ent_le es es' /\ (d ==> d') /\ pmp_first es d ==> pmp_first es' d'
Proof
  Induct
  >- simp [pmp_first_def]
  \\ gen_tac
  \\ Cases
  \\ simp [pmp_first_def]
  \\ rpt strip_tac
  \\ Cases_on `h`
  \\ fs [ent_le_def]
  >- (first_x_assum irule \\ metis_tac [])
  \\ Cases_on `x`
  \\ fs []
QED

(* ------------------------------------------------------------------------
   2. Sub-accesses and weaker kinds
   ------------------------------------------------------------------------ *)

(* An entry gives a sub-access of the bytes a .. l the same verdict as the
   access, if the access has none or T (P §3.7.1.3 p.73: an entry that
   matches all bytes of an access matches all bytes of a part of it). *)
Theorem pmpEntryCheck_sub:
  !i a l a' l' kind p s.
    a <=+ a' /\ a' <=+ l' /\ l' <=+ l ==>
    ent_le (pmpEntryCheck (i, a, l, kind, p) s)
           (pmpEntryCheck (i, a', l', kind, p) s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [pmpEntryCheck_def, ent_le_def, LET_THM]
  \\ Cases_on `pmpRegion i s`
  \\ simp_tac (srw_ss()) []
  \\ PairCases_on `x`
  \\ simp_tac (srw_ss()) []
  \\ rpt (pop_assum mp_tac)
  \\ rw [wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_NOT_LOWER_EQUAL]
  \\ metis_tac [wordsTheory.WORD_LOWER_EQ_TRANS,
                wordsTheory.WORD_LOWER_EQ_LOWER_TRANS,
                wordsTheory.WORD_LOWER_LOWER_EQ_TRANS,
                wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_NOT_LOWER_EQUAL]
QED

(* An entry gives the same access of a weaker kind a verdict at least as
   permissive. *)
Theorem pmpEntryCheck_kind:
  !i a l kind kind' p s.
    (pmpPermits (pmpcfg_ent i s, kind) ==> pmpPermits (pmpcfg_ent i s, kind')) ==>
    ent_le (pmpEntryCheck (i, a, l, kind, p) s)
           (pmpEntryCheck (i, a, l, kind', p) s)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [pmpEntryCheck_def, ent_le_def, LET_THM]
  \\ Cases_on `pmpRegion i s`
  \\ simp_tac (srw_ss()) []
  \\ PairCases_on `x`
  \\ rw []
  \\ fs []
QED

Theorem pmpCheck_sub:
  !a n a' n' kind p s.
    pmpCheck (a, n, kind, p) s /\
    a <=+ a' /\ a' <=+ a' + n2w (n' - 1) /\ a' + n2w (n' - 1) <=+ a + n2w (n - 1) ==>
    pmpCheck (a', n', kind, p) s
Proof
  rewrite_tac [pmpCheck_first]
  \\ rpt strip_tac
  \\ irule pmp_first_mono
  \\ first_assum (irule_at Any)
  \\ simp [LIST_REL_GENLIST]
  \\ rpt strip_tac
  \\ irule pmpEntryCheck_sub
  \\ simp []
QED

Theorem pmpCheck_kind:
  !a n kind kind' p s.
    pmpCheck (a, n, kind, p) s /\
    (!i. pmpPermits (pmpcfg_ent i s, kind) ==> pmpPermits (pmpcfg_ent i s, kind')) ==>
    pmpCheck (a, n, kind', p) s
Proof
  rewrite_tac [pmpCheck_first]
  \\ rpt strip_tac
  \\ irule pmp_first_mono
  \\ first_assum (irule_at Any)
  \\ simp [LIST_REL_GENLIST]
  \\ rpt strip_tac
  \\ irule pmpEntryCheck_kind
  \\ simp []
QED

(* The bytes of an aligned access of 1, 2, 4 or 8 bytes are a .. a + n - 1
   without wrapping round. *)
Theorem in_range_bounds:
  !a n x.
    ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\ (w2n a MOD n = 0) /\
    in_range a n x ==>
    a <=+ x /\ x <=+ a + n2w (n - 1)
Proof
  rpt gen_tac
  \\ PURE_REWRITE_TAC [in_range_def]
  \\ strip_tac
  \\ `x = a + n2w (w2n (x - a))` by simp_tac (srw_ss()) [wordsTheory.n2w_w2n]
  \\ qabbrev_tac `k = w2n (x - a)`
  \\ qpat_x_assum `x = _` SUBST1_TAC
  \\ qpat_x_assum `Abbrev _` kall_tac
  \\ `(k = 0) \/ (k = 1) \/ (k = 2) \/ (k = 3) \/ (k = 4) \/ (k = 5) \/
      (k = 6) \/ (k = 7)` by (rfs [] \\ decide_tac)
  \\ rfs []
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs [align_tests]
  \\ blastLib.FULL_BBLAST_TAC
QED

(* An access that PMP allows is allowed for each of its bytes (P §3.7.1.3
   p.73: the entry that decides an access matches all of its bytes, and an
   entry below it that matches none of them matches none of its bytes). *)
Theorem pmpCheck_byte:
  !a n kind p s x.
    pmpCheck (a, n, kind, p) s /\ ((n = 1) \/ (n = 2) \/ (n = 4) \/ (n = 8)) /\
    (w2n a MOD n = 0) /\ in_range a n x ==>
    pmpCheck (x, 1, kind, p) s
Proof
  rpt strip_tac
  \\ `a <=+ x /\ x <=+ a + n2w (n - 1)` by metis_tac [in_range_bounds]
  \\ match_mp_tac (Q.SPECL [`a`, `n`] pmpCheck_sub)
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ fs [wordsTheory.WORD_LOWER_EQ_REFL]
QED

(* An AMO needs R and W (P §3.7.1 p.72), so it is allowed only where a
   load and a store are. *)
Theorem pmpCheck_RW:
  !a n p s.
    pmpCheck (a, n, PMP_ReadWrite, p) s ==>
    pmpCheck (a, n, PMP_Read, p) s /\ pmpCheck (a, n, PMP_Write, p) s
Proof
  rpt strip_tac
  \\ irule (Q.SPECL [`a`, `n`, `PMP_ReadWrite`] pmpCheck_kind)
  \\ asm_simp_tac (srw_ss()) [pmpPermits_def]
QED

(* ------------------------------------------------------------------------
   3. The check as a function of the PMP CSR words

   pmp_check (cfg0, cfg2, addr) is pmpCheck written over pmpcfg0, pmpcfg2
   and the 16 pmpaddr words alone (addr i is pmpaddr<i>): the entry
   configuration byte i is byte i mod 8 of pmpcfg0 (entries 0-7) or pmpcfg2
   (entries 8-15) (P §3.7.1 Figure 31 p.71), with L = bit 7, A = bits 4:3,
   X = bit 2, W = bit 1, R = bit 0 (Figure 34 p.72), and the regions are
   those of Table 24 p.72 with grain 0 ([D48]).
   ------------------------------------------------------------------------ *)

Definition pmp_cfg_byte_def:
  pmp_cfg_byte (cfg0 : word64) (cfg2 : word64) (i : word4) : word8 =
    (7 >< 0) ((if word_bit 3 i then cfg2 else cfg0) >>> (8 * w2n ((2 >< 0) i : word3)))
End

(* The bytes lo .. hi - 1 that entry i matches: OFF none, TOR from
   pmpaddr(i-1) * 4 (0 for entry 0) to pmpaddr(i) * 4, NA4 four bytes,
   NAPOT 2^(t+3) bytes for t trailing ones (P §3.7.1.1 p.72-73). *)
Definition pmp_region_def:
  pmp_region (cfg0 : word64, cfg2 : word64, addr : word4 -> word64) (i : word4) =
    let c = pmp_cfg_byte cfg0 cfg2 i; y = addr i in
    if (4 >< 3) c = (0w : word2) then NONE
    else if (4 >< 3) c = (1w : word2) then
      (let lo = (if i = 0w then 0w else addr (i - 1w) << 2); hi = y << 2 in
       if lo <+ hi then SOME (lo, hi) else NONE)
    else if (4 >< 3) c = (2w : word2) then SOME (y << 2, (y << 2) + 4w)
    else
      (let m = y ?? (y + 1w); lo = (y && ~m) << 2 in
       SOME (lo, lo + ((m + 1w) << 2)))
End

Definition pmp_perm_def:
  pmp_perm (c : word8) kind =
    case kind of
      PMP_Read => word_bit 0 c
    | PMP_Write => word_bit 1 c
    | PMP_ReadWrite => word_bit 0 c /\ word_bit 1 c
    | PMP_Execute => word_bit 2 c
End

Definition pmp_entry_def:
  pmp_entry (cfg0, cfg2, addr) (i : word4) (a : word64, last : word64, kind, p) =
    case pmp_region (cfg0, cfg2, addr) i of
      NONE => NONE
    | SOME (lo, hi) =>
        if last <+ lo \/ hi <=+ a then NONE
        else if lo <=+ a /\ last <+ hi then
          SOME ((p = Machine) /\ ~word_bit 7 (pmp_cfg_byte cfg0 cfg2 i) \/
                pmp_perm (pmp_cfg_byte cfg0 cfg2 i) kind)
        else SOME F
End

Definition pmp_check_def:
  pmp_check (cfg0, cfg2, addr) (a : word64, n : num, kind, p) =
    pmp_first
      (GENLIST (\i. pmp_entry (cfg0, cfg2, addr) (n2w i)
                              (a, a + n2w (n - 1), kind, p)) 16)
      (p = Machine)
End

(* pmpaddr<i> of a set of machine-level CSRs *)
Definition pmpaddr_of_def:
  pmpaddr_of (m : MachineCSR) (i : word4) =
    EL (w2n i)
       [m.pmpaddr0; m.pmpaddr1; m.pmpaddr2; m.pmpaddr3; m.pmpaddr4;
        m.pmpaddr5; m.pmpaddr6; m.pmpaddr7; m.pmpaddr8; m.pmpaddr9;
        m.pmpaddr10; m.pmpaddr11; m.pmpaddr12; m.pmpaddr13; m.pmpaddr14;
        m.pmpaddr15]
End

Theorem word4_cases[local]:
  !i : word4.
    (i = 0w) \/ (i = 1w) \/ (i = 2w) \/ (i = 3w) \/ (i = 4w) \/ (i = 5w) \/
    (i = 6w) \/ (i = 7w) \/ (i = 8w) \/ (i = 9w) \/ (i = 10w) \/ (i = 11w) \/
    (i = 12w) \/ (i = 13w) \/ (i = 14w) \/ (i = 15w)
Proof
  blastLib.BBLAST_TAC
QED

Theorem pmpaddr_of:
  !i s. pmpaddr i s = pmpaddr_of (s.c_MCSR s.procID) i
Proof
  rpt gen_tac
  \\ strip_assume_tac (SPEC ``i : word4`` word4_cases)
  \\ asm_simp_tac (srw_ss()) [pmpaddr_def, pmpaddr_of_def, MCSR_def]
QED

Theorem pmpcfg_ent_byte:
  !i s.
    pmpcfg_ent i s =
    rec'pmpcfg (pmp_cfg_byte (s.c_MCSR s.procID).pmpcfg0
                             (s.c_MCSR s.procID).pmpcfg2 i)
Proof
  simp [pmpcfg_ent_def, pmp_cfg_byte_def, MCSR_def]
QED

Theorem pmpRegion_words:
  !i s.
    pmpRegion i s =
    pmp_region ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
                \j. pmpaddr j s) i
Proof
  rpt gen_tac
  \\ simp_tac std_ss [pmpRegion_def, pmp_region_def, LET_THM, pmpcfg_ent_byte]
  \\ qabbrev_tac
       `c = pmp_cfg_byte (s.c_MCSR s.procID).pmpcfg0 (s.c_MCSR s.procID).pmpcfg2 i`
  \\ simp_tac (srw_ss()) [rec'pmpcfg_def]
  \\ wordsLib.Cases_on_word_value `(4 >< 3) c : word2`
  \\ simp_tac (srw_ss()) []
QED

Theorem pmpEntryCheck_words:
  !i a l kind p s.
    pmpEntryCheck (i, a, l, kind, p) s =
    pmp_entry ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
               \j. pmpaddr j s) i (a, l, kind, p)
Proof
  rpt gen_tac
  \\ simp_tac std_ss [pmpEntryCheck_def, pmp_entry_def, LET_THM,
                      pmpRegion_words]
  \\ CASE_TAC
  \\ simp_tac std_ss []
  \\ CASE_TAC
  \\ simp_tac (srw_ss()) [pmpcfg_ent_byte, rec'pmpcfg_def, pmpPermits_def,
                          pmp_perm_def]
  \\ Cases_on `kind`
  \\ simp_tac (srw_ss()) []
QED

(* pmpCheck is the word-level check of the hart's 18 PMP CSRs. *)
Theorem pmpCheck_words:
  !a n kind p s.
    pmpCheck (a, n, kind, p) s =
    pmp_check ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
               \i. pmpaddr i s) (a, n, kind, p)
Proof
  simp_tac std_ss [pmpCheck_first, pmp_check_def, pmpEntryCheck_words]
QED

Theorem pmpCheck_MCSR:
  !acc s.
    pmpCheck acc s =
    pmp_check ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
               pmpaddr_of (s.c_MCSR s.procID)) acc
Proof
  rpt gen_tac
  \\ PairCases_on `acc`
  \\ simp_tac std_ss [pmpCheck_words, pmpaddr_of]
  \\ CONV_TAC (DEPTH_CONV ETA_CONV)
  \\ REFL_TAC
QED

(* So two states whose current harts have the same PMP CSRs check every
   access alike. *)
Theorem pmpCheck_eq:
  !acc s t.
    ((t.c_MCSR t.procID).pmpcfg0 = (s.c_MCSR s.procID).pmpcfg0) /\
    ((t.c_MCSR t.procID).pmpcfg2 = (s.c_MCSR s.procID).pmpcfg2) /\
    (!i. pmpaddr i t = pmpaddr i s) ==>
    (pmpCheck acc t = pmpCheck acc s)
Proof
  rpt strip_tac
  \\ PairCases_on `acc`
  \\ asm_simp_tac std_ss [pmpCheck_words]
QED

Theorem pmpCheck_eq_MCSR:
  !acc s t.
    (t.procID = s.procID) /\ (t.c_MCSR = s.c_MCSR) ==>
    (pmpCheck acc t = pmpCheck acc s)
Proof
  rpt strip_tac
  \\ irule pmpCheck_eq
  \\ asm_simp_tac std_ss [pmpaddr_of]
QED

(* ------------------------------------------------------------------------
   4. One byte: the lowest-numbered entry that matches decides
   ------------------------------------------------------------------------ *)

(* Entry i matches byte x. *)
Definition pmp_match_def:
  pmp_match s (i : word4) (x : word64) <=>
    ?lo hi. (pmpRegion i s = SOME (lo, hi)) /\ lo <=+ x /\ x <+ hi
End

(* P §3.7.1.3 p.73 for a 1-byte access, which no entry can match only in
   part: the access is allowed iff the lowest-numbered entry that matches
   it allows it, M-mode passing an unlocked entry, and if no entry matches,
   iff the privilege is M. *)
Theorem pmpCheck_byte_first:
  !x kind p s.
    pmpCheck (x, 1, kind, p) s <=>
    (?i. i < 16 /\ pmp_match s (n2w i) x /\
         (!j. j < i ==> ~pmp_match s (n2w j) x) /\
         ((p = Machine) /\ ~(pmpcfg_ent (n2w i) s).L \/
          pmpPermits (pmpcfg_ent (n2w i) s, kind))) \/
    (!i. i < 16 ==> ~pmp_match s (n2w i) x) /\ (p = Machine)
Proof
  rpt gen_tac
  \\ `!i. pmpEntryCheck (i, x, x, kind, p) s =
          if pmp_match s i x then
            SOME ((p = Machine) /\ ~(pmpcfg_ent i s).L \/
                  pmpPermits (pmpcfg_ent i s, kind))
          else NONE`
     by (gen_tac
         \\ simp_tac std_ss [pmpEntryCheck_def, pmp_match_def, LET_THM]
         \\ Cases_on `pmpRegion i s`
         \\ simp_tac (srw_ss()) []
         \\ PairCases_on `x'`
         \\ simp_tac (srw_ss()) []
         \\ rw []
         \\ metis_tac [wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_NOT_LOWER_EQUAL,
                       wordsTheory.WORD_LOWER_EQ_LOWER_TRANS,
                       wordsTheory.WORD_LOWER_LOWER_EQ_TRANS,
                       wordsTheory.WORD_LOWER_REFL])
  \\ asm_simp_tac std_ss [pmpCheck_first, pmp_first_GENLIST, wordsTheory.WORD_ADD_0]
  \\ simp_tac std_ss [COND_RAND, COND_RATOR, optionTheory.IS_SOME_DEF,
                      optionTheory.THE_DEF, optionTheory.NOT_SOME_NONE]
QED

(* ------------------------------------------------------------------------
   5. Legal configurations

   No entry has W = 1 with R = 0: legalize_pmpcfg_byte stores such a write
   as R = W = X = 0 ([D49]), so every pmpcfg value that M-mode writes, and
   the reset value 0, are legal (legalize_pmpcfg_legal).  With a legal
   configuration a writable byte is readable.
   ------------------------------------------------------------------------ *)

Definition pmp_legal_def:
  pmp_legal (cfg0 : word64) (cfg2 : word64) <=>
    !i. word_bit 1 (pmp_cfg_byte cfg0 cfg2 i) ==>
        word_bit 0 (pmp_cfg_byte cfg0 cfg2 i)
End

Theorem pmp_legal_bits:
  !cfg0 cfg2.
    pmp_legal cfg0 cfg2 <=>
    (cfg0 >>> 1 && ~cfg0 && 0x0101010101010101w = 0w) /\
    (cfg2 >>> 1 && ~cfg2 && 0x0101010101010101w = 0w)
Proof
  rpt gen_tac
  \\ simp_tac std_ss [pmp_legal_def]
  \\ eq_tac
  >- (strip_tac
      \\ `!i. MEM i [0w; 1w; 2w; 3w; 4w; 5w; 6w; 7w; 8w; 9w; 10w; 11w; 12w;
                     13w; 14w; 15w : word4] ==>
              word_bit 1 (pmp_cfg_byte cfg0 cfg2 i) ==>
              word_bit 0 (pmp_cfg_byte cfg0 cfg2 i)`
         by metis_tac []
      \\ pop_assum mp_tac
      \\ rpt (pop_assum kall_tac)
      \\ simp_tac (srw_ss()) [pmp_cfg_byte_def, DISJ_IMP_THM, FORALL_AND_THM]
      \\ blastLib.BBLAST_TAC)
  \\ rpt strip_tac
  \\ strip_assume_tac (SPEC ``i : word4`` word4_cases)
  \\ rpt (qpat_x_assum `word_bit _ _` mp_tac)
  \\ rpt (qpat_x_assum `_ = 0w` mp_tac)
  \\ asm_simp_tac (srw_ss()) [pmp_cfg_byte_def]
  \\ blastLib.BBLAST_TAC
QED

Theorem pmp_legal_write_read:
  !a n p s.
    pmp_legal (s.c_MCSR s.procID).pmpcfg0 (s.c_MCSR s.procID).pmpcfg2 /\
    pmpCheck (a, n, PMP_Write, p) s ==>
    pmpCheck (a, n, PMP_Read, p) s
Proof
  rpt strip_tac
  \\ irule (Q.SPECL [`a`, `n`, `PMP_Write`] pmpCheck_kind)
  \\ fs [pmpPermits_def, pmpcfg_ent_byte, rec'pmpcfg_def, pmp_legal_def]
QED

Theorem legalize_pmpcfg_byte_legal[local]:
  !b c.
    (word_bit 1 c ==> word_bit 0 c) ==>
    word_bit 1 (reg'pmpcfg (legalize_pmpcfg_byte (b, rec'pmpcfg c))) ==>
    word_bit 0 (reg'pmpcfg (legalize_pmpcfg_byte (b, rec'pmpcfg c)))
Proof
  rpt gen_tac
  \\ strip_tac
  \\ simp_tac std_ss [legalize_pmpcfg_byte_def, LET_THM]
  \\ rw []
  \\ fs ([rec'pmpcfg_def, reg'pmpcfg_def] @
         TypeBase.updates_of ``:pmpcfg`` @ TypeBase.accessors_of ``:pmpcfg``)
  \\ rpt (pop_assum mp_tac)
  \\ blastLib.BBLAST_TAC
QED

(* Every value that a write of pmpcfg0 or pmpcfg2 stores is legal if the
   old one was: a locked byte keeps its old value, and the others are
   legalised. *)
Theorem legalize_pmpcfg_legal:
  !v old.
    (old >>> 1 && ~old && 0x0101010101010101w = 0w) ==>
    (legalize_pmpcfg (v, old) >>> 1 && ~legalize_pmpcfg (v, old) &&
     0x0101010101010101w = 0w)
Proof
  rpt strip_tac
  \\ simp_tac std_ss [legalize_pmpcfg_def]
  \\ (fn (g as (_, w)) =>
        let
          fun is_reg t =
            is_comb t andalso
            (case Lib.total (fst o dest_const o rator) t of
               SOME "reg'pmpcfg" => true
             | _ => false)
          val ts = Lib.op_mk_set aconv (find_terms is_reg w)
          fun one t =
            sg `word_bit 1 ^t ==> word_bit 0 ^t`
            >- (match_mp_tac legalize_pmpcfg_byte_legal
                \\ qpat_x_assum `_ = 0w` mp_tac
                \\ blastLib.BBLAST_TAC)
        in
          (MAP_EVERY one ts
           \\ qpat_x_assum `_ = 0w` kall_tac
           \\ rpt (pop_assum mp_tac)
           \\ MAP_EVERY (fn t => SPEC_TAC (t, genvar ``:word8``)) ts) g
        end)
  \\ blastLib.BBLAST_TAC
QED

(* ------------------------------------------------------------------------
   6. A byte that U-mode may access, and entries that are OFF or NAPOT

   For a 1-byte access by U-mode the check is the permission of the
   lowest-numbered entry that matches the byte, and there must be such an
   entry (P §3.7.1.3 p.73).  An entry is OFF or NAPOT when the two bits of
   its A field are equal (Table 23 p.72); an OFF entry matches no byte, and
   a NAPOT entry matches the 2^(t+3) bytes that its pmpaddr word encodes
   with t trailing ones (Table 24 p.72).  So when every entry is OFF or
   NAPOT, a byte that U-mode may access lies in the NAPOT region of an
   entry that allows the access, and no lower entry matches it.  The
   theorems are stated for the state (pmpCheck, pmpRegion) and for the
   words (pmp_check, pmp_region) as pmpCheck_words relates them.
   ------------------------------------------------------------------------ *)

(* The entry that decides a 1-byte access by U-mode matches the byte and
   allows the access *)
Theorem pmpCheck_User_entry:
  !x kind s.
    pmpCheck (x, 1, kind, User) s ==>
    ?i lo hi. i < 16 /\ (pmpRegion (n2w i) s = SOME (lo, hi)) /\ lo <=+ x /\ x <+ hi /\
              pmpPermits (pmpcfg_ent (n2w i) s, kind) /\
              !j. j < i ==> ~pmp_match s (n2w j) x
Proof
  rw [pmpCheck_byte_first, pmp_match_def]
  \\ metis_tac []
QED

(* Entries 8-15 are configured by pmpcfg2: they are OFF when it is 0 *)
Theorem pmpRegion_pmpcfg2_off:
  !k s.
    8 <= k /\ k < 16 /\ ((s.c_MCSR s.procID).pmpcfg2 = 0w) ==>
    (pmpRegion (n2w k) s = NONE)
Proof
  rpt strip_tac
  \\ `(k = 8) \/ (k = 9) \/ (k = 10) \/ (k = 11) \/ (k = 12) \/ (k = 13) \/
      (k = 14) \/ (k = 15)` by decide_tac
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ asm_simp_tac (srw_ss()) [pmpRegion_def, pmpcfg_ent_byte, pmp_cfg_byte_def,
                              rec'pmpcfg_def, LET_THM]
QED

(* So with pmpcfg2 = 0 the deciding entry is one of entries 0-7 *)
Theorem pmpCheck_User_low:
  !x kind s.
    ((s.c_MCSR s.procID).pmpcfg2 = 0w) /\ pmpCheck (x, 1, kind, User) s ==>
    ?i lo hi. i < 8 /\ (pmpRegion (n2w i) s = SOME (lo, hi)) /\ lo <=+ x /\ x <+ hi /\
              pmpPermits (pmpcfg_ent (n2w i) s, kind) /\
              !j. j < i ==> ~pmp_match s (n2w j) x
Proof
  rpt strip_tac
  \\ drule pmpCheck_User_entry
  \\ strip_tac
  \\ Cases_on `i < 8`
  >- metis_tac []
  \\ `pmpRegion (n2w i) s = NONE` by (irule pmpRegion_pmpcfg2_off \\ simp [])
  \\ fs []
QED

(* Entry i of the PMP CSR words w = (pmpcfg0, pmpcfg2, addr) matches byte
   x: the word-level pmp_match *)
Definition pmp_match_w_def:
  pmp_match_w (w : word64 # word64 # (word4 -> word64)) (i : word4) (x : word64) <=>
    ?lo hi. (pmp_region w i = SOME (lo, hi)) /\ lo <=+ x /\ x <+ hi
End

Theorem pmp_match_words:
  !i x s.
    pmp_match s i x <=>
    pmp_match_w ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
                 \j. pmpaddr j s) i x
Proof
  simp_tac std_ss [pmp_match_def, pmp_match_w_def, pmpRegion_words]
QED

(* For a 1-byte access by U-mode an entry has a verdict iff it matches the
   byte, and the verdict is its permission for the kind *)
Theorem pmp_entry_User_byte:
  !w i x kind.
    pmp_entry w i (x, x, kind, User) =
    if pmp_match_w w i x then
      SOME (pmp_perm (pmp_cfg_byte (FST w) (FST (SND w)) i) kind)
    else NONE
Proof
  rpt gen_tac
  \\ PairCases_on `w`
  \\ simp_tac std_ss [pmp_entry_def, pmp_match_w_def]
  \\ Cases_on `pmp_region (w0, w1, w2) i`
  \\ simp_tac (srw_ss()) []
  \\ PairCases_on `x'`
  \\ simp_tac (srw_ss()) []
  \\ rw []
  \\ fs [wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_NOT_LOWER_EQUAL]
  \\ metis_tac [wordsTheory.WORD_LOWER_EQ_ANTISYM, wordsTheory.WORD_LOWER_REFL,
                wordsTheory.WORD_LOWER_LOWER_EQ_TRANS,
                wordsTheory.WORD_LOWER_EQ_LOWER_TRANS,
                wordsTheory.WORD_NOT_LOWER, wordsTheory.WORD_NOT_LOWER_EQUAL]
QED

(* P §3.7.1.3 p.73 for a 1-byte access by U-mode, over the words: some
   entry matches the byte, no lower entry does, and its byte allows the
   kind *)
Theorem pmp_check_User_byte:
  !w x kind.
    pmp_check w (x, 1, kind, User) <=>
    ?i. i < 16 /\ pmp_match_w w (n2w i) x /\
        (!j. j < i ==> ~pmp_match_w w (n2w j) x) /\
        pmp_perm (pmp_cfg_byte (FST w) (FST (SND w)) (n2w i)) kind
Proof
  rpt gen_tac
  \\ PairCases_on `w`
  \\ simp_tac (srw_ss()) [pmp_check_def, pmp_first_GENLIST, pmp_entry_User_byte,
                          wordsTheory.WORD_ADD_0]
  \\ simp_tac std_ss [COND_RAND, COND_RATOR, optionTheory.IS_SOME_DEF,
                      optionTheory.THE_DEF, optionTheory.NOT_SOME_NONE]
  \\ eq_tac
  \\ rpt strip_tac
  \\ qexists_tac `i`
  \\ fs []
QED

(* The NAPOT region [lo, hi) that a pmpaddr word y encodes, as pmp_region
   computes it: m has the trailing ones of y and the zero above them set *)
Definition napot_region_def:
  napot_region (y : word64) =
    let m = y ?? (y + 1w); lo = (y && ~m) << 2 in (lo, lo + ((m + 1w) << 2))
End

Theorem pmp_region_off_napot:
  !cfg0 cfg2 addr i.
    (((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 0w : word2) ==>
     (pmp_region (cfg0, cfg2, addr) i = NONE)) /\
    (((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 3w : word2) ==>
     (pmp_region (cfg0, cfg2, addr) i = SOME (napot_region (addr i))))
Proof
  rw [pmp_region_def, napot_region_def, LET_THM]
QED

(* Bits 4 and 3 (A) of every byte of the two configuration words equal: the
   bit form in which a contract states that every entry is OFF or NAPOT *)
Theorem off_or_napot_bytes:
  !cfg0 cfg2 i.
    ((cfg0 >>> 1 ?? cfg0) && 0x0808080808080808w = 0w) /\
    ((cfg2 >>> 1 ?? cfg2) && 0x0808080808080808w = 0w) ==>
    ((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 0w : word2) \/
    ((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 3w : word2)
Proof
  rpt gen_tac
  \\ strip_tac
  \\ strip_assume_tac (SPEC ``i : word4`` word4_cases)
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ rpt (pop_assum mp_tac)
  \\ simp_tac (srw_ss()) [pmp_cfg_byte_def]
  \\ blastLib.BBLAST_TAC
QED

(* With every entry OFF or NAPOT, a byte that U-mode may access lies in the
   NAPOT region of the lowest-numbered entry that matches it, and that
   entry's byte allows the access *)
Theorem pmp_check_User_napot:
  !cfg0 cfg2 addr x kind.
    ((cfg0 >>> 1 ?? cfg0) && 0x0808080808080808w = 0w) /\
    ((cfg2 >>> 1 ?? cfg2) && 0x0808080808080808w = 0w) /\
    pmp_check (cfg0, cfg2, addr) (x, 1, kind, User) ==>
    ?i. i < 16 /\ ((4 >< 3) (pmp_cfg_byte cfg0 cfg2 (n2w i)) = 3w : word2) /\
        pmp_perm (pmp_cfg_byte cfg0 cfg2 (n2w i)) kind /\
        FST (napot_region (addr (n2w i))) <=+ x /\
        x <+ SND (napot_region (addr (n2w i))) /\
        !j. j < i ==> ~pmp_match_w (cfg0, cfg2, addr) (n2w j) x
Proof
  rpt gen_tac
  \\ strip_tac
  \\ `!i. ((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 0w : word2) \/
          ((4 >< 3) (pmp_cfg_byte cfg0 cfg2 i) = 3w : word2)`
     by metis_tac [off_or_napot_bytes]
  \\ qpat_x_assum `pmp_check _ _` (strip_assume_tac o REWRITE_RULE [pmp_check_User_byte])
  \\ qexists_tac `i`
  \\ asm_rewrite_tac []
  \\ first_x_assum (qspec_then `n2w i` strip_assume_tac)
  \\ fs [pmp_match_w_def, pmp_region_off_napot]
QED

(* The same for the PMP CSR words of a state, as pmpCheck_words reads them:
   pmpcfg0, pmpcfg2 and pmpaddr0-15 of the current hart *)
Theorem pmpCheck_User_napot:
  !s x kind.
    (((s.c_MCSR s.procID).pmpcfg0 >>> 1 ?? (s.c_MCSR s.procID).pmpcfg0) &&
     0x0808080808080808w = 0w) /\
    (((s.c_MCSR s.procID).pmpcfg2 >>> 1 ?? (s.c_MCSR s.procID).pmpcfg2) &&
     0x0808080808080808w = 0w) /\
    pmpCheck (x, 1, kind, User) s ==>
    ?i. i < 16 /\
        ((4 >< 3) (pmp_cfg_byte (s.c_MCSR s.procID).pmpcfg0
                                (s.c_MCSR s.procID).pmpcfg2 (n2w i)) = 3w : word2) /\
        pmp_perm (pmp_cfg_byte (s.c_MCSR s.procID).pmpcfg0
                               (s.c_MCSR s.procID).pmpcfg2 (n2w i)) kind /\
        FST (napot_region (pmpaddr (n2w i) s)) <=+ x /\
        x <+ SND (napot_region (pmpaddr (n2w i) s)) /\
        !j. j < i ==>
            ~pmp_match_w ((s.c_MCSR s.procID).pmpcfg0, (s.c_MCSR s.procID).pmpcfg2,
                          \k. pmpaddr k s) (n2w j) x
Proof
  rpt gen_tac
  \\ strip_tac
  \\ qpat_x_assum `pmpCheck _ _` (assume_tac o REWRITE_RULE [pmpCheck_words])
  \\ drule_all pmp_check_User_napot
  \\ BETA_TAC
  \\ REWRITE_TAC []
QED
