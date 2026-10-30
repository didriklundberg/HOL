(* ------------------------------------------------------------------------
   Selftest of riscv_stepLib, run by Holmake when HOLSELFTESTLEVEL is set.

   riscv_step_hex is run on one encoding of every riscv_dict entry (two for
   the floating-point instructions with a rounding-mode field: a static
   mode and the dynamic one) and on every instruction of the programs in
   ../sim/tests.  Each theorem must be

     hyps |- NextRISCV s = SOME s'

   with s' a record update of s, and with hyps exactly the hypotheses that
   the M-mode contract of riscv_stepTheory (doc/design-privileged.md §1.5)
   allows for the instruction:

     H1        s.c_privilege s.procID = 3w                    always
     H2        ~(s.c_MCSR s.procID).mstatus.MPRV              data accesses
     H3        pmpcfg0/2 && 0x8080808080808080w = 0w          always
     H4        ((pmpcfg0/2 >>> 1) ?? pmpcfg0/2) &&
               0x0808080808080808w = 0w                       8-byte accesses
     H5        aligned k (address), k = log2 width            accesses of 2,
                                                              4 and 8 bytes
     H6        ~(s.c_MCSR s.procID).mstatus.MIE               always

   and, as before the priv-1.13 model, the preconditions of NextRISCV
   (exception and NextFetch), the fetch (pc alignment and the instruction
   bytes), and the conditions under which the instruction is legal: misa.C
   for a compressed instruction, misa.C or a 4-byte aligned target for a
   jump or taken branch, misa.MXL <> 1w for the RV64-only instructions,
   mstatus.FS <> 0w for the F and D instructions, and fcsr.frm in RNE, RTZ,
   RDN or RUP for those with the dynamic rounding mode.

   Encodings that cannot step (reserved, EBREAK) must make riscv_step_hex
   fail; so must the CSR instructions, which the step library does not
   support yet.  The test fails if any check fails.
   ------------------------------------------------------------------------ *)

val () = Feedback.emit_MESG := false;
val () = Feedback.emit_WARNING := false;

load "riscv_stepLib" handle _ => OS.Process.exit OS.Process.failure;

(* Set only at the end of a run without failures: a compile error or an
   exception in the code below makes the test fail too. *)
val selftest_passed = ref false;

local
open HolKernel boolLib bossLib riscv_stepLib

(* ------------------------------------------------------------------------
   Allowed hypotheses
   ------------------------------------------------------------------------ *)

val s = ``s:riscv_state``
val mcsr = ``^s.c_MCSR ^s.procID``
fun conjs th = boolSyntax.strip_conj (utilsLib.rhsc (Thm.SPEC mcsr th))
val (h3a, h3b) =
  case conjs riscv_stepTheory.pmp_unlocked_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_unlocked_def"
val (h4a, h4b) =
  case conjs riscv_stepTheory.pmp_off_or_napot_def of
     [a, b] => (a, b)
   | _ => raise Fail "pmp_off_or_napot_def"

val exact =
  [("H1", ``^s.c_privilege ^s.procID = 3w``),
   ("H2", ``~^mcsr.mstatus.MPRV``),
   ("H3.pmpcfg0", h3a), ("H3.pmpcfg2", h3b),
   ("H4.pmpcfg0", h4a), ("H4.pmpcfg2", h4b),
   ("H6", ``~^mcsr.mstatus.MIE``),
   ("exception", ``^s.exception = NoException``),
   ("NextFetch", ``^s.c_NextFetch ^s.procID = NONE``),
   ("pc<0>", ``~word_bit 0 (^s.c_PC ^s.procID)``),
   ("pc<1>|C", ``~word_bit 1 (^s.c_PC ^s.procID) \/ ^mcsr.misa.C``),
   ("C", ``^mcsr.misa.C``),
   ("RV64", ``^mcsr.misa.MXL <> 1w``),
   ("FS", ``^mcsr.mstatus.FS <> 0w``),
   ("frm", ``~word_bit 2 (^s.c_UCSR ^s.procID).fpcsr.FRM``)]

val mem_pat0 = ``^s.MEM8 (^s.c_PC ^s.procID) = v2w (l: bool list)``
val mem_pat = ``^s.MEM8 (^s.c_PC ^s.procID + k) = v2w (l: bool list)``
val aligned_pat = ``aligned n (a: word64)``
val target_pat = ``~word_bit 1 (a: word64) \/ ^mcsr.misa.C``

fun category h =
  case List.find (fn (_, t) => Term.aconv t h) exact of
     SOME (c, _) => c
   | NONE =>
       if Lib.can (Term.match_term mem_pat0) h orelse
          Lib.can (Term.match_term mem_pat) h
         then "mem"
       else case Lib.total (Term.match_term aligned_pat) h of
          SOME (sub, _) =>
            "H5." ^ Parse.term_to_string (Term.subst sub ``n:num``)
        | NONE =>
            if Lib.can (Term.match_term target_pat) h then "target<1>|C"
            else "UNEXPECTED: " ^ Parse.term_to_string h

(* ------------------------------------------------------------------------
   What each instruction needs
   ------------------------------------------------------------------------ *)

fun hex_int h = Option.valOf (StringCvt.scanString (Int.scan StringCvt.HEX) h)

(* (outer constructor, instruction name) of the decoded instruction *)
fun decoded h =
  let
    val ast = utilsLib.rhsc (riscv_decode_hex h)
    val (c, args) = boolSyntax.strip_comb ast
    val outer = fst (Term.dest_const c)
    val inner =
      case args of
         [a] => (case Lib.total (fst o Term.dest_const o fst o
                                 boolSyntax.strip_comb) a of
                    SOME n => n
                  | NONE => outer)
       | _ => outer
  in
    (outer, if List.null args then outer else inner)
  end

fun class_of (outer, inner) =
  case outer of
     "ArithI" => "ALU"
   | "ArithR" => "ALU"
   | "Shift" => "ALU"
   | "MulDiv" => "ALU"
   | "Branch" =>
       if inner = "JAL" orelse inner = "JALR" then "JAL/JALR" else "branch"
   | "Load" => "load"
   | "Store" => "store"
   | "AMO" =>
       if String.isPrefix "LR_" inner orelse String.isPrefix "SC_" inner
         then "LR/SC"
       else "AMO"
   | "FPLoad" => "FP load/store"
   | "FPStore" => "FP load/store"
   | "FArith" => "FP arithmetic"
   | "FConv" => "FP arithmetic"
   | "FENCE" => "FENCE"
   | "FENCE_I" => "FENCE"
   | "System" => "system"
   | _ => "other"

fun width inner =
  if Lib.mem inner ["LB", "LBU", "SB"] then 1
  else if Lib.mem inner ["LH", "LHU", "SH"] then 2
  else if Lib.mem inner ["LW", "LWU", "SW", "FLW", "FSW", "LR_W", "SC_W"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_W" inner then 4
  else if Lib.mem inner ["LD", "SD", "FLD", "FSD", "LR_D", "SC_D"]
          orelse String.isPrefix "AMO" inner andalso
                 String.isSuffix "_D" inner then 8
  else 0

val rv64_only =
  ["ADDIW", "SLLIW", "SRLIW", "SRAIW", "ADDW", "SUBW", "SLLW", "SRLW",
   "SRAW", "MULW", "DIVW", "REMW", "DIVUW", "REMUW", "LD", "LWU", "SD",
   "LR_D", "SC_D"]

(* the instructions with a rounding-mode field *)
val rounding =
  ["FADD_S", "FSUB_S", "FMUL_S", "FDIV_S", "FSQRT_S", "FMADD_S", "FMSUB_S",
   "FNMADD_S", "FNMSUB_S", "FCVT_S_W", "FCVT_S_WU", "FCVT_S_L", "FCVT_S_LU",
   "FCVT_W_S", "FCVT_WU_S", "FCVT_L_S", "FCVT_LU_S",
   "FADD_D", "FSUB_D", "FMUL_D", "FDIV_D", "FSQRT_D", "FMADD_D", "FMSUB_D",
   "FNMADD_D", "FNMSUB_D", "FCVT_D_W", "FCVT_D_WU", "FCVT_D_L", "FCVT_D_LU",
   "FCVT_W_D", "FCVT_WU_D", "FCVT_L_D", "FCVT_LU_D", "FCVT_S_D", "FCVT_D_S"]

(* required hypotheses, and those that may also occur *)
fun expected h (outer, inner) =
  let
    val compressed = String.size h <= 4
    val w = width inner
    val fp = Lib.mem outer ["FPLoad", "FPStore", "FArith", "FConv"]
    val dyn = Lib.mem inner rounding andalso
              (hex_int h div 4096) mod 8 = 7
    val required =
      ["H1", "H3.pmpcfg0", "H3.pmpcfg2", "H6", "exception", "NextFetch",
       "pc<0>", "mem", if compressed then "C" else "pc<1>|C"] @
      (if w > 0 then ["H2"] else []) @
      (if w = 8 then ["H4.pmpcfg0", "H4.pmpcfg2"] else []) @
      (case w of 2 => ["H5.1"] | 4 => ["H5.2"] | 8 => ["H5.3"] | _ => []) @
      (if Lib.mem inner rv64_only then ["RV64"] else []) @
      (if fp then ["FS"] else []) @
      (if dyn then ["frm"] else [])
    val optional =
      (if outer = "Branch" then ["target<1>|C"] else []) @
      (if Lib.mem inner ["SLLI", "SRLI", "SRAI"] then ["RV64"] else [])
    (* Known deviation of riscv.spec: FLE.S does not test fpEnabled(), so
       it runs while mstatus.FS is Off and its theorem lacks FS. *)
    val (required, optional) =
      if inner = "FLE_S"
        then (List.filter (not o equal "FS") required, "FS" :: optional)
      else (required, optional)
  in
    (required, optional)
  end

(* ------------------------------------------------------------------------
   Checking one theorem
   ------------------------------------------------------------------------ *)

val bad_consts =
  [``signalException``, ``signalAddressException``, ``raise'exception``,
   ``dataAddr``, ``fetchAddr``, ``pmpCheck``, ``round``, ``curPrivilege``,
   ``in32BitMode``, ``haveRVC``]

(* s' is s with a sequence of field updates *)
fun is_update tm =
  Term.aconv tm s orelse
  (case boolSyntax.strip_comb tm of
      (f, [_, r]) =>
        Term.is_const f andalso
        String.isSuffix "_fupd" (fst (Term.dest_const f)) andalso
        is_update r
    | _ => false)

fun sort_uniq l = Lib.mk_set (Listsort.sort String.compare l)

fun check h th =
  let
    val inst = decoded h
    val (required, optional) = expected h inst
    val cats = List.map category (Thm.hyp th)
    val ucats = sort_uniq cats
    val (l, r) = boolSyntax.dest_eq (Thm.concl th)
    val errors =
      List.filter (String.isPrefix "UNEXPECTED") ucats @
      List.mapPartial
        (fn c => if Lib.mem c ucats then NONE else SOME ("missing " ^ c))
        required @
      List.mapPartial
        (fn c => if Lib.mem c (required @ optional) orelse
                    String.isPrefix "UNEXPECTED" c
                   then NONE
                 else SOME ("not allowed: " ^ c)) ucats @
      (if Lib.mem "F" (List.map Parse.term_to_string (Thm.hyp th))
         then ["vacuous"] else []) @
      (if Term.aconv l ``riscv_step$NextRISCV ^s`` andalso
          optionSyntax.is_some r andalso is_update (optionSyntax.dest_some r)
         then []
       else ["conclusion is not NextRISCV s = SOME (s with ...)"]) @
      List.mapPartial
        (fn c => if Lib.can (HolKernel.find_term (Term.same_const c)) r
                   then SOME ("left in conclusion: " ^
                              fst (Term.dest_const c))
                 else NONE) bad_consts
  in
    (inst, ucats, errors)
  end

(* ------------------------------------------------------------------------
   Test cases
   ------------------------------------------------------------------------ *)

(* A deterministic choice of the free bits of a riscv_dict pattern *)
local
  val seed = ref 0w42 : Word32.word ref
  fun next () =
    ( seed := Word32.+ (Word32.* (!seed, 0w1664525), 0w1013904223)
    ; Word32.andb (Word32.>> (!seed, 0w16), 0w1) = 0w1 )
in
  fun random_bit () = next ()
end

fun bits_to_hex bs =
  let
    val n = List.foldl (fn (b, a) => 2 * a + (if b then 1 else 0)) 0 bs
    val digits = List.length bs div 4
  in
    StringCvt.padLeft #"0" digits
      (String.map Char.toLower (Int.fmt StringCvt.HEX n))
  end

(* the pattern's bits, MSB first, with rm (bits 14:12) set when given *)
fun instantiate rm pat =
  let
    val (l, _) = listSyntax.dest_list pat
    val n = List.length l
    val bits =
      List.map
        (fn t => if Teq t then true else if Feq t then false
                 else random_bit ()) l
    val bits =
      case rm of
         NONE => bits
       | SOME v =>
           List.tabulate
             (n, fn i =>
                   if i >= 17 andalso i <= 19
                     then (v div (if i = 17 then 4 else if i = 18 then 2
                                  else 1)) mod 2 = 1
                   else List.nth (bits, i))
  in
    bits_to_hex bits
  end

(* The instructions the step library cannot step, and why *)
fun no_step (outer, inner) =
  if outer = "UnknownInstruction" then SOME "reserved encoding"
  else if inner = "EBREAK" then SOME "EBREAK traps"
  else if Lib.mem inner ["CSRRW", "CSRRS", "CSRRC", "CSRRWI", "CSRRSI",
                         "CSRRCI"]
    then SOME "CSR instructions are not supported yet"
  else NONE

val sim_tests = [
  (* tests/int.S *)
  ("00002d97", "auipc s11,0x2"),
  ("050d8d93", "addi s11,s11,80"),
  ("00000193", "addi gp,zero,0"),
  ("00002417", "auipc s0,0x2"),
  ("ff440413", "addi s0,s0,-12"),
  ("00000293", "addi t0,zero,0"),
  ("00000513", "addi a0,zero,0"),
  ("00800313", "addi t1,zero,8"),
  ("00329393", "slli t2,t0,0x3"),
  ("007403b3", "add t2,s0,t2"),
  ("0003be03", "ld t3,0(t2)"),
  ("01c50533", "add a0,a0,t3"),
  ("00128293", "addi t0,t0,1"),
  ("fe62c6e3", "blt t0,t1,80000020"),
  ("00adb023", "sd a0,0(s11)"),
  ("008d8d93", "addi s11,s11,8"),
  ("00100193", "addi gp,zero,1"),
  ("00247fb7", "lui t6,0x247"),
  ("8adf8f9b", "addiw t6,t6,-1875"),
  ("00ef9f93", "slli t6,t6,0xe"),
  ("ccdf8f93", "addi t6,t6,-819"),
  ("00cf9f93", "slli t6,t6,0xc"),
  ("5e7f8f93", "addi t6,t6,1511"),
  ("00df9f93", "slli t6,t6,0xd"),
  ("024f8f93", "addi t6,t6,36"),
  ("25f51e63", "bne a0,t6,800002c0"),
  ("01040503", "lb a0,16(s0)"),
  ("00200193", "addi gp,zero,2"),
  ("ff000f93", "addi t6,zero,-16"),
  ("25f51663", "bne a0,t6,800002c0"),
  ("01044503", "lbu a0,16(s0)"),
  ("00300193", "addi gp,zero,3"),
  ("0f000f93", "addi t6,zero,240"),
  ("23f51e63", "bne a0,t6,800002c0"),
  ("01041503", "lh a0,16(s0)"),
  ("00400193", "addi gp,zero,4"),
  ("ffffefb7", "lui t6,0xffffe"),
  ("ef0f8f9b", "addiw t6,t6,-272"),
  ("23f51463", "bne a0,t6,800002c0"),
  ("01045503", "lhu a0,16(s0)"),
  ("00500193", "addi gp,zero,5"),
  ("0000efb7", "lui t6,0xe"),
  ("21f51a63", "bne a0,t6,800002c0"),
  ("01042503", "lw a0,16(s0)"),
  ("00600193", "addi gp,zero,6"),
  ("9abcefb7", "lui t6,0x9abce"),
  ("21f51063", "bne a0,t6,800002c0"),
  ("01046503", "lwu a0,16(s0)"),
  ("00700193", "addi gp,zero,7"),
  ("0004dfb7", "lui t6,0x4d"),
  ("5e7f8f9b", "addiw t6,t6,1511"),
  ("ef0f8f93", "addi t6,t6,-272"),
  ("1df51e63", "bne a0,t6,800002c0"),
  ("00002497", "auipc s1,0x2"),
  ("f5848493", "addi s1,s1,-168"),
  ("fff00593", "addi a1,zero,-1"),
  ("00b4b023", "sd a1,0(s1)"),
  ("01100593", "addi a1,zero,17"),
  ("00b48023", "sb a1,0(s1)"),
  ("000035b7", "lui a1,0x3"),
  ("3225859b", "addiw a1,a1,802"),
  ("00b49123", "sh a1,2(s1)"),
  ("776655b7", "lui a1,0x77665"),
  ("5445859b", "addiw a1,a1,1348"),
  ("00b4a223", "sw a1,4(s1)"),
  ("0004b503", "ld a0,0(s1)"),
  ("00800193", "addi gp,zero,8"),
  ("00776fb7", "lui t6,0x776"),
  ("655f8f9b", "addiw t6,t6,1621"),
  ("443f8f93", "addi t6,t6,1091"),
  ("323f8f93", "addi t6,t6,803"),
  ("010f9f93", "slli t6,t6,0x10"),
  ("f11f8f93", "addi t6,t6,-239"),
  ("17f51c63", "bne a0,t6,800002c0"),
  ("00900193", "addi gp,zero,9"),
  ("0014c503", "lbu a0,1(s1)"),
  ("0ff00f93", "addi t6,zero,255"),
  ("17f51463", "bne a0,t6,800002c0"),
  ("01043583", "ld a1,16(s0)"),
  ("00300613", "addi a2,zero,3"),
  ("02c58533", "mul a0,a1,a2"),
  ("00a00193", "addi gp,zero,10"),
  ("0036afb7", "lui t6,0x36a"),
  ("d03f8f9b", "addiw t6,t6,-765"),
  ("69df8f93", "addi t6,t6,1693"),
  ("00ff9f93", "slli t6,t6,0xf"),
  ("1b5f8f93", "addi t6,t6,437"),
  ("cd0f8f93", "addi t6,t6,-816"),
  ("13f51663", "bne a0,t6,800002c0"),
  ("01843603", "ld a2,24(s0)"),
  ("02c5b533", "mulhu a0,a1,a2"),
  ("00b00193", "addi gp,zero,11"),
  ("12345fb7", "lui t6,0x12345"),
  ("678f8f9b", "addiw t6,t6,1656"),
  ("11f51a63", "bne a0,t6,800002c0"),
  ("ff900593", "addi a1,zero,-7"),
  ("00200613", "addi a2,zero,2"),
  ("02c5c533", "div a0,a1,a2"),
  ("00c00193", "addi gp,zero,12"),
  ("ffd00f93", "addi t6,zero,-3"),
  ("0ff51e63", "bne a0,t6,800002c0"),
  ("02c5e533", "rem a0,a1,a2"),
  ("00d00193", "addi gp,zero,13"),
  ("fff00f93", "addi t6,zero,-1"),
  ("0ff51663", "bne a0,t6,800002c0"),
  ("0205d533", "divu a0,a1,zero"),
  ("00e00193", "addi gp,zero,14"),
  ("0df51e63", "bne a0,t6,800002c0"),
  ("0205e533", "rem a0,a1,zero"),
  ("00f00193", "addi gp,zero,15"),
  ("ff900f93", "addi t6,zero,-7"),
  ("0df51263", "bne a0,t6,800002c0"),
  ("02043583", "ld a1,32(s0)"),
  ("4045d513", "srai a0,a1,0x4"),
  ("01000193", "addi gp,zero,16"),
  ("fff00f9b", "addiw t6,zero,-1"),
  ("03bf9f93", "slli t6,t6,0x3b"),
  ("0bf51663", "bne a0,t6,800002c0"),
  ("0045d513", "srli a0,a1,0x4"),
  ("01100193", "addi gp,zero,17"),
  ("00100f9b", "addiw t6,zero,1"),
  ("09f51c63", "bne a0,t6,800002c0"),
  ("800005b7", "lui a1,0x80000"),
  ("fff5859b", "addiw a1,a1,-1"),
  ("0015851b", "addiw a0,a1,1"),
  ("01200193", "addi gp,zero,18"),
  ("80000fb7", "lui t6,0x80000"),
  ("09f51063", "bne a0,t6,800002c0"),
  ("0045551b", "srliw a0,a0,0x4"),
  ("01300193", "addi gp,zero,19"),
  ("08000fb7", "lui t6,0x8000"),
  ("07f51463", "bne a0,t6,800002c0"),
  ("00100613", "addi a2,zero,1"),
  ("00c5a533", "slt a0,a1,a2"),
  ("01400193", "addi gp,zero,20"),
  ("00100f93", "addi t6,zero,1"),
  ("05f51863", "bne a0,t6,800002c0"),
  ("00c5b533", "sltu a0,a1,a2"),
  ("01500193", "addi gp,zero,21"),
  ("00000f93", "addi t6,zero,0"),
  ("05f51063", "bne a0,t6,800002c0"),
  ("02800513", "addi a0,zero,40"),
  ("01c000ef", "jal ra,800002a4"),
  ("01600193", "addi gp,zero,22"),
  ("02a00f93", "addi t6,zero,42"),
  ("03f51263", "bne a0,t6,800002c0"),
  ("00c0006f", "jal zero,800002ac"),
  ("00250513", "addi a0,a0,2"),
  ("00008067", "jalr zero,0(ra)"),
  ("00001f17", "auipc t5,0x1"),
  ("d50f0f13", "addi t5,t5,-688"),
  ("01ff3023", "sd t6,0(t5)"),
  ("0000006f", "jal zero,800002bc"),
  ("00119f93", "slli t6,gp,0x1"),
  ("001fef93", "ori t6,t6,1"),
  ("d38f0f13", "addi t5,t5,-712"),
  (* tests/rvc.S *)
  ("4181", "c.li gp,0"),
  ("00002117", "auipc sp,0x2"),
  ("04610113", "addi sp,sp,70"),
  ("fee40413", "addi s0,s0,-18"),
  ("4515", "c.li a0,5"),
  ("051d", "c.addi a0,7"),
  ("55f5", "c.li a1,-3"),
  ("952e", "c.add a0,a1"),
  ("862a", "c.mv a2,a0"),
  ("8e0d", "c.sub a2,a1"),
  ("00cdb023", "sd a2,0(s11)"),
  ("0da1", "c.addi s11,8"),
  ("4185", "c.li gp,1"),
  ("4fb1", "c.li t6,12"),
  ("11f61c63", "bne a2,t6,80000148"),
  ("6014", "c.ld a3,0(s0)"),
  ("0685", "c.addi a3,1"),
  ("e414", "c.sd a3,8(s0)"),
  ("6418", "c.ld a4,8(s0)"),
  ("00edb023", "sd a4,0(s11)"),
  ("4189", "c.li gp,2"),
  ("0fba", "c.slli t6,0xe"),
  ("c4df8f93", "addi t6,t6,-947"),
  ("0fb2", "c.slli t6,0xc"),
  ("0fb6", "c.slli t6,0xd"),
  ("ef1f8f93", "addi t6,t6,-271"),
  ("0ff71563", "bne a4,t6,80000148"),
  ("405c", "c.lw a5,4(s0)"),
  ("00fdb023", "sd a5,0(s11)"),
  ("418d", "c.li gp,3"),
  ("0df79a63", "bne a5,t6,80000148"),
  ("713d", "c.addi16sp sp,-32"),
  ("0808", "c.addi4spn a0,sp,16"),
  ("e03a", "c.sdsp a4,0(sp)"),
  ("c43e", "c.swsp a5,8(sp)"),
  ("6582", "c.ldsp a1,0(sp)"),
  ("4622", "c.lwsp a2,8(sp)"),
  ("6105", "c.addi16sp sp,32"),
  ("95b2", "c.add a1,a2"),
  ("00bdb023", "sd a1,0(s11)"),
  ("4191", "c.li gp,4"),
  ("0fbe", "c.slli t6,0xf"),
  ("8adf8f93", "addi t6,t6,-1875"),
  ("f13f8f93", "addi t6,t6,-237"),
  ("569f8f93", "addi t6,t6,1385"),
  ("09f59f63", "bne a1,t6,80000148"),
  ("557d", "c.li a0,-1"),
  ("1572", "c.slli a0,0x3c"),
  ("8511", "c.srai a0,0x4"),
  ("9161", "c.srli a0,0x38"),
  ("897d", "c.andi a0,31"),
  ("4195", "c.li gp,5"),
  ("4ffd", "c.li t6,31"),
  ("09f51363", "bne a0,t6,80000148"),
  ("4571", "c.li a0,28"),
  ("45a9", "c.li a1,10"),
  ("8e6d", "c.and a2,a1"),
  ("8e4d", "c.or a2,a1"),
  ("8e29", "c.xor a2,a0"),
  ("800006b7", "lui a3,0x80000"),
  ("36fd", "c.addiw a3,-1"),
  ("9eb1", "c.addw a3,a2"),
  ("9e8d", "c.subw a3,a1"),
  ("00ddb023", "sd a3,0(s11)"),
  ("4199", "c.li gp,6"),
  ("2fad", "c.addiw t6,11"),
  ("05f69f63", "bne a3,t6,80000148"),
  ("4501", "c.li a0,0"),
  ("4581", "c.li a1,0"),
  ("c111", "c.beqz a0,800000f6"),
  ("4585", "c.li a1,1"),
  ("e99d", "c.bnez a1,8000012c"),
  ("a011", "c.j 800000fc"),
  ("4589", "c.li a1,2"),
  ("419d", "c.li gp,7"),
  ("4f81", "c.li t6,0"),
  ("05f59463", "bne a1,t6,80000148"),
  ("4505", "c.li a0,1"),
  ("00000297", "auipc t0,0x0"),
  ("02a28293", "addi t0,t0,42"),
  ("9282", "c.jalr t0"),
  ("41a1", "c.li gp,8"),
  ("4f8d", "c.li t6,3"),
  ("03f51763", "bne a0,t6,80000148"),
  ("657d", "c.lui a0,0x1f"),
  ("0001", "c.addi zero,0"),
  ("41a5", "c.li gp,9"),
  ("6ffd", "c.lui t6,0x1f"),
  ("03f51163", "bne a0,t6,80000148"),
  ("a039", "c.j 80000138"),
  ("a829", "c.j 80000148"),
  ("85aa", "c.mv a1,a0"),
  ("8082", "c.jr ra"),
  ("4f85", "c.li t6,1"),
  ("ec6f0f13", "addi t5,t5,-314"),
  ("a001", "c.j 80000146"),
  ("eb0f0f13", "addi t5,t5,-336"),
  (* tests/fp.S *)
  ("030d8d93", "addi s11,s11,48"),
  ("000022b7", "lui t0,0x2"),
  ("3002a073", "csrrs zero,mstatus,t0"),
  ("fec40413", "addi s0,s0,-20"),
  ("00043507", "fld fa0,0(s0)"),
  ("00843587", "fld fa1,8(s0)"),
  ("02b57653", "fadd.d fa2,fa0,fa1"),
  ("e2060553", "fmv.x.d a0,fa2"),
  ("00002fb7", "lui t6,0x2"),
  ("007f8f9b", "addiw t6,t6,7"),
  ("031f9f93", "slli t6,t6,0x31"),
  ("0df51a63", "bne a0,t6,80000118"),
  ("12b576d3", "fmul.d fa3,fa0,fa1"),
  ("e2068553", "fmv.x.d a0,fa3"),
  ("00004fb7", "lui t6,0x4"),
  ("00bf8f9b", "addiw t6,t6,11"),
  ("030f9f93", "slli t6,t6,0x30"),
  ("0bf51c63", "bne a0,t6,80000118"),
  ("d225f753", "fcvt.d.l fa4,a1"),
  ("52e6f7c3", "fmadd.d fa5,fa3,fa4,fa0"),
  ("00f43827", "fsd fa5,16(s0)"),
  ("01043503", "ld a0,16(s0)"),
  ("fffe0fb7", "lui t6,0xfffe0"),
  ("1b1f8f9b", "addiw t6,t6,433"),
  ("02df9f93", "slli t6,t6,0x2d"),
  ("09f51463", "bne a0,t6,80000118"),
  ("c2279553", "fcvt.l.d a0,fa5,rtz"),
  ("fea00f93", "addi t6,zero,-22"),
  ("07f51863", "bne a0,t6,80000118"),
  ("01843507", "fld fa0,24(s0)"),
  ("02043587", "fld fa1,32(s0)"),
  ("03fd3fb7", "lui t6,0x3fd3"),
  ("333f8f9b", "addiw t6,t6,819"),
  ("333f8f93", "addi t6,t6,819"),
  ("334f8f93", "addi t6,t6,820"),
  ("03f51863", "bne a0,t6,80000118"),
  ("02843687", "fld fa3,40(s0)"),
  ("a2d62553", "feq.d a0,fa2,fa3"),
  ("01f51e63", "bne a0,t6,80000118"),
  ("0040006f", "jal zero,80000104"),
  ("ef8f0f13", "addi t5,t5,-264"),
  ("ee0f0f13", "addi t5,t5,-288"),
  (* tests/fail.S *)
  ("000d8d93", "addi s11,s11,0"),
  ("03f01a63", "bne zero,t6,80000048"),
  ("03f01463", "bne zero,t6,80000048"),
  ("01f01e63", "bne zero,t6,80000048"),
  ("fc8f0f13", "addi t5,t5,-56"),
  ("fb0f0f13", "addi t5,t5,-80")
]

(* ------------------------------------------------------------------------
   Running
   ------------------------------------------------------------------------ *)

val failures = ref ([] : string list)
val shapes = ref ([] : (string * string list) list)
val examples = ref ([] : (string * (string * Thm.thm)) list)
val counts = ref ([] : (string * int) list)
val no_steps = ref 0

fun incr key =
  counts :=
    (case Lib.assoc1 key (!counts) of
        SOME (_, n) => (key, n + 1) :: List.filter (not o equal key o fst)
                                                    (!counts)
      | NONE => (key, 1) :: !counts)

fun fail msg = (print ("FAIL " ^ msg ^ "\n"); failures := msg :: !failures)

(* returns false when the theorem is vacuous for this choice of bits *)
fun test name h =
  let
    val inst = decoded h
  in
    case no_step inst of
       SOME why =>
         (( ignore (riscv_step_hex h)
          ; fail (name ^ " " ^ h ^ ": stepped, but " ^ why); true )
          handle HOL_ERR _ =>
            ( no_steps := !no_steps + 1
            ; print ("no step (" ^ why ^ "): " ^ name ^ " " ^ h ^ "\n")
            ; true ))
     | NONE =>
         let
           val th = riscv_step_hex h
           val (inst as (_, inner), cats, errors) = check h th
           val compressed = String.size h <= 4
           val cls = class_of inst
           val key = if compressed then "compressed" else cls
         in
           if List.exists (Lib.equal "vacuous") errors then false
           else
             ( List.app (fn e => fail (name ^ " " ^ h ^ " (" ^ inner ^
                                        "): " ^ e)) errors
             ; incr key
             ; shapes := (key, cats) :: !shapes
             ; if Lib.can (Lib.assoc key) (!examples) then ()
               else examples := (key, (name ^ " " ^ h, th)) :: !examples
             ; true )
         end
         handle e =>
           (fail (name ^ " " ^ h ^ ": " ^ General.exnMessage e); true)
  end

val () = print "\nriscv_stepLib selftest\n\n"
val t0 = Time.now ()

(* every riscv_dict entry; a vacuous theorem (e.g. a misaligned constant
   address) is retried with other bits *)
val () =
  List.app
    (fn (name, pat) =>
       let
         val base =
           if String.isSuffix "_NOP" name
             then String.substring (name, 0, String.size name - 4)
           else name
         val rms = if Lib.mem base rounding then [SOME 0, SOME 7] else [NONE]
         fun go rm k =
           if k = 0 then fail (name ^ ": no non-vacuous encoding found")
           else if test name (instantiate rm pat) then ()
           else go rm (k - 1)
       in
         List.app (fn rm => go rm 8) rms
       end)
    riscv_dict

val ndict = List.length riscv_dict

val () =
  List.app
    (fn (h, txt) =>
       if test ("sim: " ^ txt) h then ()
       else fail ("sim: " ^ txt ^ " " ^ h ^ ": vacuous theorem"))
    sim_tests

val () =
  let
    val classes =
      ["ALU", "branch", "JAL/JALR", "load", "store", "AMO", "LR/SC",
       "FP load/store", "FP arithmetic", "compressed", "FENCE", "system"]
    fun pr_shape (key, l) =
      print ("    {" ^ String.concatWith ", " l ^ "}\n")
  in
    print ("\nriscv_dict entries: " ^ Int.toString ndict ^
           ", sim/tests instructions: " ^ Int.toString (List.length sim_tests) ^
           "\nexpected not to step (reserved, EBREAK, CSR): " ^
           Int.toString (!no_steps) ^ "\n\nhypotheses by class:\n");
    List.app
      (fn c =>
         let
           val n = case Lib.assoc1 c (!counts) of SOME (_, n) => n | NONE => 0
           val sets =
             Lib.mk_set
               (List.map (String.concatWith ", " o snd)
                  (List.filter (equal c o fst) (!shapes)))
         in
           print ("  " ^ c ^ ": " ^ Int.toString n ^ " theorems\n");
           List.app (fn x => print ("    {" ^ x ^ "}\n"))
             (Listsort.sort String.compare sets)
         end) classes;
    print "\nexamples:\n";
    List.app
      (fn c =>
         case Lib.assoc1 c (!examples) of
            SOME (_, (what, th)) =>
              ( print ("\n  " ^ c ^ ": " ^ what ^ "\n")
              ; List.app (fn h => print ("    " ^ Parse.term_to_string h ^ "\n"))
                  (Thm.hyp th) )
          | NONE => ()) classes;
    print ("\ntime: " ^ Time.toString (Time.- (Time.now (), t0)) ^ " s\n")
  end
in
val () =
  case !failures of
     [] => ( print "\nriscv_stepLib selftest: all checks passed\n"
           ; selftest_passed := true )
   | l => print ("\nriscv_stepLib selftest: " ^ Int.toString (List.length l) ^
                 " failures\n")
end;

val () =
  OS.Process.exit
    (if !selftest_passed then OS.Process.success else OS.Process.failure);
