(* riscv-sim: a standalone emulator around the L3-generated RISC-V model
   (../model/riscv.sml), for running ELF files and writing a per-step trace
   that compare.py can diff against sail-riscv.  See README.md for the
   command line, the trace format and the known limitations.

   The structure follows l3riscv's src/sml/model.sml (BSD licence, see
   lib/LICENSE.l3riscv), rewritten for HOL's export of riscv.spec, which has
   different state and CSR names.

   How the effects of one step are found (README.md, "How effects are
   captured"):
   - GPR/FPR writes: the spec's own log (mark_log(LOG_REG, ...) in the GPR,
     FPRS and FPRD components), which lists every write, also of an
     unchanged value.  The value printed is the register after the step.
     As a cross-check the register files are also diffed around the step;
     a change without a log entry is reported on stderr and still traced.
   - CSR writes: the log entries of the CSR component (explicit CSR
     instructions), plus every watched CSR whose value changed (implicit
     writes: fflags from FP instructions, mstatus.FS, trap entry, ...).
     The value printed is CSRMap(n) after the step.
   - Memory writes: the spec's StateDelta (recordStore), whose addr and
     st_width say where a store, AMO or SC wrote: the physical address,
     as in sail's trace.  The data printed is read back from memory after
     the step.
   - Traps: the log entry of takeTrap ("trapping from ... [exc] n").
*)

structure Sim :> sig val main : unit -> unit end =
struct

(* ------------------------------------------------------------------------
   Output and exit
   ------------------------------------------------------------------------ *)

(* stdout (the trace) is flushed first so that messages appear in order *)
fun eprint s =
  ( TextIO.flushOut TextIO.stdOut
  ; TextIO.output (TextIO.stdErr, s)
  ; TextIO.flushOut TextIO.stdErr )
fun oprint s = TextIO.output (TextIO.stdOut, s)

val EXIT_PASS        = 0   (* HTIF exit code 0 *)
val EXIT_FAIL        = 1   (* HTIF exit code <> 0 *)
val EXIT_MAX_INSTS   = 2   (* --max-insts reached *)
val EXIT_MODEL_ERROR = 3   (* the model raised UNDEFINED, INTERNAL_ERROR, ... *)
val EXIT_TRAP_LOOP   = 4   (* TRAP_LOOP_LIMIT consecutive steps trapped *)
val EXIT_USAGE       = 64  (* bad command line or unloadable ELF *)

fun exitWith (n : int) =
  ( TextIO.flushOut TextIO.stdOut
  ; TextIO.flushOut TextIO.stdErr
  ; Posix.Process.exit (Word8.fromInt n) )

exception Usage of string      (* bad command line: print the usage *)
exception LoadError of string  (* unusable ELF file *)

(* ------------------------------------------------------------------------
   Numbers
   ------------------------------------------------------------------------ *)

val two64 : IntInf.int = IntInf.pow (2, 64)

fun hexDigits (n : int) (v : IntInf.int) =
  StringCvt.padLeft #"0" n (String.map Char.toLower (IntInf.fmt StringCvt.HEX v))

fun hex16 v = "0x" ^ hexDigits 16 v

val u = BitsN.toUInt

(* bits hi..lo of a non-negative integer *)
fun bitsOf (v : IntInf.int, hi : int, lo : int) =
  (v div IntInf.pow (2, lo)) mod IntInf.pow (2, hi - lo + 1)

fun parseNum (s : string) : IntInf.int =
  let
    val (radix, digits, isDigit) =
      if String.isPrefix "0x" s orelse String.isPrefix "0X" s
        then (StringCvt.HEX, String.extract (s, 2, NONE), Char.isHexDigit)
      else (StringCvt.DEC, s, Char.isDigit)
  in
    if digits <> "" andalso CharVector.all isDigit digits
      then valOf (StringCvt.scanString (IntInf.scan radix) digits)
    else raise Usage ("not a number: " ^ s)
  end

(* ------------------------------------------------------------------------
   Warnings (each distinct message once, on stderr)
   ------------------------------------------------------------------------ *)

val warned : string list ref = ref []

fun warn s =
  if List.exists (fn x => x = s) (!warned) then ()
  else (warned := s :: !warned; eprint ("riscv-sim: warning: " ^ s ^ "\n"))

(* ------------------------------------------------------------------------
   Memory (the model's byte map MEM8, indexed by physical address)
   ------------------------------------------------------------------------ *)

fun memByte (a : IntInf.int) : IntInf.int =
  u (riscv.Map.lookup (!riscv.MEM8, a mod two64))

fun setMemByte (a : IntInf.int, b : IntInf.int) =
  riscv.MEM8 := riscv.Map.update (!riscv.MEM8, a mod two64, BitsN.fromInt (b, 8))

(* w bytes at a, little-endian *)
fun readLE (a : IntInf.int, w : int) : IntInf.int =
  let
    fun loop (i, acc) =
      if i < 0 then acc
      else loop (i - 1, acc * 256 + memByte (a + IntInf.fromInt i))
  in
    loop (w - 1, 0)
  end

fun writeLE (a : IntInf.int, w : int, v : IntInf.int) =
  let
    fun loop (i, v) =
      if i = w then ()
      else ( setMemByte (a + IntInf.fromInt i, v mod 256)
           ; loop (i + 1, v div 256) )
  in
    loop (0, v)
  end

(* ------------------------------------------------------------------------
   Options
   ------------------------------------------------------------------------ *)

type options =
  { trace : bool, traceMemReads : bool, asm : bool, maxInsts : IntInf.int,
    pcStart : IntInf.int option, sigFile : string option,
    tohostExit : bool, rvc : bool, elf : string }

val usage =
  "usage: riscv-sim [options] <elf>\n\
  \\n\
  \Runs <elf> on the L3 RISC-V model (HOL4 examples/l3-machine-code/riscv).\n\
  \\n\
  \  --trace            write the canonical per-step trace to stdout\n\
  \  --trace-mem-reads  with --trace, also trace memory reads (mr[...])\n\
  \  --no-asm           with --trace, leave out the '# disassembly' comments\n\
  \  --max-insts N      stop after N steps, exit status 2 (default 0: no limit)\n\
  \  --pc-start ADDR    start at ADDR instead of the ELF entry point\n\
  \  --signature FILE   at the end, write memory [begin_signature,\n\
  \                     end_signature) to FILE, one 32-bit word per line\n\
  \  --tohost-exit      stop at the first store that leaves a non-zero value\n\
  \                     in tohost, without waiting for a complete HTIF command\n\
  \  --no-c             disable the C extension (misa.C := false)\n\
  \  -h, --help         this message\n\
  \\n\
  \Exit status: 0 tohost pass, 1 tohost fail, 2 --max-insts reached,\n\
  \3 model exception (UNDEFINED, INTERNAL_ERROR, ...), 4 trap loop,\n\
  \64 usage or ELF error.\n"

val defaultOptions : options =
  { trace = false, traceMemReads = false, asm = true, maxInsts = 0,
    pcStart = NONE, sigFile = NONE, tohostExit = false, rvc = true,
    elf = "" }

fun parseArgs (args : string list) : options =
  let
    fun go (o' as {trace, traceMemReads, asm, maxInsts, pcStart, sigFile,
                   tohostExit, rvc, elf} : options) l =
      case l of
         [] => o'
       | "--trace" :: r =>
           go {trace = true, traceMemReads = traceMemReads, asm = asm,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = sigFile,
               tohostExit = tohostExit, rvc = rvc, elf = elf} r
       | "--trace-mem-reads" :: r =>
           go {trace = trace, traceMemReads = true, asm = asm,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = sigFile,
               tohostExit = tohostExit, rvc = rvc, elf = elf} r
       | "--no-asm" :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = false,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = sigFile,
               tohostExit = tohostExit, rvc = rvc, elf = elf} r
       | "--max-insts" :: n :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = asm,
               maxInsts = parseNum n, pcStart = pcStart,
               sigFile = sigFile, tohostExit = tohostExit, rvc = rvc,
               elf = elf} r
       | "--pc-start" :: n :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = asm,
               maxInsts = maxInsts, pcStart = SOME (parseNum n),
               sigFile = sigFile, tohostExit = tohostExit, rvc = rvc,
               elf = elf} r
       | "--signature" :: f :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = asm,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = SOME f,
               tohostExit = tohostExit, rvc = rvc, elf = elf} r
       | "--tohost-exit" :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = asm,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = sigFile,
               tohostExit = true, rvc = rvc, elf = elf} r
       | "--no-c" :: r =>
           go {trace = trace, traceMemReads = traceMemReads, asm = asm,
               maxInsts = maxInsts, pcStart = pcStart, sigFile = sigFile,
               tohostExit = tohostExit, rvc = false, elf = elf} r
       | "-h" :: _ => (oprint usage; exitWith 0)
       | "--help" :: _ => (oprint usage; exitWith 0)
       | x :: r =>
           if String.isPrefix "-" x then
             raise Usage ("unknown option, or option without its argument: " ^ x)
           else if elf <> "" then raise Usage ("more than one ELF file: " ^ x)
           else go {trace = trace, traceMemReads = traceMemReads, asm = asm,
                    maxInsts = maxInsts, pcStart = pcStart,
                    sigFile = sigFile, tohostExit = tohostExit,
                    rvc = rvc, elf = x} r
    val opts = go defaultOptions args
  in
    if #elf opts = "" then raise Usage "no ELF file given" else opts
  end

(* ------------------------------------------------------------------------
   ELF loading
   ------------------------------------------------------------------------ *)

type loaded = { entry : IntInf.int, symbols : (string * IntInf.int) list }

val EM_RISCV = 243

(* e_machine: the little-endian 16-bit field at offset 18 of the ELF
   header (lib/Elf's header record does not carry it). *)
fun elfMachine (file : string) : int =
  let
    val strm = BinIO.openIn file
    val v = BinIO.inputN (strm, 20) handle e => (BinIO.closeIn strm; raise e)
    val () = BinIO.closeIn strm
  in
    if Word8Vector.length v < 20 then ~1
    else Word8.toInt (Word8Vector.sub (v, 18)) +
         256 * Word8.toInt (Word8Vector.sub (v, 19))
  end

(* Load every PT_LOAD segment at its physical address, zero-filling
   memsz - filesz bytes, as sail-riscv's ELF loader does.  MEM8 reads as
   zero until written, so only the part of that range that an earlier
   segment has already written needs zeroing (a large .bss would otherwise
   cost one Map.update per byte).  An ELF without section headers
   (e_shnum = 0) is loaded with no symbols, like a stripped one. *)
fun loadElf (file : string) : loaded =
  let
    val elf = Elf.openElf file
    val () = if Elf.isELFFile elf then ()
             else raise LoadError (file ^ " is not an ELF file")
    val hdr = Elf.getHeader elf
    val () = if #class hdr = Elf.BIT_64 andalso #endian hdr = Elf.LITTLE then ()
             else raise LoadError (file ^ " is not a little-endian ELF64 file")
    val () = if elfMachine file = EM_RISCV then ()
             else raise LoadError (file ^ " is not a RISC-V ELF file")
    fun zero (a, hi) =
      if a >= hi then () else (setMemByte (a, 0); zero (a + 1, hi))
    val loadedRanges = ref ([] : (IntInf.int * IntInf.int) list)
    fun zeroWritten (lo, hi) =
      List.app
        (fn (b, e) => zero (IntInf.max (lo, b), IntInf.min (hi, e)))
        (!loadedRanges)
    fun loadSeg (s : Elf.segm) =
      if #ptype s <> Elf.PT_LOAD then ()
      else
        let
          val base = #paddr s
          val bytes = #bytes s
          val filesz = Word8Vector.length bytes
        in
          if IntInf.fromInt filesz > #memsz s
            then raise LoadError (file ^ ": segment file size exceeds memory size")
          else ();
          Word8Vector.appi
            (fn (i, b) => setMemByte (base + IntInf.fromInt i, Word8.toLargeInt b))
            bytes;
          zeroWritten (base + IntInf.fromInt filesz, base + #memsz s);
          loadedRanges := (base, base + #memsz s) :: !loadedRanges
        end
    val () = List.app loadSeg (Elf.getSegments elf hdr)
    val syms =
      if #shnum hdr = 0 then []
      else Elf.getSymbols elf hdr
             (Elf.getNamedSections elf hdr (Elf.getSections elf hdr))
    (* As sail-riscv's ELF::symbols(): keep only defined (st_shndx <>
       SHN_UNDEF) symbols of type STT_NOTYPE, STT_OBJECT, STT_FUNC or
       STT_COMMON. *)
    fun keep (s : Elf.symb) =
      #syshndx s <> 0 andalso
      List.exists (fn t => t = IntInf.andb (#syinfo s, 0xf)) [0, 1, 2, 5]
    val named =
      List.mapPartial
        (fn (s : Elf.symb) =>
            case #syname s of
               SOME n => if keep s then SOME (Substring.string n, #syvalue s)
                         else NONE
             | NONE => NONE) syms
  in
    { entry = #entry hdr, symbols = named }
  end

(* When several kept symbols have the name, the LAST one in the symbol
   table wins, as in sail-riscv (whose std::map assignment overwrites).
   Local symbols precede global ones in an ELF symbol table, so a global
   beats a local of the same name from another object. *)
fun lookupSym (l : loaded) name =
  Option.map #2 (List.find (fn (n, _) => n = name) (List.rev (#symbols l)))

(* ------------------------------------------------------------------------
   Model state access
   ------------------------------------------------------------------------ *)

fun gprVal i = u (riscv.gpr (BitsN.fromInt (IntInf.fromInt i, 5)))
fun fprVal i = u (riscv.fpr (BitsN.fromInt (IntInf.fromInt i, 5)))
(* The value traced for CSR n: what a CSR read gives, except that mepc and
   sepc are traced as stored.  With misa.C = 0 their bit 1 reads as zero
   but stays stored (design D44); sail logs the stored value, and a write
   of misa.C is not a write of mepc or sepc. *)
fun csrVal (n : int) =
  case n of
     0x341 => u (#mepc (riscv.MCSR ()))
   | 0x141 => u (#sepc (riscv.SCSR ()))
   | _ => u (riscv.CSRMap (BitsN.fromInt (IntInf.fromInt n, 12)))
fun modelCsrName (n : int) = riscv.csrName (BitsN.fromInt (IntInf.fromInt n, 12))
fun csrDefined (n : int) = riscv.is_CSR_defined (BitsN.fromInt (IntInf.fromInt n, 12))

(* (name, number) for every CSR number that csrName knows *)
val csrNumbers : (string * int) list ref = ref []

(* All numbers with this model name.  riscv.spec's csrName gives some
   numbers the same name (0x144 and 0x344 are both "mip"), so there can be
   more than one. *)
fun csrNumbersOf name =
  List.mapPartial (fn (s, n) => if s = name then SOME n else NONE) (!csrNumbers)

(* The name used in the trace: the model's name, or name@0xNNN when the
   model gives that name to more than one number. *)
fun csrName (n : int) =
  let
    val nm = modelCsrName n
  in
    case csrNumbersOf nm of
       [_] => nm
     | [] => nm
     | _ => nm ^ "@0x" ^ hexDigits 3 (IntInf.fromInt n)
  end

(* Counters and timers change on every step and are not watched for
   implicit writes; explicit CSR-instruction writes to them are still
   traced: cycle, time, instret, mcycle, minstret. *)
fun isCounter n =
  (0xC00 <= n andalso n <= 0xC02) orelse n = 0xB00 orelse n = 0xB02

(* The watched CSRs, each with its value after the previous step. *)
val watched : (int * IntInf.int ref) list ref = ref []

fun initCsrTables () =
  let
    fun loop (n, names, watch) =
      if n > 0xFFF then (List.rev names, List.rev watch)
      else
        let
          val nm = modelCsrName n
          val names = if nm = "UNKNOWN" then names else (nm, n) :: names
          val watch =
            if csrDefined n andalso not (isCounter n) then
              (case (SOME (csrVal n) handle _ => NONE) of
                  SOME v => (n, ref v) :: watch
                | NONE => watch)
            else watch
        in
          loop (n + 1, names, watch)
        end
    val (names, watch) = loop (0, [], [])
  in
    csrNumbers := names;
    watched := watch;
    case List.filter (fn (nm, n) => length (csrNumbersOf nm) > 1
                                    andalso hd (csrNumbersOf nm) = n) names of
       [] => ()
     | dups =>
         warn ("riscv.spec's csrName gives one name to several CSRs (" ^
               String.concatWith "; "
                 (List.map (fn (nm, _) =>
                              nm ^ ": " ^ String.concatWith ", "
                                (List.map (fn m => "0x" ^ hexDigits 3 (IntInf.fromInt m))
                                   (csrNumbersOf nm))) dups) ^
               "); the trace writes these as name@0xNNN")
  end

(* ------------------------------------------------------------------------
   Model initialisation
   ------------------------------------------------------------------------ *)

fun initModel (rvc : bool, pc : IntInf.int) =
  ( riscv.totalCore := 1
  ; riscv.procID := BitsN.fromInt (0, BitsN.size (!riscv.procID))
  ; riscv.initIdent riscv.RV64I
  ; if rvc then ()
    else let
           val m = riscv.MCSR ()
         in
           riscv.write'MCSR
             (riscv.MachineCSR_misa_rupd
                (m, riscv.misa_C_rupd (#misa m, false)))
         end
  ; riscv.initMachine (!riscv.procID)
  ; riscv.initRegs pc
    (* boot convention, as sail-riscv's init_boot_requirements: a0 = mhartid,
       a1 = the device-tree address 0x1000 (design D72) *)
  ; riscv.write'gpr (BitsN.fromInt (0, 64), BitsN.fromInt (10, 5))
  ; riscv.write'gpr (BitsN.fromInt (0x1000, 64), BitsN.fromInt (11, 5))
  ; riscv.clear_logs () )

(* The model keeps the CLINT's mtime in memory and does not advance it
   (design D67); like sail-riscv with one instruction per tick, mtime
   advances by one after every step, trapping or not. *)
val MTIME_ADDR : IntInf.int = 0x200BFF8

fun tickMtime () =
  writeLE (MTIME_ADDR, 8, (readLE (MTIME_ADDR, 8) + 1) mod two64)

(* setupDelta in the spec only runs after a successful fetch, so clear the
   delta before every step to avoid reporting a previous step's store. *)
fun resetDelta (pc : BitsN.nbit) =
  riscv.write'Delta
    { addr = NONE, data1 = NONE, data2 = NONE, exc_taken = false,
      fetch_exc = false, fp_data = NONE, pc = pc,
      rinstr = riscv.Word (BitsN.fromInt (0, 32)), st_width = NONE }

(* ------------------------------------------------------------------------
   Log parsing
   ------------------------------------------------------------------------ *)

(* the text between the first "(" and the next ")" *)
fun inParens (s : string) : string option =
  let
    val (_, rest) = Substring.splitl (fn c => c <> #"(") (Substring.full s)
  in
    if Substring.isEmpty rest then NONE
    else
      let
        val (inside, close) =
          Substring.splitl (fn c => c <> #")") (Substring.triml 1 rest)
      in
        if Substring.isEmpty close then NONE else SOME (Substring.string inside)
      end
  end

fun regInParens s =
  case Option.mapPartial Int.fromString (inParens s) of
     SOME n => if 0 <= n andalso n < 32 then SOME n else NONE
   | NONE => NONE

fun lastToken s =
  case List.rev (String.tokens Char.isSpace s) of
     t :: _ => SOME t
   | [] => NONE

datatype logEvent =
    LogGPR of int
  | LogFPR of int
  | LogCSR of string
  | LogTrap of bool * int * bool  (* is interrupt, cause, taken into S-mode *)
  | LogAddrExc
  | LogOther

fun unparsed s = (warn ("cannot parse model log entry: " ^ s); LogOther)

(* "trapping from <p> to <q> at pc ...": is q S-mode? *)
fun trapToS s =
  case String.tokens Char.isSpace s of
     _ :: _ :: _ :: _ :: q :: _ => q = "S"
   | _ => false

(* The formats are those of log_w_gpr, log_w_fprs/log_w_fprd, log_w_csr,
   takeTrap and signalAddressException in riscv.spec. *)
fun classify ((lvl, s) : Nat.nat * string) : logEvent =
  if lvl = 2 andalso String.isPrefix "Reg " s then
    (case regInParens s of SOME n => LogGPR n | NONE => unparsed s)
  else if lvl = 2 andalso String.isPrefix "FPR " s then
    (case regInParens s of SOME n => LogFPR n | NONE => unparsed s)
  else if lvl = 2 andalso String.isPrefix "CSR (" s then
    (case inParens s of SOME nm => LogCSR nm | NONE => unparsed s)
  else if lvl = 1 andalso String.isPrefix "trapping from " s then
    (case Option.mapPartial Int.fromString (lastToken s) of
        SOME c => LogTrap (String.isSubstring "[intr]" s, c, trapToS s)
      | NONE => unparsed s)
  else if lvl = 1 andalso String.isPrefix "signalling address exception" s then
    LogAddrExc
  else LogOther

fun logHasTrap () =
  List.exists (fn (lvl, s) => lvl = 1 andalso String.isPrefix "trapping from " s)
    (!riscv.log)

(* ------------------------------------------------------------------------
   HTIF (tohost), following sail-riscv's htif_store (model/sys/platform.sail)
   ------------------------------------------------------------------------ *)

datatype htifResult = HtifNone | HtifExit of IntInf.int

val htifTohost = ref (0 : IntInf.int)
val htifCmdWrite = ref false
val htifPayloadWrites = ref 0

fun htifReset () = (htifTohost := 0; htifCmdWrite := false; htifPayloadWrites := 0)

(* A store of w bytes at a, whose data is now in memory, overlapping the
   8 bytes at tohost.  Both are physical addresses: a is the one that
   recordStore gives, which is translated, and tohost the symbol's, where
   the ELF is loaded; riscv-tests' -v environment stores to tohost through
   a virtual address.  console is where HTIF terminal output goes. *)
fun htifStore (tohost : IntInf.int, a : IntInf.int, w : int,
               console : TextIO.outstream) : htifResult =
  let
    val data = readLE (a, w)
    val ok =
      if w = 8 andalso a = tohost then
        ( htifCmdWrite := true
        ; htifPayloadWrites := !htifPayloadWrites + 1
        ; htifTohost := data
        ; true )
      else if w = 4 andalso a = tohost then
        ( if data = bitsOf (!htifTohost, 31, 0)
            then htifPayloadWrites := !htifPayloadWrites + 1
          else htifPayloadWrites := 1
        ; htifTohost := bitsOf (!htifTohost, 63, 32) * IntInf.pow (2, 32) + data
        ; true )
      else if w = 4 andalso a = tohost + 4 then
        ( if bitsOf (data, 15, 0) = bitsOf (!htifTohost, 47, 32)
            then htifPayloadWrites := !htifPayloadWrites + 1
          else htifPayloadWrites := 1
        ; htifCmdWrite := true
        ; htifTohost := data * IntInf.pow (2, 32) + bitsOf (!htifTohost, 31, 0)
        ; true )
      else
        ( warn ("store of " ^ Int.toString w ^ " bytes at " ^ hex16 a ^
                " overlaps tohost but is not an aligned 4- or 8-byte access; \
                \ignored by HTIF (sail-riscv raises a store access fault)")
        ; false )
  in
    if ok andalso ((!htifCmdWrite andalso !htifPayloadWrites > 0)
                   orelse !htifPayloadWrites > 2) then
      let
        val cmd = !htifTohost
        val device = bitsOf (cmd, 63, 56)
        val command = bitsOf (cmd, 55, 48)
        val payload = bitsOf (cmd, 47, 0)
      in
        if device = 0 then
          if bitsOf (payload, 0, 0) = 1 then HtifExit (payload div 2)
          else (warn "HTIF syscall-proxy commands are not supported; ignored";
                HtifNone)
        else if device = 1 then
          ( if command = 1 then
              ( TextIO.output1 (console, Char.chr (IntInf.toInt (bitsOf (payload, 7, 0))))
              ; TextIO.flushOut console )
            else if command = 0 then ()
            else warn ("unknown HTIF terminal command " ^ IntInf.toString command)
          ; htifReset ()
          (* acknowledge: a program polling tohost sees zero *)
          ; writeLE (tohost, 8, 0)
          ; HtifNone )
        else (warn ("unknown HTIF device " ^ IntInf.toString device); HtifNone)
      end
    else HtifNone
  end

(* ------------------------------------------------------------------------
   Decoding for the trace
   ------------------------------------------------------------------------ *)

(* as Next does it *)
fun decodeRaw (riscv.Half h) =
      if riscv.haveRVC () then riscv.DecodeRVC h else riscv.UnknownInstruction
  | decodeRaw (riscv.Word w) = riscv.Decode w

fun rawHex (riscv.Half h) = "0x" ^ hexDigits 4 (u h)
  | rawHex (riscv.Word w) = "0x" ^ hexDigits 8 (u w)

fun asmOf raw = riscv.instructionToString (decodeRaw raw) handle _ => "?"

(* bytes read by a load-type instruction (for --trace-mem-reads) *)
fun loadWidth (i : riscv.instruction) : int option =
  case i of
     riscv.Load (riscv.LB _) => SOME 1
   | riscv.Load (riscv.LBU _) => SOME 1
   | riscv.Load (riscv.LH _) => SOME 2
   | riscv.Load (riscv.LHU _) => SOME 2
   | riscv.Load (riscv.LW _) => SOME 4
   | riscv.Load (riscv.LWU _) => SOME 4
   | riscv.Load (riscv.LD _) => SOME 8
   | riscv.FPLoad (riscv.FLW _) => SOME 4
   | riscv.FPLoad (riscv.FLD _) => SOME 8
   | riscv.AMO (riscv.LR_W _) => SOME 4
   | riscv.AMO (riscv.LR_D _) => SOME 8
   | riscv.AMO (riscv.SC_W _) => NONE
   | riscv.AMO (riscv.SC_D _) => NONE
   | riscv.AMO (riscv.AMOSWAP_W _) => SOME 4
   | riscv.AMO (riscv.AMOADD_W _) => SOME 4
   | riscv.AMO (riscv.AMOXOR_W _) => SOME 4
   | riscv.AMO (riscv.AMOAND_W _) => SOME 4
   | riscv.AMO (riscv.AMOOR_W _) => SOME 4
   | riscv.AMO (riscv.AMOMIN_W _) => SOME 4
   | riscv.AMO (riscv.AMOMAX_W _) => SOME 4
   | riscv.AMO (riscv.AMOMINU_W _) => SOME 4
   | riscv.AMO (riscv.AMOMAXU_W _) => SOME 4
   | riscv.AMO _ => SOME 8
   | _ => NONE

(* ------------------------------------------------------------------------
   One step
   ------------------------------------------------------------------------ *)

type stepInfo =
  { trapped : bool,
    store : (IntInf.int * int) option }  (* address, bytes *)

fun storeOf (d : riscv.StateDelta) =
  case (#addr d, #st_width d) of
     (SOME a, SOME w) => SOME (u a, IntInf.toInt (u w))
   | _ => NONE

fun insertSorted (x : int, l : int list) =
  case l of
     [] => [x]
   | y :: r => if x = y then l else if x < y then x :: l else y :: insertSorted (x, r)

(* Run one step without tracing. *)
fun stepQuiet () : stepInfo =
  ( resetDelta (riscv.PC ())
  ; riscv.Next ()
  ; tickMtime ()
  ; {trapped = logHasTrap (), store = storeOf (riscv.Delta ())} )

(* Run one step and print its trace line. *)
fun stepTraced (opts : options, n : IntInf.int) : stepInfo =
  let
    val pc = riscv.PC ()
    val gprsBefore = Vector.tabulate (32, gprVal)
    val fprsBefore = Vector.tabulate (32, fprVal)
    val () = resetDelta pc
    val () = riscv.Next ()
    val d = riscv.Delta ()
    val events = List.map classify (List.rev (!riscv.log))

    (* registers: logged writes, plus changes the log missed (warned) *)
    fun regsWritten (logged, old, now, prefix) =
      let
        val fromLog = List.foldl insertSorted [] logged
        fun loop (i, acc) =
          if i = 32 then acc
          else if Vector.sub (old, i) <> now i
                  andalso not (List.exists (fn j => j = i) fromLog) then
            ( warn (prefix ^ Int.toString i ^ " changed without a log entry")
            ; loop (i + 1, insertSorted (i, acc)) )
          else loop (i + 1, acc)
      in
        loop (0, fromLog)
      end
    val gprs =
      List.filter (fn i => i <> 0)
        (regsWritten (List.mapPartial (fn LogGPR i => SOME i | _ => NONE) events,
                      gprsBefore, gprVal, "x"))
    val fprs =
      regsWritten (List.mapPartial (fn LogFPR i => SOME i | _ => NONE) events,
                   fprsBefore, fprVal, "f")

    (* CSRs: explicit (logged) and implicit (watched and changed) *)
    (* The log gives only the CSR's name.  If several CSRs have that name,
       use the number that writeCSR left in Delta.addr (a CSR write has no
       st_width); failing that, report all of them. *)
    val deltaCsr =
      case (#addr d, #st_width d) of
         (SOME a, NONE) => if u a < 4096 then SOME (IntInf.toInt (u a)) else NONE
       | _ => NONE
    val explicit =
      List.concat
        (List.map
           (fn LogCSR nm =>
                 (case csrNumbersOf nm of
                     [] => (warn ("model log names an unknown CSR " ^ nm); [])
                   | [c] => [c]
                   | l => (case deltaCsr of
                              SOME c => if List.exists (fn x => x = c) l then [c] else l
                            | NONE => l))
             | _ => []) events)
    val implicit =
      List.mapPartial
        (fn (c, r) =>
            let
              val v = csrVal c
            in
              if v <> !r then (r := v; SOME c) else NONE
            end) (!watched)
    val csrs = List.foldl insertSorted [] (explicit @ implicit)

    (* traps; a step that takes an interrupt fetches nothing *)
    val trap = List.find (fn LogTrap _ => true | _ => false) events
    val interrupt = case trap of SOME (LogTrap (true, _, _)) => true | _ => false
    val fetched = not (#fetch_exc d) andalso not interrupt
    val raw = #rinstr d

    (* memory *)
    val store = storeOf d
    (* LR.W/LR.D call no recordLoad; a successful LR sets ReserveLoad to
       its physical address and leaves memory unchanged, so read the value
       back. *)
    val load =
      if #traceMemReads opts andalso fetched then
        case (decodeRaw raw, riscv.ReserveLoad ()) of
           (riscv.AMO (riscv.LR_W _), SOME a) =>
              if Option.isSome trap then NONE else SOME (u a, 4, readLE (u a, 4))
         | (riscv.AMO (riscv.LR_D _), SOME a) =>
              if Option.isSome trap then NONE else SOME (u a, 8, readLE (u a, 8))
         | (i, _) =>
             (case (loadWidth i, #addr d, #data1 d) of
                 (SOME w, SOME a, SOME v) => SOME (u a, w, bitsOf (u v, 8 * w - 1, 0))
               | _ => NONE)
      else NONE


    fun field (name, v) = " " ^ name ^ "=" ^ hex16 v
    val fields =
      List.map (fn i => field ("x" ^ Int.toString i, gprVal i)) gprs @
      List.map (fn i => field ("f" ^ Int.toString i, fprVal i)) fprs @
      List.map (fn c => field ("csr[" ^ csrName c ^ "]", csrVal c)) csrs @
      (case load of
          SOME (a, w, v) => [" mr[" ^ hex16 a ^ "]=0x" ^ hexDigits (2 * w) v]
        | NONE => []) @
      (case store of
          SOME (a, w) =>
            [" mw[" ^ hex16 a ^ "]=0x" ^ hexDigits (2 * w) (readLE (a, w))]
        | NONE => []) @
      (case trap of
          SOME (LogTrap (false, c, toS)) =>
            [" trap=" ^ Int.toString c,
             field ("tval", u (if toS then #stval (riscv.SCSR ())
                               else #mtval (riscv.MCSR ())))]
        | SOME (LogTrap (true, c, _)) => [" intr=" ^ Int.toString c]
        | _ => [])
    val comment =
      if not (#asm opts) then ""
      else if fetched then "  # " ^ asmOf raw
      else if interrupt then "  # interrupt"
      else "  # fetch failed"
  in
    oprint (String.concat
              (["S ", IntInf.toString n, " pc=", hex16 (u pc),
                " inst=", if fetched then rawHex raw else "-"] @
               fields @ [comment, "\n"]));
    tickMtime ();
    {trapped = Option.isSome trap, store = store}
  end

(* ------------------------------------------------------------------------
   Signature
   ------------------------------------------------------------------------ *)

(* riscv-arch-test format, as sail-riscv's --test-signature with the
   default granularity 4: one word per line, most significant byte first,
   lower-case hex. *)
fun writeSignature (file : string, b : IntInf.int, e : IntInf.int) =
  let
    val os = TextIO.openOut file
    fun loop a =
      if a >= e then ()
      else (TextIO.output (os, hexDigits 8 (readLE (a, 4)) ^ "\n"); loop (a + 4))
  in
    loop b;
    TextIO.closeOut os
  end

(* ------------------------------------------------------------------------
   Main loop
   ------------------------------------------------------------------------ *)

(* A run of this many steps that all trap, with no instruction retiring in
   between, makes no progress. *)
val TRAP_LOOP_LIMIT = 64

fun run (opts : options) =
  let
    val loaded = loadElf (#elf opts)
      handle LoadError s => raise LoadError s
           | e => raise LoadError ("cannot load " ^ #elf opts ^ ": " ^ exnMessage e)
    val tohost = lookupSym loaded "tohost"
    val sigRange =
      case #sigFile opts of
         NONE => NONE
       | SOME f =>
           (case (lookupSym loaded "begin_signature",
                  lookupSym loaded "end_signature") of
               (SOME b, SOME e) => SOME (f, b, e)
             | _ => raise LoadError ("--signature: " ^ #elf opts ^
                                 " has no begin_signature/end_signature symbols"))
    val pc0 = Option.getOpt (#pcStart opts, #entry loaded)
    val () = initModel (#rvc opts, pc0)
    val () = if #trace opts then initCsrTables () else ()
    val () = if Option.isSome tohost then ()
             else eprint "riscv-sim: no tohost symbol; HTIF disabled\n"
    val console = if #trace opts then TextIO.stdErr else TextIO.stdOut
    val () =
      if #trace opts then
        ( oprint ("# riscv-sim trace v1: " ^ #elf opts ^ "\n")
        ; oprint ("# initial pc=" ^ hex16 pc0 ^
                  (if #rvc opts then "" else ", C disabled") ^ "\n")
        ; List.app
            (fn (c, r) => oprint ("I csr[" ^ csrName c ^ "]=" ^ hex16 (!r) ^ "\n"))
            (!watched) )
      else ()

    fun finish (status, msg) =
      ( case sigRange of
           SOME (f, b, e) =>
             if status = EXIT_MODEL_ERROR then () else writeSignature (f, b, e)
         | NONE => ()
      ; eprint ("riscv-sim: " ^ msg ^ "\n")
      ; exitWith status )

    fun htifExit (code, steps) =
      if code = 0 then finish (EXIT_PASS, "PASS after " ^ steps ^ " steps")
      else finish (EXIT_FAIL, "FAIL: tohost exit code " ^ IntInf.toString code ^
                              " (test " ^ IntInf.toString code ^ ") after " ^
                              steps ^ " steps")

    fun modelError (n, pc, what) =
      ( if #trace opts then
          oprint ("# step " ^ IntInf.toString n ^ " raised " ^ what ^ "\n")
        else ()
      ; finish (EXIT_MODEL_ERROR, what ^ " at step " ^ IntInf.toString n ^
                                  ", pc " ^ hex16 pc) )

    fun checkTohost (store, steps) =
      case (tohost, store) of
         (SOME t, SOME (a, w)) =>
           if a < t + 8 andalso a + IntInf.fromInt w > t then
             (* --tohost-exit: the HTIF logic still runs (so complete
                console commands are printed and acknowledged), and then
                any non-zero value left in tohost whose device field
                (bits 63:56) is 0 ends the run *)
             (case htifStore (t, a, w, console) of
                 HtifExit code => htifExit (code, steps)
               | HtifNone =>
                   if not (#tohostExit opts) then ()
                   else
                     let
                       val v = readLE (t, 8)
                     in
                       if v = 0 orelse bitsOf (v, 63, 56) <> 0 then ()
                       else if v mod 2 = 1 then htifExit (v div 2, steps)
                       else finish (EXIT_FAIL, "FAIL: tohost = " ^ hex16 v ^
                                               " (even) after " ^ steps ^ " steps")
                     end)
           else ()
       | _ => ()

    fun loop (n : IntInf.int, trapRun : int) =
      if #maxInsts opts > 0 andalso n >= #maxInsts opts then
        finish (EXIT_MAX_INSTS, "stopped by --max-insts after " ^
                                IntInf.toString n ^ " steps, pc " ^
                                hex16 (u (riscv.PC ())))
      else
        let
          val pc = u (riscv.PC ())
          val info =
            (if #trace opts then stepTraced (opts, n) else stepQuiet ())
            handle riscv.UNDEFINED s => modelError (n, pc, "UNDEFINED \"" ^ s ^ "\"")
                 | riscv.INTERNAL_ERROR s =>
                     modelError (n, pc, "INTERNAL_ERROR \"" ^ s ^ "\"")
                 | e => modelError (n, pc, "exception " ^ exnMessage e)
          val steps = IntInf.toString (n + 1)
          val trapRun = if #trapped info then trapRun + 1 else 0
        in
          (* the model's termination flag (nothing in the model sets it: HTIF
             belongs to the emulator) *)
          if !riscv.done then htifExit (Nat.toInt (riscv.exitCode ()), steps)
          else ();
          (* memory-mapped tohost *)
          checkTohost (#store info, steps);
          if trapRun >= TRAP_LOOP_LIMIT then
            finish (EXIT_TRAP_LOOP, "trap loop: " ^ Int.toString trapRun ^
                                    " consecutive steps trapped, the last at pc " ^
                                    hex16 pc ^ " (step " ^ IntInf.toString n ^ ")")
          else ();
          loop (n + 1, trapRun)
        end
  in
    loop (0, 0)
  end

fun main () =
  run (parseArgs (CommandLine.arguments ()))
  handle Usage s => (eprint ("riscv-sim: " ^ s ^ "\n\n" ^ usage); exitWith EXIT_USAGE)
       | LoadError s => (eprint ("riscv-sim: " ^ s ^ "\n"); exitWith EXIT_USAGE)

end
