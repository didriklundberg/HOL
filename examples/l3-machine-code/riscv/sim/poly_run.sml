(* Build driver for riscv-sim under Poly/ML (polyc).

   Loads lib/IntInfFix.sml, the L3 runtime library, the L3-generated model
   (../model/riscv.sig and riscv.sml), the ELF reader in lib/ and the
   harness sim.sml, in that order.  Adapted from l3riscv's
   src/sml/poly_run.sml (BSD licence, see lib/LICENSE.l3riscv).

   Environment variables read at build time:
     L3LIBDIR         the L3 lib directory (BitsN.sml, FP64.sml,
                      sse_float.dynlib, ...); required
     RISCV_MODEL_DIR  directory holding riscv.sig and riscv.sml
                      (default: ../model relative to this file)
     SSE_SHIM         absolute path of sse_fp64_shim.so (built by the
                      Makefile from lib/sse_fp64_shim.c); required, see
                      lib/SSEFix.sml

   At run time the L3 library looks for sse_float.dynlib in $L3LIBDIR if
   that is set, otherwise in the L3LIBDIR given at build time. *)

structure SimBuild =
struct
  fun fail s =
    (TextIO.output (TextIO.stdErr, "poly_run.sml: " ^ s ^ "\n");
     OS.Process.exit OS.Process.failure)

  val here =
    case PolyML.getUseFileName () of
       SOME f => (case OS.Path.dir f of "" => "." | d => d)
     | NONE => "."

  val l3lib =
    case OS.Process.getEnv "L3LIBDIR" of
       SOME s => s
     | NONE => fail "L3LIBDIR is not set"

  val sseShim =
    case OS.Process.getEnv "SSE_SHIM" of
       SOME s => s
     | NONE => fail "SSE_SHIM is not set"

  val modeldir =
    case OS.Process.getEnv "RISCV_MODEL_DIR" of
       SOME d => d
     | NONE => OS.Path.concat (here, "../model")

  fun readable p = OS.FileSys.access (p, [OS.FileSys.A_READ])

  fun useFile dir f =
    let
      val p = OS.Path.concat (dir, f)
    in
      if readable p then PolyML.use p else fail ("missing " ^ p)
    end

  (* Load s.sig and then s.sml, whichever exist (L3's library has some
     structures without a .sig and the SSE signature without a .sml). *)
  fun useSigSml dir s =
    let
      val sg = readable (OS.Path.concat (dir, s ^ ".sig"))
      val sm = readable (OS.Path.concat (dir, s ^ ".sml"))
    in
      if sg orelse sm then
        ( if sg then useFile dir (s ^ ".sig") else ()
        ; if sm then useFile dir (s ^ ".sml") else () )
      else fail ("neither " ^ s ^ ".sig nor " ^ s ^ ".sml in " ^ dir)
    end
end;

(* FP64.sml and friends refer to these. *)
structure Real64           = LargeReal;
structure PackReal64Little = PackRealLittle;

(* Correct IntInf.~>> for negative bignums (lib/IntInfFix.sml), before
   anything else uses IntInf. *)
val () = SimBuild.useFile (OS.Path.concat (SimBuild.here, "lib")) "IntInfFix.sml";

val () =
  List.app (SimBuild.useSigSml SimBuild.l3lib)
    ["IntExtra", "Nat", "Set", "L3", "Bitstring", "BitsN", "Ptree", "Map",
     "MutableMapFunctor", "MutableMap16", "Runtime"];

val () = L3.setLibDir SimBuild.l3lib;

val () =
  List.app (SimBuild.useSigSml SimBuild.l3lib) ["SSE", "PolySSE"];

(* Work around struct returns from sse_float.dynlib (lib/SSEFix.sml). *)
val () = SimBuild.useFile (OS.Path.concat (SimBuild.here, "lib")) "SSEFix.sml";

val () =
  List.app (SimBuild.useSigSml SimBuild.l3lib) ["FP", "FP32", "FP64", "FPConvert"];

val () = SimBuild.useSigSml SimBuild.modeldir "riscv";

val () = SimBuild.useSigSml (OS.Path.concat (SimBuild.here, "lib")) "Elf";

val () = SimBuild.useFile SimBuild.here "sim.sml";

(* polyc makes an executable whose entry point is `main`. *)
fun main () = Sim.main ();
