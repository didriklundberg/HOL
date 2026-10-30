(* Rebinds the 64-bit operations of L3's SSE structure (PolySSE.sml) to the
   wrappers in sse_fp64_shim.c; see the comment there for why.  Loaded by
   poly_run.sml after L3's PolySSE.sml and before FP64.sml.  The MXCSR
   decoding and rounding-mode numbering are those of PolySSE.sml. *)

structure SSE :> SSE =
struct
  open SSE

  local
    open Foreign

    val lib = loadLibrary SimBuild.sseShim
    fun sym s = getSymbol lib ("shim_" ^ s)

    val last_mxcsr = buildCall0 (sym "last_mxcsr", (), cUint32)

    fun decode_mxcsr mxcsr =
      let
        val m = Word32.fromInt mxcsr
      in
        { Precision    = Word32.andb (m, 0w32) = 0w32
        , Underflow    = Word32.andb (m, 0w16) = 0w16
        , Overflow     = Word32.andb (m, 0w8) = 0w8
        , DivideByZero = Word32.andb (m, 0w4) = 0w4
        , InvalidOp    = Word32.andb (m, 0w1) = 0w1
        }
      end

    val rm =
      fn IEEEReal.TO_NEAREST => 0
       | IEEEReal.TO_NEGINF => 1
       | IEEEReal.TO_POSINF => 2
       | IEEEReal.TO_ZERO => 3

    fun result r = (decode_mxcsr (last_mxcsr ()), Word64.fromLargeInt r)

    fun monop s =
      let
        val f = buildCall2 (sym s, (cUint32, cUint64Large), cUint64Large)
      in
        fn (m, a) => result (f (rm m, a))
      end

    fun binop s =
      let
        val f = buildCall3 (sym s, (cUint32, cUint64Large, cUint64Large),
                            cUint64Large)
      in
        fn (m, a, b) => result (f (rm m, a, b))
      end

    fun triop s =
      let
        val f = buildCall4 (sym s, (cUint32, cUint64Large, cUint64Large,
                                    cUint64Large), cUint64Large)
      in
        fn (m, a, b, c) => result (f (rm m, a, b, c))
      end
  in
    val fp_add64  = binop "fp_add64"
    val fp_sub64  = binop "fp_sub64"
    val fp_mul64  = binop "fp_mul64"
    val fp_div64  = binop "fp_div64"
    val fp_sqrt64 = monop "fp_sqrt64"
    val fp_fma64  = triop "fp_fma64"
    val fp_fms64  = triop "fp_fms64"
  end
end;
