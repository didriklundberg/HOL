(* Work-around for a Poly/ML 5.9.2 bug: IntInf.~>> of a negative value that
   is not a short (tagged) integer, i.e. below -2^62 on 64-bit Poly/ML, rounds
   toward zero instead of down, and gives 0 instead of ~1 when every
   magnitude bit is shifted out; for example IntInf.~>> (~2^63, 0w64) = 0.
   The RTS function PolyShiftRightArbitrary (libpolyml/arb.cpp) shifts the
   magnitude and keeps the sign.  Fixed upstream for Poly/ML issue #243
   (master 64eb08b0, branch fixes-5.9.2 ccd3e371, December 2025), but not in
   the 5.9.2 release.

   Loaded by poly_run.sml before L3's library, so that the library, the model
   and the harness all see this IntInf.  L3's library and the model only
   shift non-negative values (BitsN payloads, map keys), so this is a
   safeguard rather than a fix of a known wrong result.  For i < 0,
   floor (i / 2^n) = ~(floor ((~i - 1) / 2^n)) - 1, and the shift of the
   non-negative ~i - 1 is correct. *)

structure IntInf =
struct
  open IntInf
  fun op ~>> (i : int, n : Word.word) : int =
    if i >= 0 then IntInf.~>> (i, n) else ~ (IntInf.~>> (~ i - 1, n)) - 1
end;
