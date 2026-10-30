/* Work-around for a Poly/ML Foreign-interface problem (seen with Poly/ML
   5.9.2 on x86-64 Linux): calls to C functions that return the 16-byte
   struct fp64 {uint32_t mxcsr; uint64_t result;} of L3's sse_float.c, which
   the x86-64 SysV ABI returns in RAX:RDX, come back with the result in the
   wrong field and garbage in the other.  FP32 results (an 8-byte struct,
   returned in RAX alone) are fine.

   These wrappers return the result as a plain uint64_t and keep the MXCSR
   value for shim_last_mxcsr().  They are compiled together with
   $(L3LIBDIR)/sse_float.c into sse_fp64_shim.so, and lib/SSEFix.sml rebinds
   SSE.fp_{add,sub,mul,div,sqrt,fma,fms}64 to them before FP64.sml is
   loaded.  Single-threaded use only. */

#include <stdint.h>
#include "sse_float.h"

static uint32_t last_mxcsr;

uint32_t shim_last_mxcsr (void) { return last_mxcsr; }

#define SHIM_BINOP(f)                                              \
  uint64_t shim_##f (uint32_t mode, uint64_t a, uint64_t b)        \
  { fp64 r = f (mode, a, b); last_mxcsr = r.mxcsr; return r.result; }

#define SHIM_TRIOP(f)                                                     \
  uint64_t shim_##f (uint32_t mode, uint64_t a, uint64_t b, uint64_t c)   \
  { fp64 r = f (mode, a, b, c); last_mxcsr = r.mxcsr; return r.result; }

SHIM_BINOP (fp_add64)
SHIM_BINOP (fp_sub64)
SHIM_BINOP (fp_mul64)
SHIM_BINOP (fp_div64)
SHIM_TRIOP (fp_fma64)
SHIM_TRIOP (fp_fms64)

uint64_t shim_fp_sqrt64 (uint32_t mode, uint64_t a)
{ fp64 r = fp_sqrt64 (mode, a); last_mxcsr = r.mxcsr; return r.result; }
