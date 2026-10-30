# riscv-sim: running ELF files on the L3 RISC-V model

`riscv-sim` is a standalone emulator built from the SML export of
`../src/riscv.spec` (`../model/riscv.sml`, `riscv.sig`). It loads an ELF file,
runs it with the model's `Next` function, stops on the HTIF `tohost`
protocol, and can write a per-step trace. `compare.py` runs the same ELF on
[sail-riscv](https://github.com/riscv/sail-riscv), normalises sail's trace to
the same format and reports where the two differ. Together they are the
oracle check for the rewrite of the model (work package WP0.3 of the RISC-V
model plan).

Nothing here is used by the HOL build; `Holmake` does not look in this
directory.

## Building

Needs Poly/ML (`poly`, `polyc`; tested with 5.9.2), the runtime library of
[L3](https://acjf3.github.io/l3/) (tested with L3-2018-02-09), a C compiler,
and GNU make. The smoke tests also need `riscv64-unknown-elf-gcc`.

    make                     # builds ./riscv-sim
    make test                # builds and checks the smoke tests in tests/
    make compare             # compare.py against sail-riscv (needs SAIL)

Make variables:

| Variable | Default | |
|---|---|---|
| `L3LIBDIR` | `l3 --lib-path` if `l3` is on `PATH`, else `$(HOME)/Documents/riscv-tools/l3/L3-2018-02-09/lib` | L3's `lib` directory |
| `MODELDIR` | `../model` | where `riscv.sig` and `riscv.sml` are |
| `POLYC`, `CC` | `polyc`, `cc` | |
| `RISCV_PREFIX` | `riscv64-unknown-elf-` | for the smoke tests |
| `SAIL` | `$(HOME)/Documents/riscv-tools/sail-riscv/build/c_emulator/sail_riscv_sim` | for `make compare` |

The executable is called `riscv-sim` (not `riscv-sim.poly`, as l3riscv's
is), after the command it provides.

`polyc` prints every declaration it compiles; the Makefile keeps that in
`riscv-sim.log` and shows only errors and warnings. One warning is expected
(`riscv.sml`: "Matches are not exhaustive", in the generated `amotype`).

The executable loads two shared libraries at run time, by the absolute paths
they had at build time: `$(L3LIBDIR)/sse_float.dynlib` (L3's floating-point
code; `$L3LIBDIR` overrides the directory) and `sse_fp64_shim.so` in this
directory. Rebuild after moving either.

### The floating-point shim

With Poly/ML 5.9.2 on x86-64 Linux, L3's `PolySSE.sml` gets wrong results
for every double-precision operation it implements by calling C
(`fp_add64`, `fp_sub64`, `fp_mul64`, `fp_div64`, `fp_sqrt64`, `fp_fma64`,
`fp_fms64`): these functions return the 16-byte struct
`{uint32_t mxcsr; uint64_t result;}` in RAX:RDX, and through Poly's `Foreign`
interface the result arrives in the wrong field, with garbage in the other
(for example `fadd.d` of 1.5 and 2.25 gave `0x000075b8e3f59790`).
Single-precision results, an 8-byte struct, are correct. `lib/sse_fp64_shim.c`
wraps the seven functions so that they return the result as a plain
`uint64_t`, and `lib/SSEFix.sml` rebinds them in structure `SSE` before
`FP64.sml` is loaded. Without this every RV64D arithmetic instruction is
wrong; it is a problem of the host toolchain, not of the model.

## Running

    riscv-sim [--trace] [--trace-mem-reads] [--no-asm] [--max-insts N]
              [--pc-start ADDR] [--signature FILE] [--tohost-exit] [--no-c] <elf>

| Option | |
|---|---|
| `--trace` | write the trace (below) to stdout |
| `--trace-mem-reads` | also trace memory reads (`mr[...]` fields) |
| `--no-asm` | leave the `# disassembly` comments out of the trace |
| `--max-insts N` | stop after N steps (default 0: no limit) |
| `--pc-start ADDR` | start at ADDR instead of the ELF entry point |
| `--signature FILE` | at the end, write memory from symbol `begin_signature` up to `end_signature` to FILE |
| `--tohost-exit` | also stop at the first store that leaves a non-zero device-0 value in `tohost`, without waiting for a complete HTIF command (below) |
| `--no-c` | run with the C extension disabled |

Numbers are decimal or `0x` hexadecimal. Messages (pass/fail, warnings) go
to stderr, so that stdout is only the trace.

Exit status:

| Status | |
|---|---|
| 0 | HTIF exit with code 0 (riscv-tests: pass) |
| 1 | HTIF exit with code n ≠ 0; prints "test n" (riscv-tests: `TESTNUM`) |
| 2 | `--max-insts` reached |
| 3 | the model raised an exception (`UNDEFINED`, `INTERNAL_ERROR`, or any other SML exception from `Next`); prints the message, the step and the pc |
| 4 | trap loop: 64 consecutive steps trapped without retiring an instruction |
| 64 | bad command line, unreadable ELF, `--signature` without the symbols |

The signature is written on every exit except status 3 and 64.

### What the harness sets up

- **Memory**: every `PT_LOAD` segment is written to the model's byte memory
  `MEM8` at its physical address, in program-header order, and the
  `memsz - filesz` bytes after it read as zero, as with sail-riscv's
  loader. `MEM8` reads as zero until written, so only the part of that range
  an earlier segment has already written is zeroed explicitly (a large
  `.bss` costs nothing). Overlapping segments are allowed, the later one
  wins; sail-riscv refuses to load them. All other memory reads as zero;
  there are no devices and no address-range checks.
- **Symbols**: from the ELF's symbol table (`tohost`, `begin_signature`,
  `end_signature`), with sail-riscv's rule (`ELF::symbols()`): only defined
  symbols (`st_shndx` not `SHN_UNDEF`) of type `NOTYPE`, `OBJECT`, `FUNC` or
  `COMMON` count, and if several have the same name the last one in the
  table wins, so a global beats a local of that name (locals come first in
  an ELF symbol table). A stripped ELF, or one without section headers
  (`e_shnum` = 0), loads with no symbols, so HTIF is off.
- **ELF checks**: the file must be a little-endian ELF64 with `e_machine` =
  `EM_RISCV` (243); anything else is rejected with exit status 64, as sail
  rejects a non-RISC-V ELF.
- **Machine state**: `initIdent RV64I`, `initMachine 0`, `initRegs pc`, one
  hart. This leaves the model in M-mode with all GPRs and FPRs zero,
  `mstatus.FS` = Initial, `mtvec` = 0x100 (so traps from M-mode go to
  0x1c0, see `takeTrap`), and the C extension on. `--no-c` clears
  `mcpuid.C` after `initIdent`; the model then decodes no 16-bit instruction
  and requires 4-byte aligned fetch and jump targets (`haveRVC` in the
  spec).
- **HTIF**: if the ELF has a `tohost` symbol, every store that overlaps the
  8 bytes at `tohost` is passed through a copy of sail-riscv's `htif_store`
  (`model/sys/platform.sail` in sail): an 8-byte store, or a store to the
  upper word, or the same lower word written three times, completes a
  command. Device 0 with bit 0 set is exit with code `payload >> 1`; device 1
  command 1 writes a character (to stdout, or stderr with `--trace`) and
  clears `tohost`. So a riscv-tests `RVTEST_PASS` (`sw` of the lower word,
  then of the upper word) stops after the second store, as in sail.
  With `--tohost-exit` the same HTIF logic runs, and in addition the run
  stops at the first store to `tohost` after which `tohost` holds a
  non-zero value with device field (bits 63:56) 0: odd values are exit
  with code `value >> 1` as above, even values are failure. Values for
  other devices are left to HTIF, so console output written with one 8-byte
  store works; console output written as two 4-byte stores, lower word
  first, still looks like an even device-0 value after the first store and
  fails. The model's own
  HTIF, the `mtohost` CSR that `Next` polls, also ends the run (it sets
  `done` at the start of the step after the CSR write, which therefore
  still executes).
- **Timer**: whatever the model does (`tickClock`, `checkTimers`): `mip.MTIP`
  and `STIP` are set once the clock passes `mtimecmp` = 0, which happens at
  step 200. Interrupts stay disabled unless the program enables them.

## Trace format

One line per step, that is per call of `Next`: an instruction that retires
or traps, or a failed fetch. The fields of a step line are separated by
single spaces, and nothing after ` # ` is significant.

    S <n> pc=0x<16 hex> inst=<instruction> <effect>... [# <disassembly>]

- `<n>`: step number from 0, the same numbering as sail's `[n]`.
- `pc`: the address the step fetched from (not the next pc).
- `inst`: `0x` and 4 hex digits for a 16-bit instruction, 8 for a 32-bit
  one, or `-` if the fetch failed.

Effects, always in this order:

| Field | Meaning |
|---|---|
| `x<i>=0x<16 hex>` | GPR `i` written (also with an unchanged value); never `x0`; ascending `i` |
| `f<i>=0x<16 hex>` | FPR `i` written, its whole 64-bit value after the step; ascending `i` |
| `csr[<name>]=0x<16 hex>` | CSR written, its value after the step; ascending CSR number |
| `mr[0x<16 hex>]=0x<2w hex>` | memory read of w bytes at that address (only with `--trace-mem-reads`) |
| `mw[0x<16 hex>]=0x<2w hex>` | memory write of w bytes; the data as a little-endian number, as sail prints it |
| `trap=<cause>` | the step took an exception with this `mcause` code (decimal) |
| `tval=0x<16 hex>` | after `trap=`, the trap value, when the model has one (below) |
| `intr=<cause>` | an interrupt was taken at the end of the step |

All hex digits are lower case. Other lines:

- `I csr[<name>]=0x<16 hex>`: the value of a watched CSR (below) before
  step 0; there is one such line per watched CSR, before the first `S`
  line. `compare.py` uses them as the model's initial CSR state.
- `# ...`: comments: a header, and `# step <n> raised <exception>` before an
  exit with status 3.

CSR names are those of `csrName` in `riscv.spec` (priv 1.7: `mbadaddr`,
`mcpuid`, `sptbr`, ...). Where `csrName` gives one name to several numbers
the trace writes `name@0xNNN`: `0x144` and `0x344` are both called `mip`, and
several counter shadows have the names of the counters they shadow (a
warning lists them all; these are bugs in `csrName`).

Example (the floating-point smoke test):

    S 7 pc=0x000000008000001c inst=0x02b57653 f12=0x400e000000000000 csr[sstatus]=0x8000000000003000 csr[mstatus]=0x8000000000003006  # FADD.D       fs12, fs10, fs11
    S 9 pc=0x0000000080000024 inst=0x00adb023 mw[0x0000000080002030]=0x400e000000000000  # SD           a0, s11, 0x0

(The disassembly is the model's `instructionToString`, which prints FPR
operands with odd names.)

### How effects are captured

The harness does not diff memory: the model's memory is a mutable map, so a
diff would mean copying or scanning it at every step. It uses what the
export already records about a step, and reads values back from the state
afterwards:

- **GPR, FPR, CSR writes**: the spec logs every write through the `GPR`,
  `FPRS`/`FPRD` and `CSR` components (`mark_log(LOG_REG, ...)`; the export
  keeps the log in `riscv.log`, cleared at the start of `Next`). That gives
  writes of unchanged values too, as sail reports them. The register number
  comes from the log text, the value from the state after the step. As a
  check, the GPR and FPR files are also diffed around each step; a change
  without a log entry is traced anyway and reported on stderr.
- **Implicit CSR writes** (trap entry, `mstatus.FS` from FP instructions,
  `fflags`) go to the CSR records directly, without a log entry. The harness
  watches every CSR that `is_CSR_defined` accepts, except the counters and
  timers (`cycle`, `time`, `instret` and their shadows and high halves,
  `mtime`, `stime`, `htime`), and traces those whose value changed in the
  step. A watched CSR rewritten with its old value implicitly is therefore
  not traced; `compare.py` compares CSRs as state for this reason.
- **Memory writes**: the spec's `StateDelta` record (`Delta`, set by
  `recordStore`) gives the address and width of the store, AMO or SC of the
  step; the data are read back from memory. The harness clears `Delta`
  before each step, because the spec only resets it after a successful
  fetch.
- **Memory reads** (`--trace-mem-reads`): address and value from
  `recordLoad`, width from the decoded instruction. `LR.W`/`LR.D` call no
  `recordLoad`; for an `LR` that does not trap the harness takes the address
  from `ReserveLoad`, which the `LR` has just set, and reads the 4 or 8
  bytes back from memory (an `LR` does not change memory).
- **Traps**: the log entry of `takeTrap`, `trapping from ... [exc] <cause>`
  or `[intr]`. `tval` is printed only when the step signalled an address
  exception (`signalAddressException`), and is then `mbadaddr`; for other
  exceptions the priv-1.7 model writes no trap value.

Addresses are those that the store or load computed (virtual addresses),
which equal physical ones while the model runs with `mstatus.VM` = Mbare, as
it always does from reset. Page-table updates by the model's page walker are
not traced.

## compare.py

    compare.py [options] <elf>

Runs `riscv-sim --trace` and `sail_riscv_sim --trace-instr --trace-reg
--trace-mem --trace-exception --trace-interrupt --trace-step --trace-output
FILE` on the ELF, normalises sail's trace, compares step by step and prints
the first divergences with the preceding steps of both traces. Exit status
0 if the traces agree, 1 on a divergence, 2 on a usage or tool error.
Python 3 standard library only.

A tool error is anything that means the two emulators were not both run on
the program, so that a comparison loop can tell it from a divergence:
riscv-sim exiting 64 (bad command line or an ELF it cannot load) or writing
no trace; sail writing no trace file (it rejected its options, `--config`
or the ELF before running; the last lines of its output are shown); either
trace having no steps (for example sail refusing to load overlapping
segments, or the model raising an exception at step 0); an unreadable
`--model-trace`/`--sail-trace` file. sail's own exit status is not used:
it is 1 also when the program fails its test, which is a result, not an
error.

Main options (`--help` lists all): `--riscv-sim`, `--sail` (default
`$SAIL_RISCV_SIM` or the path in the table above), `--sail-config FILE`,
`--sail-config-override FILE` (repeatable), `--max-insts N` (both
emulators; default 100000), `--max-divergences N` (default 5), `--context N`
(default 3), `--raw-sail`, `--mem-reads` (compare memory reads; also
the only case in which `mr[...]` fields appear in reports, `--save-traces`'
`sail.trace` and `--normalise` output, so that without it the sail side
lines up with `riscv-sim --trace`), `--no-csr`, `--ignore-csr
NAME[,NAME]`, `--csr-alias MODEL=SAIL`, `--save-traces DIR`, and
`--model-trace FILE`/`--sail-trace FILE` to compare saved traces, or
`--normalise SAILTRACE` to print a sail trace in the canonical format.

Per step it compares pc, instruction bits, GPR writes, FPR writes, memory
writes (and reads with `--mem-reads`), and trap or interrupt cause; the trap
value only when both traces have one. Different trace lengths are a
divergence.

CSRs are compared as **state**, because the two models write CSRs
implicitly in different places (sail logs `mstatus` at every FP register
write and `fflags`/`fcsr` at every FP operation; the model writes them
without a log). Both sides start from their known values (the model's `I`
lines; sail's are unknown until written); after each step, every CSR that
either side wrote in that step is compared, if both sides know a value for
it. A mismatch is reported once until one of the values changes. Model
names are mapped to sail's first (`mbadaddr`→`mtval`, `sbadaddr`→`stval`,
`sptbr`→`satp`, `mip@0x344`→`mip`, `mip@0x144`→`sip`; extend with
`--csr-alias`). `mip` and `sip` are ignored by default (`--no-default-ignores`
to compare them): sail's CLINT starts with `mtimecmp` = 0 and sets MTIP
before the first instruction, the model at step 200. CSRs that only one side
knows are listed at the end, not compared.

### The sail trace normaliser

Written from the sail-riscv sources at tag `2026-10-26-6f886e6`
(`c_emulator/riscv_callbacks_log.cpp`, `model/postlude/step.sail`,
`model/sys/sys_control.sail`) and checked against traces of that build on
the smoke tests and on `rv64uf-p-fadd` from riscv-tests:

- `--trace-step` ends every step with a blank line; a step is the block of
  lines before it. If the block has an `[n]` instruction line, n must equal
  the block's index (counting from 0). The `[n]` line need not come first:
  sail's first block starts with a `CSR mip (0x344) <- ...` write and
  `mem[X,...]` fetch reads, and a block for a taken interrupt has no `[n]`
  line at all.
- `[n] [M]: 0x<pc> (0x<inst>) <asm>   <symbol>+<offset>`: pc and instruction.
- `x<i> <- 0x...`, `f<i> <- 0x...`: register writes.
- `CSR <name> (0x<num>) <- 0x...`: CSR writes; `CSR ... -> ...` (reads) are
  dropped.
- `mem[<type>,0x<addr>] <- 0x<data>` / `-> 0x<data>`: memory write / read,
  width from the number of digits; type `X` (instruction fetch) is dropped.
- `trapping from ... to handle ...` and `handling exc#<name> ... | tval=0x...`
  mark an exception and give its trap value; `Handling interrupt: ...` and
  `handling int#...` mark an interrupt. The cause is the value sail then
  logs for `mcause` (or `scause`).
- `ret-ing from ...` and WFI/WRS wait messages are ignored; any other line is
  reported on stderr and ignored.
- A block without an instruction line (failed fetch) gets `inst=-` and the
  pc from the `mepc` write.

### Results so far

With sail's default configuration, `int.elf` (217 steps) and `rvc.elf` (118
steps) agree. `fp_fs.elf` (the FP test with `mstatus.FS` switched on, see
below) diverges where expected: the `mstatus` layout (priv 1.7 against 1.13),
and at step 37, `fcvt.l.d` with `rtz` of -22.125, where sail sets
`fflags.NX` and the model sets no flag. Scratch programs also showed that
the model does not NaN-box single-precision results (`flw` leaves the upper
32 bits of the FPR, sail writes `0xffffffff`), and that its `fmadd.d` rounds
twice (`dfn'FMADD_D` is `FP64.add` of `FP64.mul`; 2^-60 expected, 0
computed). All three are findings for the WP1 audit, not harness problems.

## Smoke tests

`tests/` has small self-checking programs in the style of riscv-tests
(`tests/test.h`): `gp` holds the number of the current check, failure stores
`(n << 1) | 1` to `tohost`, success stores 1, both as one 8-byte store.
Results are also stored in a signature region. None of them touches a CSR.

| Test | | Expected |
|---|---|---|
| `int.S` (rv64im) | sum over an 8-dword array, sign/zero-extending loads, sb/sh/sw/sd, mul/mulhu/div/rem including division by zero, shifts, `addiw` overflow, compares, call/return | exit 0, `int.sig.expected`, and the trace in `int.trace.expected` |
| `rvc.S` (rv64imac) | written with explicit `c.*` mnemonics: most RV64C instructions, including the stack-pointer forms, `c.addiw`/`c.addw`/`c.subw`, branches, `c.jalr`/`c.jr`, `c.lui` | exit 0, `rvc.sig.expected`; with `--no-c` exit 4 |
| `fp.S` (rv64imafd) | `fld`, `fadd.d`, `fmul.d`, `fcvt.d.l`, `fmadd.d`, `fcvt.l.d` (rtz), `fsd`, `fmv.x.d`, `feq.d` on values with exact results, and 0.1 + 0.2 | exit 0, `fp.sig.expected` |
| `fail.S` | fails check 3 on purpose | exit 1, "test 3" |

`make test` also checks that `--max-insts 10` gives exit 2, and prints the
trace of `fp.elf`. The expected signatures and `int.trace.expected` (CSR
fields left out) are sail-riscv's results too, so the files test the
harness, not only the model.

`fp.S` built with `-DENABLE_FS` (`build/fp_fs.elf`, used by `make
compare`) first sets bit 13 of `mstatus`: sail resets `mstatus.FS` to Off,
which makes FP instructions illegal there, while the model resets it to
Initial.

## Known not to work yet

- **Programs that use CSRs, and so riscv-tests and riscv-arch-test.** The
  model's privileged architecture is priv 1.7. The riscv-tests (`rv64ui-p-*`
  etc.) read `mhartid` at 0xF14, which the model does not define, at step 32
  and then end in a trap loop at 0x1c0 (exit 4); the arch tests trap at the
  first CSR the model does not have (`mideleg`, step 11) and loop likewise. This is expected until the privileged rework (WP2).
- **FP programs on sail** need `mstatus.FS` set first (above). FP exception
  flags are mostly not modelled: the spec drops the flags that L3's
  `FP64`/`FP32` operations return (`L3.snd`); only a few NaN cases call
  `setFP_Invalid`.
- **Interrupts** are taken by the model at the end of the step whose
  instruction retired (`intr=` on that line), by sail as a step of their own;
  `compare.py` will see the traces shift by one step after an interrupt.
- **Trap values**: the model has no `mtval`; `tval=` appears only for address
  exceptions, so for other traps the trap value is not compared.
- Only bare-metal, little-endian ELF64 files; no virtual memory in the trace
  (above); no devices other than HTIF; HTIF syscall-proxy requests (device 0
  with bit 0 clear) are ignored with a warning, as in sail.

## Files and provenance

| File | |
|---|---|
| `Makefile` | build, `test`, `compare` |
| `poly_run.sml` | loads the L3 library, `SSEFix.sml`, the model, `lib/Elf`, `sim.sml` under `polyc` |
| `sim.sml` | the harness (structure `Sim`) |
| `lib/Elf.sig`, `lib/Elf.sml` | ELF64 reader with symbol table |
| `lib/LICENSE.l3riscv` | the l3riscv licence (BSD) |
| `lib/sse_fp64_shim.c`, `lib/SSEFix.sml` | the floating-point work-around |
| `compare.py` | trace comparison with sail-riscv |
| `tests/` | smoke tests, linker script, expected results |

The structure of `sim.sml` and `poly_run.sml` follows `src/sml/model.sml` and
`src/sml/poly_run.sml` of [l3riscv](https://github.com/SRI-CSL/l3riscv)
(SRI International and University of Cambridge, BSD licence, commit
`a5ed4e10`, 2019-02-25), rewritten for this export: HOL's `riscv.spec`
derives from an older version of the same spec and has different state, CSR
names (priv 1.7) and memory (`MEM8`), and no `misa`, `mtval` or `satp`.
`lib/Elf.sig` is l3riscv's `src/sml/lib/Elf.sig` unchanged apart from a
provenance header comment, and
`lib/Elf.sml` its `Elf.sml` with two fixes (both marked): reads of segments
and sections no longer stop at Poly/ML's 100 KiB `readVec` limit, which had
silently truncated larger segments. Their licence headers are kept and refer
to `lib/LICENSE.l3riscv`. The HTIF logic in `sim.sml` follows sail-riscv's
`htif_store` (BSD-2-Clause).
