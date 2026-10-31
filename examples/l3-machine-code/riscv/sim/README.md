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
    make test                # builds and checks the smoke tests and regression programs in tests/
    make compare             # compare.py against sail-riscv on them (needs SAIL)
    make corpus              # the riscv-tests corpus on riscv-sim (needs CORPUS)
    make compare-corpus      # the corpus against sail-riscv (needs CORPUS, SAIL)
    make corpus-update       # rewrite tests/corpus.expected from both

Make variables:

| Variable | Default | |
|---|---|---|
| `L3LIBDIR` | `l3 --lib-path` if `l3` is on `PATH`, else `$(HOME)/Documents/riscv-tools/l3/L3-2018-02-09/lib` | L3's `lib` directory |
| `MODELDIR` | `../model` | where `riscv.sig` and `riscv.sml` are |
| `POLYC`, `CC` | `polyc`, `cc` | |
| `RISCV_PREFIX` | `riscv64-unknown-elf-` | for the smoke tests |
| `SAIL` | `$(HOME)/Documents/riscv-tools/sail-riscv/build/c_emulator/sail_riscv_sim` | for `make compare` and `make compare-corpus` |
| `SAIL_CONFIG` | `$(HOME)/Documents/riscv-tools/rv64gc_mu_pmp.json` | sail `--config-override` for the regression programs and the corpus; empty for sail's built-in configuration |
| `CORPUS` | `$(HOME)/Documents/riscv-tools/corpus/riscv-tests` | directory of prebuilt riscv-tests ELFs |
| `CORPUS_FLAGS` | | extra `corpus.py` options, e.g. `--pattern 'rv64ui-p-*'`, `-j 4`, `-v` |

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
wrong; it is a problem of the host toolchain, not of the model. The other
entry points (comparisons, conversions between integers, single and double,
round-to-integral) return a scalar or an 8-byte struct and are not affected:
with the shim, `FP64`, `FP32` and `FPConvert` agree with C's `fenv.h`/libm
in all four rounding modes, flags included (17,565 cases in WP1 batch A; the
only difference is the sign of the NaN that `mul_sub` propagates).

### The IntInf.~>> work-around

Poly/ML 5.9.2's `IntInf.~>>` rounds toward zero instead of down for a
negative value outside the short-integer range (below -2^62), for example
`IntInf.~>> (~2^63, 0w64)` gives 0 instead of ~1 (fixed upstream after the
release, Poly/ML issue #243). `lib/IntInfFix.sml` redefines `IntInf` with a
correct `~>>`, and `poly_run.sml` loads it before L3's library, so that the
library, the model and the harness all use it. L3's library and the model
only shift non-negative values, so this is a safeguard; it matters for code
added to the harness or for oracles written in SML, which should use
`IntInf.div` (or load this file) rather than the stock `~>>`.

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
| `--no-c` | run with the C extension disabled (`misa.C` = 0) |

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
  there are no address-range checks and no PMAs (`../doc/design-smode.md`
  §6 Q9), and the only devices are HTIF and the CLINT words (below).
- **Symbols**: from the ELF's symbol table (`tohost`, `begin_signature`,
  `end_signature`), with sail-riscv's rule (`ELF::symbols()`): only defined
  symbols (`st_shndx` not `SHN_UNDEF`) of type `NOTYPE`, `OBJECT`, `FUNC` or
  `COMMON` count, and if several have the same name the last one in the
  table wins, so a global beats a local of that name (locals come first in
  an ELF symbol table). A stripped ELF, or one without section headers
  (`e_shnum` = 0), loads with no symbols, so HTIF is off. Symbol values
  are taken as physical addresses, where the ELF is loaded, as in sail.
- **ELF checks**: the file must be a little-endian ELF64 with `e_machine` =
  `EM_RISCV` (243); anything else is rejected with exit status 64, as sail
  rejects a non-RISC-V ELF.
- **Machine state**: `initIdent RV64I`, `initMachine 0`, `initRegs pc`, one
  hart, then `a0` = 0 (`mhartid`) and `a1` = 0x1000 (the device-tree
  address), as sail-riscv's `init_boot_requirements` does (design D72).
  This leaves the model in M-mode with the other GPRs and all FPRs zero,
  `mstatus` = 0x0000000a00000000 (`FS` = Off, as in sail, so FP
  instructions are illegal until the program sets `FS`; `MPP` = U),
  `mtvec` = 0 in Direct mode (so every trap goes to address 0 until the
  program sets `mtvec`), every PMP entry off, and `misa` =
  0x800000000014112d (RV64IMAFDCSU), so the C extension is on. `--no-c`
  clears `misa.C` after `initIdent` (`initMachine` does not reset `misa`),
  as a write of `misa` could; the model then decodes no 16-bit instruction
  and requires 4-byte aligned fetch and jump targets (`haveRVC` in the
  spec, which reads `misa.C`), and bit 1 of `mepc`/`sepc` reads as zero.
- **HTIF**: if the ELF has a `tohost` symbol, every store whose physical
  address overlaps the 8 bytes at `tohost` is passed through a copy of
  sail-riscv's `htif_store`
  (`model/sys/platform.sail` in sail): an 8-byte store, or a store to the
  upper word, or the same lower word written three times, completes a
  command. Device 0 with bit 0 set is exit with code `payload >> 1`; device 1
  command 1 writes a character (to stdout, or stderr with `--trace`) and
  clears `tohost`. So a riscv-tests `RVTEST_PASS` (`sw` of the lower word,
  then of the upper word) stops after the second store, as in sail. The
  riscv-tests `-v` environment stores to `tohost` from S-mode through a
  virtual address; the store is recorded with its physical address
  (below), which is what HTIF matches, as in sail.
  With `--tohost-exit` the same HTIF logic runs, and in addition the run
  stops at the first store to `tohost` after which `tohost` holds a
  non-zero value with device field (bits 63:56) 0: odd values are exit
  with code `value >> 1` as above, even values are failure. Values for
  other devices are left to HTIF, so console output written with one 8-byte
  store works; console output written as two 4-byte stores, lower word
  first, still looks like an even device-0 value after the first store and
  fails. `tohost` in memory is the only HTIF: the model has none of its
  own (the priv-1.7 `mtohost` CSR is gone; HTIF belongs to the emulator,
  design D13).
- **Timer**: the CLINT's registers are words of the model's memory, as in
  sail-riscv's platform (design D67): `msip` at 0x2000000, `mtimecmp` at
  0x2004000 and `mtime` at 0x200bff8 (hart 0). The model reads them
  (`mip.MTIP` is `mtimecmp <= mtime`, `mip.MSIP` is `msip` bit 0) but
  never advances `mtime`; the harness adds one to `mtime` after every
  step, trapping or not, as sail does with one instruction per tick. The
  harness writes nothing else there, so all three start at 0 and `MTIP`
  is pending from step 0, as in sail. Interrupts stay disabled unless the
  program enables them (`mstatus.MIE`, `mie`).

## Trace format

One line per step, that is per call of `Next`: an instruction that retires
or traps, a failed fetch, or an interrupt taken. The fields of a step line
are separated by single spaces, and nothing after ` # ` is significant.

    S <n> pc=0x<16 hex> inst=<instruction> <effect>... [# <disassembly>]

- `<n>`: step number from 0, the same numbering as sail's `[n]`.
- `pc`: the address the step fetched from (not the next pc).
- `inst`: `0x` and 4 hex digits for a 16-bit instruction, 8 for a 32-bit
  one, or `-` if the fetch failed or the step took an interrupt (the
  comment is then `# fetch failed` or `# interrupt`).

Effects, always in this order:

| Field | Meaning |
|---|---|
| `x<i>=0x<16 hex>` | GPR `i` written (also with an unchanged value); never `x0`; ascending `i` |
| `f<i>=0x<16 hex>` | FPR `i` written, its whole 64-bit value after the step; ascending `i` |
| `csr[<name>]=0x<16 hex>` | CSR written, its value after the step; ascending CSR number |
| `mr[0x<16 hex>]=0x<2w hex>` | memory read of w bytes at that address (only with `--trace-mem-reads`) |
| `mw[0x<16 hex>]=0x<2w hex>` | memory write of w bytes; the data as a little-endian number, as sail prints it |
| `trap=<cause>` | the step took an exception with this cause code (decimal), into M-mode (`mcause`) or S-mode (`scause`) |
| `tval=0x<16 hex>` | after `trap=`, always: the trap value, `mtval` or `stval` after the trap |
| `intr=<cause>` | the step took an interrupt with this cause code (without bit 63) instead of fetching |

All hex digits are lower case. Other lines:

- `I csr[<name>]=0x<16 hex>`: the value of a watched CSR (below) before
  step 0; there is one such line per watched CSR, before the first `S`
  line. `compare.py` uses them as the model's initial CSR state.
- `# ...`: comments: a header, and `# step <n> raised <exception>` before an
  exit with status 3.

CSR names are those of `csrName` in `riscv.spec`, the priv-1.13 names that
sail uses (`mtval`, `stval`, `satp`, `misa`, ...). Should `csrName` give one
name to several numbers, the trace writes `name@0xNNN` for them and a
warning lists them; the current model gives every number its own name.

Example (the floating-point smoke test):

    S 7 pc=0x000000008000001c inst=0x00043507 f10=0x3ff8000000000000 csr[sstatus]=0x8000000200006000 csr[mstatus]=0x8000000a00006000  # FLD          fs10, fp, 0x0
    S 11 pc=0x000000008000002c inst=0x00adb023 mw[0x0000000080002030]=0x400e000000000000  # SD           a0, s11, 0x0

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
- **Implicit CSR writes** (trap entry and `xRET`, `mstatus.FS` from FP
  instructions, `fflags`, `mip` from the CLINT) go to the CSR records
  directly, without a log entry. The harness watches every CSR that
  `is_CSR_defined` accepts, except the counters and timers (`cycle`,
  `time`, `instret`, `mcycle`, `minstret`), and traces those whose value
  changed in the step. `mepc` and `sepc` are traced as stored, not as
  read: with `misa.C` = 0 their bit 1 reads as zero but stays stored
  (design D44), and sail logs the stored value. A watched CSR rewritten
  with its old value implicitly is therefore not traced; `compare.py`
  compares CSRs as state for this reason.
- **Memory writes**: the spec's `StateDelta` record (`Delta`, set by
  `recordStore`) gives the address and width of the store, AMO or SC of the
  step; the data are read back from memory. The harness clears `Delta`
  before each step, because the spec only resets it after a successful
  fetch.
- **Memory reads** (`--trace-mem-reads`): address and value from
  `recordLoad`, width from the decoded instruction. `LR.W`/`LR.D` call no
  `recordLoad`; for an `LR` that does not trap the harness takes the
  address from `ReserveLoad`, which the `LR` has just set to the physical
  address it reserved, and reads the 4 or 8 bytes back from memory (an
  `LR` does not change memory).
- **Traps**: the log entry of `takeTrap`, `trapping from <p> to <q> at pc
  ... [exc] <cause>` or `[intr]`. `takeTrap` writes a trap value for every
  exception (zero where the spec defines none), so `tval` is printed for
  every exception: `stval` when `q` is S (the exception was delegated),
  else `mtval`. A step that takes an interrupt does not fetch (the model
  checks for interrupts at the start of `Next`), so it has `inst=-` and no
  other effects than the trap-entry CSRs.

Memory addresses (`mr`, `mw`) are physical: the spec gives `recordLoad` and
`recordStore` the address after translation, which is what sail logs
(`../doc/design-smode.md` S30). The `pc` and the trap value are virtual
addresses. The page-table walk reads PTEs without a log entry or a
`StateDelta`, so they are never traced (S6), and under Svade it writes
none.

## compare.py

    compare.py [options] <elf>

Runs `riscv-sim --trace` and `sail_riscv_sim --trace-instr --trace-reg
--trace-mem --trace-exception --trace-interrupt --trace-step --trace-ptw
--trace-output FILE` on the ELF, normalises sail's trace, compares step by
step and prints the first divergences with the preceding steps of both
traces. Exit status 0 if the traces agree, 1 on a divergence, 2 on a usage
or tool error.
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
divergence. Memory accesses are compared by physical address, the pc and
the trap value as virtual addresses, which is how both emulators log them.
sail's reads of page-table entries are dropped (below): the model's are not
traced, and how many sail makes depends on its TLB, which the model does
not have (`../doc/design-smode.md` S4, S6).

CSRs are compared as **state**, because the two models write CSRs
implicitly in different places (sail logs `mstatus` at every FP register
write and `fflags`/`fcsr` at every FP operation; the model writes them
without a log). Both sides start from their known values (the model's `I`
lines; sail's are unknown until written); after each step, every CSR that
either side wrote in that step is compared, if both sides know a value for
it. A mismatch is reported once until one of the values changes. Model
names are mapped to sail's first; the model now uses sail's names, and the
built-in aliases (`mbadaddr`→`mtval`, `sbadaddr`→`stval`, `sptbr`→`satp`,
`mip@0x344`→`mip`, `mip@0x144`→`sip`) only matter for traces of the
earlier priv-1.7 model; extend them with `--csr-alias`. `sstatus`, `sie`
and `sip` are views of `mstatus`, `mie` and `mip`; sail logs only the one
an instruction (or trap entry, or an `xRET`) writes, so when a step's sail
log has one of a pair and not the other, compare.py forgets sail's value
of the other, which is stale, until sail logs it again. `sie` and `sip`
also change with `mideleg`, which restricts them, so when sail logs
`mideleg` without one of them, compare.py forgets its value of that one
too. `mip` and `sip` are
ignored by default (`--no-default-ignores` to compare them), because the
two emulators drive them from timers of their own; both now start with
`mtimecmp` = 0 and so with MTIP set before the first instruction, and they
agree on the riscv-tests below also with `--no-default-ignores`.
CSRs that only one side writes are listed in a note, not compared. `satp`
and `menvcfg` are compared like the others: riscv-sim watches every CSR
that `is_CSR_defined` accepts, and sail logs every write of them.

`fflags`, `frm` and `fcsr` are views of one register, but sail logs a CSR
instruction's write only under the name the instruction used (and `fflags`
and `fcsr` when an FP instruction accrues flags), so after a program writes
one of them compare.py's copy of the others can be stale and report a false
divergence. For FP programs that write these CSRs, use `--ignore-csr fcsr`
and read the CSRs into registers, which are compared exactly. The `rv64uf`
and `rv64ud` riscv-tests are such programs: they read and clear `fflags`
with `csrrw` after every operation.

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
- `PTW: Start`, `PTW: Step`, `PTW: Success` and `PTW: Failed`
  (`--trace-ptw`) mark one page-table walk: each level is `PTW: Start`, the
  read of the PTE as a `mem[R,...]` line (none if the PMP denies it) and
  `PTW: Step`. The PTW lines, and a memory read between `PTW: Start` and
  the next PTW line, are dropped: sail's TLB decides how many walks there
  are (`../doc/design-smode.md` §4.1, which found the normalised traces of
  the `-v` riscv-tests otherwise identical with and without the TLB).
  There are no PTE writes, since A and D are managed by software (Svade).
- `ret-ing from ...` and WFI/WRS wait messages are ignored; any other line is
  reported on stderr and ignored. With `wfi_is_nop` false and
  `max_time_to_wait` 0, as in `rv64gc_mu_pmp.json`, a WFI that does not
  trap at once is still one block: its instruction line, `entering
  WAIT-WFI state ...`, then `interrupt exit ...` or `forced exit ...` and
  what the exit does (retire, or an illegal-instruction trap in S-mode
  with `mstatus.TW` set), like the model's one step
  (`../doc/design-smode.md` §2.11).
- A block without an instruction line (failed fetch) gets `inst=-` and the
  pc from the `mepc` write.

### Results so far

With sail's default configuration, `int.elf` (217 steps), `rvc.elf` (118
steps) and `fp_fs.elf` (69 steps) agree. Before the fixes of the WP1 audit
(`../doc/audit-unprivileged.md`), `fp_fs.elf` diverged at step 7, where
`fld` left `mstatus.FS` at Initial (audit F5), and at step 37, `fcvt.l.d`
with `rtz` of -22.125, where the model set no `fflags.NX` (F11); scratch
programs also showed that the model did not NaN-box single-precision results
(F7) and that its `fmadd.d` rounded twice (F9). These were audit findings,
not harness problems.

With `--sail-config-override` of an RV64GC M/S/U configuration with PMP
and Sv39, Sv48 and Sv57 (`rv64gc_mu_pmp.json`), the traces of all 134
`rv64{ui,um,ua,uf,ud,uc,mi,si}-p-*` riscv-tests agree with sail, those of
`rv64uf` and `rv64ud` with `--ignore-csr fcsr` (above). Among them are
`rv64mi-p-csr`, which diverged at step 171 until `fmv.w.x` NaN-boxed its
result (F7), `rv64ui-p-ma_data` and `rv64mi-p-breakpoint`, which fail on
both emulators (below), and `rv64si-p-dirty` and `rv64si-p-icache-alias`,
which need Sv39 and diverged until the model translated addresses (WP7).
109 of the 110 `rv64{ui,um,ua,uf,ud,uc}-v-*` tests, which run in U-mode
under Sv39 with S-mode handling their page faults, pass and agree; the
other is `rv64ui-v-ma_data` (below). With `mstatus.FS` Off, every F and D
instruction, the RV64C FP loads and stores and each CSR instruction on
`fflags`, `frm` and `fcsr` must raise illegal instruction;
`tests/fsoff-all.S`, which runs all of them,
agrees with sail. It diverged at its `fle.s`, which ran and set FS to Dirty,
until FLE.S was given the FS check that the other F and D instructions
have. Within the model's scope, the one known divergence is rounding mode
RMM in an instruction that rounds (audit F13, below).

## Smoke tests

`tests/` has small self-checking programs in the style of riscv-tests
(`tests/test.h`): `gp` holds the number of the current check, failure stores
`(n << 1) | 1` to `tohost`, success stores 1, both as one 8-byte store.
Results are also stored in a signature region. Only `fp.S` touches a CSR
(below).

| Test | | Expected |
|---|---|---|
| `int.S` (rv64im) | sum over an 8-dword array, sign/zero-extending loads, sb/sh/sw/sd, mul/mulhu/div/rem including division by zero, shifts, `addiw` overflow, compares, call/return | exit 0, `int.sig.expected`, and the trace in `int.trace.expected` |
| `rvc.S` (rv64imac) | written with explicit `c.*` mnemonics: most RV64C instructions, including the stack-pointer forms, `c.addiw`/`c.addw`/`c.subw`, branches, `c.jalr`/`c.jr`, `c.lui` | exit 0, `rvc.sig.expected`; with `--no-c` exit 4 |
| `fp.S` (rv64imafd, `-DENABLE_FS`) | `fld`, `fadd.d`, `fmul.d`, `fcvt.d.l`, `fmadd.d`, `fcvt.l.d` (rtz), `fsd`, `fmv.x.d`, `feq.d` on values with exact results, and 0.1 + 0.2 | exit 0, `fp.sig.expected` |
| `fail.S` | fails check 3 on purpose | exit 1, "test 3" |

`make test` also checks that `--max-insts 10` gives exit 2, and prints the
trace of `fp.elf`. The expected signatures and `int.trace.expected` (CSR
fields left out) are sail-riscv's results too, so the files test the
harness, not only the model.

`fp.S` built with `-DENABLE_FS` first sets bit 13 of `mstatus` (`FS` =
Initial): both the model and sail reset `mstatus.FS` to Off, which makes FP
instructions illegal. `build/fp.elf` (for `make test`) and
`build/fp_fs.elf` (for `make compare`) are therefore built the same way.

## Regression programs

Programs written while fixing or extending the model, kept in `tests/`
because each found a bug, pins down a known divergence, or covers what no
riscv-test does. They use `test.h` like the
smoke tests (the FP ones through `fpmacros.h`, which also stores and clears
`fflags` after every case), are built by the Makefile into `build/`, and
are checked by `make test` (riscv-sim alone) and `make compare` (against
sail with `SAIL_CONFIG`). The expected signatures are sail's.

| Test | | `make test` | `make compare` |
|---|---|---|---|
| `fsoff-all.S` (rv64imafdc) | with `mstatus.FS` Off, every F/D instruction, the RV64C FP loads and stores and every `fflags`/`frm`/`fcsr` access must trap with illegal instruction, `mtval` = the instruction, and change nothing; found the missing FS check of FLE.S | exit 0, `fsoff-all.sig.expected` (79 traps) | agree |
| `fp-arith.S` (rv64imafdc) | F/D arithmetic, FMA, FMIN/FMAX, FCLASS, compares, with NaN, sNaN, infinity, subnormal and tie inputs in the four non-RMM rounding modes (audit F5–F12) | exit 0, `fp-arith.sig.expected` | agree with `--ignore-csr fcsr` |
| `fp-conv.S` (rv64imafdc) | every FCVT direction with saturating, boundary and tie inputs, FCVT.S.D/D.S special values, NaN-boxing round trips, `fcsr` reads | exit 0, `fp-conv.sig.expected` | agree with `--ignore-csr fcsr` |
| `fp-rmm.S` (rv64imafdc) | RMM in the exact conversions FCVT.D.S/D.W/D.WU, which must agree, then `fadd.s` with RMM at label `rmm_fadd` (audit F13, deferred): the model raises illegal instruction, sail rounds | the first trap is illegal instruction at `rmm_fadd`; exit 4 (trap loop at `mtvec` = 0) | the first divergence is the step at `rmm_fadd` |
| `batch-a.S` (rv64imac) | LR/SC reservation after a failed SC (F3), AMOMIN/MAX[U].W with junk in `rs2<63:32>` (F4), C.ADDIW (F15), DIV/REM/REMU with `rd` aliasing a source, x/0 and MIN/-1 (F20) | exit 0, `batch-a.sig.expected` | agree |
| `smode.S` (rv64im_zicsr) | S-mode execution (WP7, `../doc/design-smode.md` §2): MRET and SRET into S-mode and U-mode, ECALL from S-mode taken in M-mode and, delegated, in S-mode, the `medeleg`/`mideleg` masks, `sie`/`sip` through `mideleg`, SSIP set by M-mode and taken in S-mode with `stvec` Direct and Vectored, an undelegated SSI in S-mode and a delegated one in U-mode, SRET under TSR, WFI under TW (also with SSIP pending and enabled while SIE is clear), counter enables from S-mode and U-mode, `scause` WLRL, `stval` of an illegal instruction in S-mode, `satp` and SFENCE.VMA under TVM | exit 0, `smode.sig.expected` (100 checks) | agree |

The FP programs set `mstatus.FS` themselves (`ENABLE_FP` in `fpmacros.h`);
`fsoff-all` relies on its reset value, Off. `fp-arith` and `fp-conv` need
`--ignore-csr fcsr` for the reason given under compare.py above.

To add a regression program `tests/foo.S`:

1. Write it self-checking with `test.h` (`TEST_START`, `CHECK`, `RESULT`,
   `TEST_END`, `SIGNATURE(n)`), so that riscv-sim exits 0 on success.
2. Add `foo` to `FP_REGRESS` in the Makefile if it needs F/D (it is then
   built with `-march=rv64imafdc_zicsr`), else to `REGRESS` with a build
   rule of its own like `build/batch-a.elf`.
3. Add it to the loop in `make test`, and write `tests/foo.sig.expected`
   from sail: `sail_riscv_sim --config-override $(SAIL_CONFIG)
   --test-signature tests/foo.sig.expected build/foo.elf`.
4. Add a `compare.py $(SAIL_FLAGS) build/foo.elf` line to `make compare`
   (with `--ignore-csr fcsr` if it writes `fflags`, `frm` or `fcsr`). A
   program with an expected divergence pins it down like `fp-rmm`: a label
   at the instruction, `--max-divergences 1`, and a check that the first
   divergent step is at that label.
5. Add it to the table above.

## The riscv-tests corpus

`corpus.py` runs every `rv64*-p-*` and `rv64*-v-*` ELF in `CORPUS` (the
prebuilt [riscv-tests](https://github.com/riscv-software-src/riscv-tests),
which end through `tohost`) and checks the outcomes against
`tests/corpus.expected`. The `-p` tests run in physical memory; the `-v`
tests run the same code in U-mode under Sv39, with the riscv-tests
environment's `vm.c` in S-mode mapping pages on demand from its page-fault
handler:

- `make corpus` (`corpus.py run`) runs each test on riscv-sim and prints a
  table per suite (`rv64ui`, `rv64mi`, ..., and `rv64ui-v`, ... for the
  `-v` tests) of passes and failures, then
  each failure with its reason: the riscv-tests `TESTNUM` from `tohost`,
  riscv-sim's exit status and message, an `UNDEFINED` message, and the
  note from the expected file.
- `make compare-corpus` (`corpus.py compare`) runs `compare.py
  --max-divergences 1` on each test, with `--sail-config-override
  $(SAIL_CONFIG)` and, for `rv64uf`, `rv64ud` and `rv64uzfh`,
  `--ignore-csr fcsr`; it prints agree or diverge per test, with the first
  divergence line of each diverging test, and a table per suite.

Both exit 1 on any difference from the expected file, in either
direction: a regression (an expected pass that fails, or a change of
failure such as another test number), an unexpected pass (an expected
failure that passes), a test without an expected outcome, and an expected
test that the corpus no longer has. Exit status 2 is a tool error (no
riscv-sim, corpus or sail). `CORPUS_FLAGS=--pattern 'rv64ui-p-*'`
restricts both to some tests, `-v` lists every outcome of `make corpus`.

`tests/corpus.expected` has one line per test,
`test | riscv-sim | compare | note`. Outcomes are `pass`, `fail: test N`
(HTIF exit code N), `exception: MSG` (exit 3, e.g. `UNDEFINED "..."`),
`trap loop`, `step limit`, `timeout` for riscv-sim, and `agree`,
`diverge: step N` (the first divergent step), `error` for compare.py.
After a change of outcome that is intended (a fix, a new extension),
`make corpus-update` (or `corpus.py run --update`, `corpus.py compare
--update`) rewrites the outcome columns; it keeps the notes, and every
expected failure or divergence should have one, so review the diff of the
file before committing it.

With the default paths and `rv64gc_mu_pmp.json` the corpus has 372 tests,
199 `rv64*-p-*` and 173 `rv64*-v-*`. riscv-sim passes 246 and sail agrees
on 354:

- the 134 `rv64{ui,um,ua,uc,uf,ud,mi,si}-p` tests behave as described
  under "Results so far" and "Known not to work yet": 132 pass, all agree;
- the 62 `-p` tests of `rv64uzba`, `uzbb`, `uzbc`, `uzbkb`, `uzbkx`,
  `uzbs`, `uzfh` (but `recoding`, which passes), `uzicond` and `mzicbo`
  fail with an illegal-instruction trap that riscv-tests reports as code
  668 or 669 (1337 | `TESTNUM`), because the model has none of these
  extensions, and agree with sail, which with this configuration has none
  of them either;
- `rv64uziccid-p-ziccid` passes and agrees, and so does
  `rv64ssvnapot-p-napot`: Svnapot is absent, so its PTE with N set gives a
  page fault, which the test accepts;
- of the 110 `rv64{ui,um,ua,uc,uf,ud}-v` tests 109 pass and agree;
  `rv64ui-v-ma_data` fails and diverges (below);
- of the 63 `-v` tests of the other extensions, `uzfh-v-recoding` and
  `uziccid-v-ziccid` pass and agree. The others fail with exit code 420:
  their illegal-instruction trap is not delegated, so it goes to `vm.c`'s
  `wtf` in M-mode, which calls `terminate(841)`. In `uzba`, `uzbb`,
  `uzbkb` and `uzbs` `vm.c` itself, built with the extension, runs the
  instruction while it boots, and they agree with sail. In `uzbc`,
  `uzbkx`, `uzfh` and `uzicond` the test runs it in U-mode, `wtf` stores
  below address 0 with U-mode's `sp`, and they diverge there (below).

## Known not to work yet

- **Three riscv-tests.** Of the 134 `rv64{ui,um,ua,uf,ud,uc,mi,si}-p-*`
  tests, 132 pass. The other two fail on sail too: `rv64ui-p-ma_data` by
  design (misaligned accesses trap), `rv64mi-p-breakpoint` because it needs
  Sdtrig. Of the 110 `rv64{ui,um,ua,uf,ud,uc}-v-*` tests, 109 pass:
  `rv64ui-v-ma_data` fails by design too, and its misaligned-access trap,
  which `vm.c` does not delegate, ends in `vm.c`'s `wtf` in M-mode with
  U-mode's `sp`, 0. The first store of `wtf`, to 0xfffffffffffffff8, is
  outside sail's memory map, so sail faults there and loops, while the
  harness, which has no PMAs, goes on to `terminate(841)`; the traces
  diverge at that store. The other suites of the corpus test extensions
  that the model does not have (above, "The riscv-tests corpus");
  `tests/corpus.expected` lists every expected failure with its reason.
  riscv-arch-test has not been rerun on this model.
- **FP programs** need `mstatus.FS` set first (above), on both emulators.
  Rounding mode RMM raises illegal instruction in the model except in the
  exact conversions `fcvt.d.s`, `fcvt.d.w` and `fcvt.d.wu` (audit F13,
  deferred: neither L3's FP library nor HOL's binary_ieee rounds ties away
  from zero).
- Only bare-metal, little-endian ELF64 files; no PMAs, so accesses outside
  sail's memory map do not fault (above); no devices other than HTIF and
  the CLINT words; HTIF syscall-proxy requests (device 0 with bit 0 clear)
  are ignored with a warning, as in sail.

## Files and provenance

| File | |
|---|---|
| `Makefile` | build, `test`, `compare`, `corpus`, `compare-corpus`, `corpus-update` |
| `poly_run.sml` | loads `IntInfFix.sml`, the L3 library, `SSEFix.sml`, the model, `lib/Elf`, `sim.sml` under `polyc` |
| `sim.sml` | the harness (structure `Sim`) |
| `lib/Elf.sig`, `lib/Elf.sml` | ELF64 reader with symbol table |
| `lib/LICENSE.l3riscv` | the l3riscv licence (BSD) |
| `lib/sse_fp64_shim.c`, `lib/SSEFix.sml` | the floating-point work-around |
| `lib/IntInfFix.sml` | the `IntInf.~>>` work-around |
| `compare.py` | trace comparison with sail-riscv |
| `corpus.py` | the riscv-tests corpus on riscv-sim and through `compare.py` |
| `tests/` | smoke tests, regression programs, linker script, expected results (`*.sig.expected`, `int.trace.expected`, `corpus.expected`) |

The structure of `sim.sml` and `poly_run.sml` follows `src/sml/model.sml` and
`src/sml/poly_run.sml` of [l3riscv](https://github.com/SRI-CSL/l3riscv)
(SRI International and University of Cambridge, BSD licence, commit
`a5ed4e10`, 2019-02-25), rewritten for this export: HOL's `riscv.spec`
derives from an older version of the same spec, since rewritten for priv
1.13, and has different state, CSRs and memory (`MEM8`).
`lib/Elf.sig` is l3riscv's `src/sml/lib/Elf.sig` unchanged apart from a
provenance header comment, and
`lib/Elf.sml` its `Elf.sml` with two fixes (both marked): reads of segments
and sections no longer stop at Poly/ML's 100 KiB `readVec` limit, which had
silently truncated larger segments. Their licence headers are kept and refer
to `lib/LICENSE.l3riscv`. The HTIF logic in `sim.sml` follows sail-riscv's
`htif_store` (BSD-2-Clause).
