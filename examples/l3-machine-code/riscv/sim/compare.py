#!/usr/bin/env python3
"""Run an ELF on riscv-sim (the L3 model) and on sail-riscv, and diff the
per-step traces.

Both traces are brought into the canonical format of README.md ("Trace
format"): riscv-sim writes it directly, sail's --trace-* output is
normalised here (normalise_sail).  The traces are compared step by step:

  pc, instruction bits, GPR writes, FPR writes, memory writes (and reads
  with --mem-reads), trap/interrupt cause, trap value when both sides give
  one, and CSRs (see compare_csrs: CSR effects are compared as state, not
  as write events, because the two models write different CSRs implicitly).

Exit status: 0 traces agree, 1 divergence, 2 usage or tool error: an
emulator that cannot be run, rejects its arguments, configuration or ELF,
or writes no trace or a trace with no steps.

Only the Python 3 standard library is used.
"""

import argparse
import os
import re
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))

DEFAULT_RISCV_SIM = os.path.join(HERE, "riscv-sim")
DEFAULT_SAIL = os.environ.get(
    "SAIL_RISCV_SIM",
    os.path.expanduser(
        "~/Documents/riscv-tools/sail-riscv/build/c_emulator/sail_riscv_sim"))

# Model CSR names -> sail-riscv names, for CSRs whose meaning is the same.
# The priv-1.13 riscv.spec uses sail's names; these are the names of the
# earlier priv-1.7 spec, where 0x144 and 0x344 were both "mip" (riscv-sim
# writes name@0xNNN when the spec gives one name to several numbers).
DEFAULT_CSR_ALIASES = {
    "mbadaddr": "mtval",
    "sbadaddr": "stval",
    "sptbr": "satp",
    "mip@0x344": "mip",
    "mip@0x144": "sip",
}

# Ignored by default: mip/sip hold the timer-interrupt pending bits, which
# the two emulators drive from timers of their own (riscv-sim advances the
# CLINT's mtime in memory by one per step).  Both start with mtimecmp = 0,
# so MTIP is set before the first instruction on both sides.
DEFAULT_CSR_IGNORES = ["mip", "sip"]

# sstatus, sie and sip are views of mstatus, mie and mip (priv spec
# §12.1.1, §12.1.3).  sail logs only the CSR that an instruction writes
# (or that trap entry or an xRET writes), so when it logs one of a pair its
# last logged value of the other is stale: compare.py then forgets it.
CSR_VIEWS = [("sstatus", "mstatus"), ("sie", "mie"), ("sip", "mip")]

# riscv-sim's first trace line, and its exit status for a bad command line
# or an ELF it cannot load
RISCV_SIM_TRACE_HEADER = "# riscv-sim trace v1"
RISCV_SIM_EXIT_USAGE = 64

SAIL_TRACE_FLAGS = ["--trace-instr", "--trace-reg", "--trace-mem",
                    "--trace-exception", "--trace-interrupt", "--trace-step"]


class Step:
    """One canonical step."""

    def __init__(self, n):
        self.n = n
        self.pc = None          # int
        self.inst = None        # "0x...." lower case, or "-"
        self.gpr = {}           # reg -> int
        self.fpr = {}           # reg -> int
        self.csr = {}           # name -> int (last write in the step)
        self.memw = []          # (addr, "0x...")
        self.memr = []          # (addr, "0x...")
        self.trap = None        # (is_interrupt, cause)
        self.tval = None        # int or None
        self.asm = ""
        self.raw = []           # source lines, for context

    def line(self, mem_reads=False):
        """The canonical text of this step (without comment)."""
        out = ["S %d pc=0x%016x inst=%s" % (self.n, self.pc or 0, self.inst)]
        out += ["x%d=0x%016x" % (r, v) for r, v in sorted(self.gpr.items())]
        out += ["f%d=0x%016x" % (r, v) for r, v in sorted(self.fpr.items())]
        out += ["csr[%s]=0x%016x" % (c, v) for c, v in sorted(self.csr.items())]
        if mem_reads:
            out += ["mr[0x%016x]=%s" % (a, d) for a, d in self.memr]
        out += ["mw[0x%016x]=%s" % (a, d) for a, d in self.memw]
        if self.trap is not None:
            intr, cause = self.trap
            out.append(("intr=%d" if intr else "trap=%d") % cause)
            if self.tval is not None and not intr:
                out.append("tval=0x%016x" % self.tval)
        return " ".join(out)


class Trace:
    def __init__(self):
        self.initial_csr = {}   # name -> int
        self.steps = []
        self.notes = []         # free text about the run (exit, errors)


# --------------------------------------------------------------------------
# The canonical format (riscv-sim output)
# --------------------------------------------------------------------------

FIELD_RE = re.compile(r"^(x\d+|f\d+|csr\[[^\]]+\]|mw\[0x[0-9a-f]+\]|mr\[0x[0-9a-f]+\]"
                      r"|trap|intr|tval)=(0x[0-9a-f]+|\d+)$")


def parse_canonical(text):
    tr = Trace()
    for lineno, line in enumerate(text.splitlines(), 1):
        if not line.strip():
            continue
        if line.startswith("#"):
            tr.notes.append(line[1:].strip())
            continue
        body, _, comment = line.partition(" # ")
        toks = body.split()
        if toks[0] == "I":
            for t in toks[1:]:
                m = re.match(r"^csr\[([^\]]+)\]=(0x[0-9a-f]+)$", t)
                if not m:
                    raise ValueError("line %d: bad initial field %r" % (lineno, t))
                tr.initial_csr[m.group(1)] = int(m.group(2), 16)
            continue
        if toks[0] != "S" or len(toks) < 4:
            raise ValueError("line %d: not a trace line: %r" % (lineno, line))
        st = Step(int(toks[1]))
        st.raw.append(line)
        st.asm = comment.strip()
        if not toks[2].startswith("pc=") or not toks[3].startswith("inst="):
            raise ValueError("line %d: expected pc= and inst=: %r" % (lineno, line))
        st.pc = int(toks[2][3:], 16)
        st.inst = toks[3][5:]
        for t in toks[4:]:
            m = FIELD_RE.match(t)
            if not m:
                raise ValueError("line %d: bad field %r" % (lineno, t))
            k, v = m.group(1), m.group(2)
            if k[0] == "x":
                st.gpr[int(k[1:])] = int(v, 16)
            elif k[0] == "f":
                st.fpr[int(k[1:])] = int(v, 16)
            elif k.startswith("csr["):
                st.csr[k[4:-1]] = int(v, 16)
            elif k.startswith("mw["):
                st.memw.append((int(k[3:-1], 16), v))
            elif k.startswith("mr["):
                st.memr.append((int(k[3:-1], 16), v))
            elif k == "trap":
                st.trap = (False, int(v))
            elif k == "intr":
                st.trap = (True, int(v))
            elif k == "tval":
                st.tval = int(v, 16)
        tr.steps.append(st)
    return tr


# --------------------------------------------------------------------------
# sail-riscv's trace (sail 2026-10-26-6f886e6, c_emulator/riscv_callbacks_log.cpp
# and model/postlude/step.sail), run with SAIL_TRACE_FLAGS
# --------------------------------------------------------------------------

S_INSTR = re.compile(r"^\[(\d+)\] \[(\w+)\]: 0x([0-9A-Fa-f]+) \(0x([0-9A-Fa-f]+)\) (.*)$")
S_XREG = re.compile(r"^x(\d+) <- 0x([0-9A-Fa-f]+)$")
S_FREG = re.compile(r"^f(\d+) <- 0x([0-9A-Fa-f]+)$")
S_CSRW = re.compile(r"^CSR (\S+) \(0x([0-9A-Fa-f]+)\) <- 0x([0-9A-Fa-f]+)$")
S_CSRR = re.compile(r"^CSR (\S+) \(0x([0-9A-Fa-f]+)\) -> 0x([0-9A-Fa-f]+)$")
S_MEM = re.compile(r"^mem\[([A-Za-z.]+),0x([0-9A-Fa-f]+)\] (<-|->) 0x([0-9A-Fa-f]+)$")
S_TRAPPING = re.compile(r"^trapping from \S+ to \S+ to handle (.*)$")
S_HANDLING = re.compile(r"^handling (\S+) at priv \S+ \| tval=0x([0-9A-Fa-f]+)")
S_INTERRUPT = re.compile(r"^Handling interrupt: 0x([0-9A-Fa-f]+)$")
# informational lines that carry nothing the canonical format records
S_IGNORE = [re.compile(r) for r in (
    r"^ret-ing from \S+ to \S+$",                       # mret/sret
    r"^(entering|remaining in) \S+ state at PC ",          # WFI/WRS waits
    r"^(interrupt|forced|timed-out|reservation invalid) exit from \S+ state at PC ",
)]


def normalise_sail(text, warn=None):
    """sail's --trace-* output (with --trace-step) -> Trace.

    A step is the block of lines up to a blank line.  The trap cause is
    taken from the mcause/scause write that sail logs at trap entry, the
    trap value from its "handling ... | tval=" line.
    """
    tr = Trace()
    unknown = {}
    blocks, cur = [], []
    for line in text.splitlines():
        if line.strip() == "":
            if cur:
                blocks.append(cur)
                cur = []
        else:
            cur.append(line.rstrip())
    if cur:
        blocks.append(cur)

    for idx, block in enumerate(blocks):
        st = Step(idx)
        st.raw = block
        exception = False
        interrupt = False
        cause = None
        for line in block:
            m = S_INSTR.match(line)
            if m:
                if int(m.group(1)) != idx:
                    raise ValueError("sail step [%s] is block %d of the trace; "
                                     "was sail run with --trace-step?" % (m.group(1), idx))
                st.pc = int(m.group(3), 16)
                st.inst = "0x" + m.group(4).lower()
                # the disassembly, without the symbol column
                st.asm = re.split(r"\s{2,}", m.group(5).strip())[0]
                continue
            m = S_XREG.match(line)
            if m:
                if int(m.group(1)) != 0:
                    st.gpr[int(m.group(1))] = int(m.group(2), 16)
                continue
            m = S_FREG.match(line)
            if m:
                st.fpr[int(m.group(1))] = int(m.group(2), 16)
                continue
            m = S_CSRW.match(line)
            if m:
                name, val = m.group(1), int(m.group(3), 16)
                st.csr[name] = val
                if name in ("mcause", "scause") and (exception or interrupt):
                    cause = val
                continue
            if S_CSRR.match(line):
                continue
            m = S_MEM.match(line)
            if m:
                kind, addr, arrow, data = m.groups()
                if kind == "X":
                    continue        # instruction fetch
                d = "0x" + data.lower()
                if arrow == "<-":
                    st.memw.append((int(addr, 16), d))
                else:
                    st.memr.append((int(addr, 16), d))
                continue
            m = S_TRAPPING.match(line)
            if m:
                exception = True
                continue
            m = S_HANDLING.match(line)
            if m:
                if m.group(1).startswith("exc#"):
                    exception = True
                    st.tval = int(m.group(2), 16)
                else:
                    interrupt = True
                continue
            m = S_INTERRUPT.match(line)
            if m:
                interrupt = True
                continue
            if any(r.match(line) for r in S_IGNORE):
                continue
            unknown[line] = unknown.get(line, 0) + 1
        if st.pc is None:
            # no instruction line: a fetch failure or an interrupt taken
            # before fetching; sail does not print the pc, use mepc/sepc
            st.inst = "-"
            st.pc = st.csr.get("mepc", st.csr.get("sepc", 0))
        if exception or interrupt:
            if cause is None:
                raise ValueError("sail step %d traps but logs no mcause/scause "
                                 "write:\n  %s" % (idx, "\n  ".join(block)))
            is_intr = bool(cause >> 63)
            st.trap = (is_intr, cause & ((1 << 63) - 1))
            if is_intr:
                st.tval = None
        tr.steps.append(st)
    if unknown and warn:
        for line, k in sorted(unknown.items()):
            warn("sail trace line not understood (%d times, ignored): %s" % (k, line))
    return tr


# --------------------------------------------------------------------------
# Comparison
# --------------------------------------------------------------------------

class Divergence:
    def __init__(self, step, what):
        self.step = step
        self.what = what        # list of strings


def fmt_mem(lst):
    return ", ".join("[0x%x]=%s" % (a, d) for a, d in lst) or "none"


def compare(model, sail, opts):
    """Return (divergences, csr_notes)."""
    divs = []
    aliases = dict(DEFAULT_CSR_ALIASES)
    for a in opts.csr_alias:
        k, _, v = a.partition("=")
        aliases[k] = v
    ignores = set() if opts.no_default_ignores else set(DEFAULT_CSR_IGNORES)
    for i in opts.ignore_csr:
        ignores.update(x for x in i.split(",") if x)

    def canon(name):
        return aliases.get(name, name)

    m_csr = {canon(k): v for k, v in model.initial_csr.items()}
    s_csr = {}
    # A CSR mismatch is reported once, until either value changes; otherwise
    # e.g. a differently laid out mstatus would be reported at every step
    # that writes it.
    reported = {}
    only_model, only_sail = set(), set()

    for k in range(min(len(model.steps), len(sail.steps))):
        a, b = model.steps[k], sail.steps[k]
        what = []
        if a.pc != b.pc:
            what.append("pc: model 0x%x, sail 0x%x" % (a.pc, b.pc))
        if a.inst != b.inst:
            what.append("inst: model %s, sail %s" % (a.inst, b.inst))
        if a.gpr != b.gpr:
            for r in sorted(set(a.gpr) | set(b.gpr)):
                va, vb = a.gpr.get(r), b.gpr.get(r)
                if va != vb:
                    what.append("x%d: model %s, sail %s" % (
                        r, "0x%016x" % va if va is not None else "not written",
                        "0x%016x" % vb if vb is not None else "not written"))
        if a.fpr != b.fpr:
            for r in sorted(set(a.fpr) | set(b.fpr)):
                va, vb = a.fpr.get(r), b.fpr.get(r)
                if va != vb:
                    what.append("f%d: model %s, sail %s" % (
                        r, "0x%016x" % va if va is not None else "not written",
                        "0x%016x" % vb if vb is not None else "not written"))
        if sorted(a.memw) != sorted(b.memw):
            what.append("memory writes: model %s; sail %s" % (fmt_mem(a.memw), fmt_mem(b.memw)))
        if opts.mem_reads and sorted(a.memr) != sorted(b.memr):
            what.append("memory reads: model %s; sail %s" % (fmt_mem(a.memr), fmt_mem(b.memr)))
        ta = a.trap
        tb = b.trap
        if ta != tb:
            def t(x):
                if x is None:
                    return "none"
                return ("interrupt %d" if x[0] else "exception %d") % x[1]
            what.append("trap: model %s, sail %s" % (t(ta), t(tb)))
        elif ta is not None and a.tval is not None and b.tval is not None \
                and a.tval != b.tval:
            what.append("tval: model 0x%x, sail 0x%x" % (a.tval, b.tval))

        if not opts.no_csr:
            wa = {canon(c): v for c, v in a.csr.items()}
            wb = dict(b.csr)
            m_csr.update(wa)
            s_csr.update(wb)
            for v, r in CSR_VIEWS:
                if (v in wb) != (r in wb):
                    s_csr.pop(r if v in wb else v, None)
            for c in sorted(set(wa) | set(wb)):
                if c in ignores:
                    continue
                if c not in m_csr:
                    only_sail.add(c)
                    continue
                if c not in s_csr:
                    only_model.add(c)
                    continue
                if m_csr[c] == s_csr[c]:
                    reported.pop(c, None)
                elif reported.get(c) != (m_csr[c], s_csr[c]):
                    reported[c] = (m_csr[c], s_csr[c])
                    who = ("both write it" if c in wa and c in wb else
                           "model writes it" if c in wa else "sail writes it")
                    what.append("csr %s: model 0x%016x, sail 0x%016x (%s)" % (
                        c, m_csr[c], s_csr[c], who))
        if what:
            divs.append(Divergence(k, what))
            if len(divs) >= opts.max_divergences:
                break

    if len(divs) < opts.max_divergences and len(model.steps) != len(sail.steps):
        k = min(len(model.steps), len(sail.steps))
        longer = "model" if len(model.steps) > len(sail.steps) else "sail"
        divs.append(Divergence(k, [
            "length: model trace has %d steps, sail trace %d; %s continues" % (
                len(model.steps), len(sail.steps), longer)]))

    notes = []
    if ignores and not opts.no_csr:
        notes.append("CSRs ignored: " + ", ".join(sorted(ignores)))
    if only_sail:
        notes.append("CSRs written only by sail and unknown to the model (not compared): "
                     + ", ".join(sorted(only_sail)))
    if only_model:
        notes.append("CSRs written by the model and never by sail (not compared): "
                     + ", ".join(sorted(only_model)))
    return divs, notes


def report(divs, model, sail, opts, out):
    for d in divs:
        out.write("\n=== divergence at step %d\n" % d.step)
        for w in d.what:
            out.write("  %s\n" % w)
        lo = max(0, d.step - opts.context)
        out.write("  --- model (riscv-sim), steps %d..%d\n" % (lo, d.step))
        for st in model.steps[lo:d.step + 1]:
            out.write("    %s%s\n" % (st.line(opts.mem_reads), "  # " + st.asm if st.asm else ""))
        out.write("  --- sail, normalised\n")
        for st in sail.steps[lo:d.step + 1]:
            out.write("    %s%s\n" % (st.line(opts.mem_reads), "  # " + st.asm if st.asm else ""))
        if opts.raw_sail and d.step < len(sail.steps):
            out.write("  --- sail, raw\n")
            for line in sail.steps[d.step].raw:
                out.write("    | %s\n" % line)


# --------------------------------------------------------------------------
# Running the emulators
# --------------------------------------------------------------------------

def run_model(opts, elf):
    cmd = [opts.riscv_sim, "--trace"]
    if opts.mem_reads:
        cmd.append("--trace-mem-reads")
    if opts.no_c:
        cmd.append("--no-c")
    if opts.max_insts:
        cmd += ["--max-insts", str(opts.max_insts)]
    cmd.append(elf)
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    return cmd, p.returncode, p.stdout, p.stderr


def run_sail(opts, elf, tracefile):
    cmd = [opts.sail] + SAIL_TRACE_FLAGS + ["--trace-output", tracefile]
    if opts.sail_config:
        cmd += ["--config", opts.sail_config]
    for o in opts.sail_config_override:
        cmd += ["--config-override", o]
    if opts.max_insts:
        cmd += ["--inst-limit", str(opts.max_insts)]
    cmd.append(elf)
    p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                       universal_newlines=True)
    # sail exits 1 also when the program fails its test, so the exit status
    # alone does not tell a tool error; a missing trace file does (sail
    # rejected its options, config or ELF before running).
    if os.path.exists(tracefile):
        with open(tracefile) as f:
            text = f.read()
    else:
        text = None
    return cmd, p.returncode, p.stdout + p.stderr, text


def main():
    ap = argparse.ArgumentParser(
        description="Diff the per-step traces of riscv-sim (L3 model) and sail-riscv.")
    ap.add_argument("elf", nargs="?", help="ELF file to run on both emulators")
    ap.add_argument("--riscv-sim", default=DEFAULT_RISCV_SIM,
                    help="riscv-sim binary (default: %(default)s)")
    ap.add_argument("--sail", default=DEFAULT_SAIL,
                    help="sail_riscv_sim binary (default: $SAIL_RISCV_SIM or %(default)s)")
    ap.add_argument("--sail-config", help="sail --config JSON file (default: sail's built-in)")
    ap.add_argument("--sail-config-override", action="append", default=[],
                    help="sail --config-override JSON file (repeatable)")
    ap.add_argument("--max-insts", type=int, default=100000,
                    help="step limit for both emulators (default %(default)s; 0: none)")
    ap.add_argument("--no-c", action="store_true",
                    help="run riscv-sim with --no-c (configure sail to match yourself)")
    ap.add_argument("--max-divergences", type=int, default=5,
                    help="stop after this many divergent steps (default %(default)s)")
    ap.add_argument("--context", type=int, default=3,
                    help="steps of context before a divergence (default %(default)s)")
    ap.add_argument("--raw-sail", action="store_true",
                    help="also print sail's raw trace lines of each divergent step")
    ap.add_argument("--mem-reads", action="store_true",
                    help="compare memory reads too, and show them in reports and --normalise output")
    ap.add_argument("--no-csr", action="store_true", help="do not compare CSRs")
    ap.add_argument("--ignore-csr", action="append", default=[], metavar="NAME[,NAME]",
                    help="do not compare these CSRs (sail names); default ignores: "
                         + ", ".join(DEFAULT_CSR_IGNORES))
    ap.add_argument("--no-default-ignores", action="store_true",
                    help="drop the default CSR ignore list")
    ap.add_argument("--csr-alias", action="append", default=[], metavar="MODEL=SAIL",
                    help="treat the model's CSR MODEL as sail's SAIL (added to: %s)"
                         % ", ".join("%s=%s" % kv for kv in sorted(DEFAULT_CSR_ALIASES.items())))
    ap.add_argument("--save-traces", metavar="DIR",
                    help="write model.trace, sail.raw and sail.trace into DIR")
    ap.add_argument("--model-trace", metavar="FILE",
                    help="use this riscv-sim trace instead of running riscv-sim")
    ap.add_argument("--sail-trace", metavar="FILE",
                    help="use this raw sail trace instead of running sail")
    ap.add_argument("--normalise", metavar="SAIL_TRACE",
                    help="only print the canonical form of a raw sail trace and exit")
    opts = ap.parse_args()

    def warn(s):
        sys.stdout.flush()
        sys.stderr.write("compare.py: %s\n" % s)

    if opts.normalise:
        with open(opts.normalise) as f:
            tr = normalise_sail(f.read(), warn)
        for st in tr.steps:
            sys.stdout.write(st.line(opts.mem_reads) + ("  # " + st.asm if st.asm else "") + "\n")
        return 0

    if not opts.elf and not (opts.model_trace and opts.sail_trace):
        ap.error("an ELF file is needed unless both --model-trace and --sail-trace are given")

    tmpdir = tempfile.mkdtemp(prefix="compare-")
    try:
        if opts.model_trace:
            with open(opts.model_trace) as f:
                model_text = f.read()
            model_status = None
        else:
            if not os.access(opts.riscv_sim, os.X_OK):
                warn("riscv-sim not found at %s (run make, or use --riscv-sim)" % opts.riscv_sim)
                return 2
            cmd, model_status, model_text, model_err = run_model(opts, opts.elf)
            sys.stdout.write("model: %s -> exit %d\n" % (" ".join(cmd), model_status))
            for line in model_err.splitlines():
                if not line.startswith("riscv-sim: warning: riscv.spec's csrName"):
                    sys.stdout.write("  %s\n" % line)
            if model_status == RISCV_SIM_EXIT_USAGE:
                warn("riscv-sim could not run %s (exit %d); not comparing"
                     % (opts.elf, model_status))
                return 2
            if not model_text.startswith(RISCV_SIM_TRACE_HEADER):
                warn("riscv-sim (%s) wrote no trace (exit %d); not comparing"
                     % (opts.riscv_sim, model_status))
                return 2
        if opts.sail_trace:
            with open(opts.sail_trace) as f:
                sail_text = f.read()
        else:
            if not os.access(opts.sail, os.X_OK):
                warn("sail_riscv_sim not found at %s (use --sail or $SAIL_RISCV_SIM)" % opts.sail)
                return 2
            raw = os.path.join(tmpdir, "sail.raw")
            cmd, sail_status, sail_out, sail_text = run_sail(opts, opts.elf, raw)
            sys.stdout.write("sail:  %s -> exit %d\n" % (" ".join(cmd), sail_status))
            if sail_text is None:
                for line in sail_out.splitlines()[-20:]:
                    sys.stdout.write("  %s\n" % line)
                warn("sail wrote no trace file (exit %d); not comparing" % sail_status)
                return 2
            for line in sail_out.splitlines():
                if line.startswith(("SUCCESS", "FAILURE", "Error", "error")):
                    sys.stdout.write("  %s\n" % line)

        try:
            model = parse_canonical(model_text)
            sail = normalise_sail(sail_text, warn)
        except ValueError as e:
            warn(str(e))
            return 2
        # An empty trace means the emulator did not run the program at all
        # (or the model raised an exception at step 0, see the notes);
        # that is reported as a tool error, not as a divergence.
        for who, tr in (("riscv-sim", model), ("sail", sail)):
            if not tr.steps:
                for n in tr.notes:
                    sys.stdout.write("  %s: %s\n" % (who, n))
                warn("the %s trace has no steps; not comparing" % who)
                return 2

        if opts.save_traces:
            os.makedirs(opts.save_traces, exist_ok=True)
            with open(os.path.join(opts.save_traces, "model.trace"), "w") as f:
                f.write(model_text)
            with open(os.path.join(opts.save_traces, "sail.raw"), "w") as f:
                f.write(sail_text)
            with open(os.path.join(opts.save_traces, "sail.trace"), "w") as f:
                for st in sail.steps:
                    f.write(st.line(opts.mem_reads) + ("  # " + st.asm if st.asm else "") + "\n")

        divs, notes = compare(model, sail, opts)
        sys.stdout.write("steps: model %d, sail %d\n" % (len(model.steps), len(sail.steps)))
        for n in notes:
            sys.stdout.write("note: %s\n" % n)
        if not divs:
            sys.stdout.write("traces agree\n")
            return 0
        report(divs, model, sail, opts, sys.stdout)
        sys.stdout.write("\n%d divergent step(s) reported%s\n" % (
            len(divs), " (stopped at --max-divergences)"
            if len(divs) >= opts.max_divergences else ""))
        return 1
    finally:
        shutil.rmtree(tmpdir, ignore_errors=True)


def main_or_tool_error():
    try:
        return main()
    except OSError as e:
        # unreadable --model-trace/--sail-trace/--normalise file, an
        # emulator that cannot be executed, an unwritable --save-traces
        sys.stderr.write("compare.py: %s\n" % e)
        return 2


if __name__ == "__main__":
    sys.exit(main_or_tool_error())
