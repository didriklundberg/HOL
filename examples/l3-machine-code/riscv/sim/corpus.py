#!/usr/bin/env python3
"""Run the prebuilt riscv-tests corpus on riscv-sim, or compare it with
sail-riscv through compare.py, and check the outcomes against the expected
results in tests/corpus.expected.

  corpus.py run     [options]   riscv-sim outcome of every test
  corpus.py compare [options]   compare.py outcome of every test

The tests are the ELF files in --corpus whose names match --pattern
(default rv64*-p-*).  Both modes print a per-suite table (the suite is the
part of the name before "-p-") and the tests that fail or diverge, with
their reason, and then every difference from the expected file: a
regression, an unexpected pass, any other change of outcome, a test with
no expected outcome, and an expected test missing from the corpus.

Outcomes, as written in the expected file:

  run       pass                  HTIF exit 0
            fail: test N          HTIF exit code N (riscv-tests: TESTNUM)
            step limit            --max-insts reached (exit 2)
            exception: MSG        the model raised MSG, e.g. UNDEFINED "..."
            trap loop             64 consecutive trapping steps (exit 4)
            timeout, exit N       anything else
  compare   agree                 compare.py exit 0
            diverge: step N       compare.py exit 1, first divergence at N
            error                 compare.py exit 2 (a tool error)

--update rewrites the column of the mode that ran (keeping the other
column and the notes) instead of checking it.

Exit status: 0 every outcome as expected (or --update), 1 some outcome
changed, 2 usage or tool error (no riscv-sim, no corpus, no sail).

Only the Python 3 standard library is used.
"""

import argparse
import concurrent.futures
import fnmatch
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
TOOLS = os.path.expanduser("~/Documents/riscv-tools")

DEFAULT_RISCV_SIM = os.path.join(HERE, "riscv-sim")
DEFAULT_COMPARE = os.path.join(HERE, "compare.py")
DEFAULT_EXPECTED = os.path.join(HERE, "tests", "corpus.expected")
DEFAULT_CORPUS = os.path.join(TOOLS, "corpus", "riscv-tests")
DEFAULT_SAIL = os.environ.get(
    "SAIL_RISCV_SIM",
    os.path.join(TOOLS, "sail-riscv", "build", "c_emulator", "sail_riscv_sim"))
DEFAULT_SAIL_CONFIG = os.path.join(TOOLS, "rv64gc_mu_pmp.json")
DEFAULT_PATTERN = "rv64*-p-*"

# Extra compare.py options per suite.  The FP tests read and clear fflags
# with csrrw after every operation; sail logs a CSR instruction's write
# only under the name it used, so compare.py's copy of fcsr goes stale
# (README.md, compare.py).  The registers the values are read into are
# compared exactly.
COMPARE_OPTIONS = {
    "rv64uf": ["--ignore-csr", "fcsr"],
    "rv64ud": ["--ignore-csr", "fcsr"],
    "rv64uzfh": ["--ignore-csr", "fcsr"],
}

COLUMNS = {"run": 1, "compare": 2}
GOOD = {"run": "pass", "compare": "agree"}
UNKNOWN = "-"

HEADER = """\
# Expected outcomes of the riscv-tests corpus (rv64*-p-*) on riscv-sim and
# against sail-riscv; checked by `make corpus` (column riscv-sim) and `make
# compare-corpus` (column compare), rewritten by `make corpus-update`.
# Outcomes are those of corpus.py (see its docstring); "-" is not
# recorded.  Notes are kept by corpus-update; give every expected failure
# or divergence one.
#
# test | riscv-sim | compare | note
"""


def suite_of(name):
    return name.split("-p-")[0] if "-p-" in name else name


def is_elf(path):
    try:
        with open(path, "rb") as f:
            return f.read(4) == b"\x7fELF"
    except OSError:
        return False


def find_tests(corpus, pattern):
    names = [n for n in os.listdir(corpus)
             if fnmatch.fnmatch(n, pattern) and is_elf(os.path.join(corpus, n))]
    return sorted(names)


# --------------------------------------------------------------------------
# Running one test
# --------------------------------------------------------------------------

def last_line(text):
    lines = [l for l in text.splitlines() if l.strip()]
    return lines[-1].strip() if lines else ""


def run_one(opts, name):
    """riscv-sim outcome of one test: (outcome, detail)."""
    elf = os.path.join(opts.corpus, name)
    cmd = [opts.riscv_sim, "--max-insts", str(opts.max_insts), elf]
    try:
        p = subprocess.run(cmd, stdout=subprocess.DEVNULL, stderr=subprocess.PIPE,
                           universal_newlines=True, timeout=opts.timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "no exit after %d s" % opts.timeout
    msg = last_line(p.stderr)
    s = p.returncode
    detail = "exit %d: %s" % (s, msg)
    if s == 0:
        return "pass", detail
    if s == 1:
        m = re.search(r"\(test (\d+)\)", msg)
        return ("fail: test %s" % m.group(1) if m else "fail"), detail
    if s == 2:
        return "step limit", detail
    if s == 3:
        what = re.sub(r"^riscv-sim: ", "", msg)
        what = re.sub(r" at step \d+, pc 0x[0-9a-f]+$", "", what)
        return "exception: " + what, detail
    if s == 4:
        return "trap loop", detail
    return "exit %d" % s, detail


def compare_one(opts, name):
    """compare.py outcome of one test: (outcome, detail)."""
    elf = os.path.join(opts.corpus, name)
    cmd = [sys.executable, opts.compare, "--riscv-sim", opts.riscv_sim,
           "--sail", opts.sail, "--max-divergences", "1"]
    for c in opts.sail_config_override:
        cmd += ["--sail-config-override", c]
    if opts.max_insts_given:
        cmd += ["--max-insts", str(opts.max_insts)]
    cmd += COMPARE_OPTIONS.get(suite_of(name), [])
    cmd.append(elf)
    try:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                           universal_newlines=True, timeout=opts.timeout)
    except subprocess.TimeoutExpired:
        return "timeout", "no exit after %d s" % opts.timeout
    out = p.stdout.splitlines()
    steps = next((l for l in out if l.startswith("steps:")), "")
    if p.returncode == 0:
        return "agree", steps
    if p.returncode == 1:
        for i, l in enumerate(out):
            m = re.match(r"=== divergence at step (\d+)$", l)
            if m:
                first = out[i + 1].strip() if i + 1 < len(out) else ""
                return "diverge: step %s" % m.group(1), first
        return "diverge", last_line(p.stdout)
    return "error", last_line(p.stderr) or last_line(p.stdout)


# --------------------------------------------------------------------------
# The expected file
# --------------------------------------------------------------------------

def read_expected(path):
    """{name: [name, run, compare, note]}, in file order."""
    entries = {}
    if not os.path.exists(path):
        return entries
    with open(path) as f:
        for n, line in enumerate(f, 1):
            line = line.rstrip("\n")
            if not line.strip() or line.lstrip().startswith("#"):
                continue
            fields = [x.strip() for x in line.split("|", 3)]
            if len(fields) < 3:
                raise ValueError("%s:%d: expected 'test | riscv-sim | compare | note'"
                                 % (path, n))
            while len(fields) < 4:
                fields.append("")
            if fields[0] in entries:
                raise ValueError("%s:%d: %s listed twice" % (path, n, fields[0]))
            entries[fields[0]] = fields
    return entries


def write_expected(path, entries):
    rows = [entries[k] for k in sorted(entries)]
    w0 = max([len(r[0]) for r in rows] + [4])
    w1 = max([len(r[1]) for r in rows] + [9])
    w2 = max([len(r[2]) for r in rows] + [7])
    with open(path, "w") as f:
        f.write(HEADER)
        for r in rows:
            line = "%-*s | %-*s | %-*s" % (w0, r[0], w1, r[1], w2, r[2])
            line += (" | " + r[3]) if r[3] else ""
            f.write(line.rstrip() + "\n")


# --------------------------------------------------------------------------
# Main
# --------------------------------------------------------------------------

def table(mode, names, results):
    if mode == "run":
        cols = ["pass", "fail", "other"]
        def kind(o):
            return "pass" if o == "pass" else "fail" if o.startswith("fail") else "other"
    else:
        cols = ["agree", "diverge", "error"]
        def kind(o):
            return o if o in ("agree", "error") else \
                "diverge" if o.startswith("diverge") else "error"
    suites = {}
    for n in names:
        row = suites.setdefault(suite_of(n), dict((c, 0) for c in cols))
        row[kind(results[n][0])] += 1
    w = max([len(s) for s in suites] + [5])
    lines = ["%-*s %6s" % (w, "suite", "tests") + "".join(" %7s" % c for c in cols)]
    total = dict((c, 0) for c in cols)
    for s in sorted(suites):
        row = suites[s]
        lines.append("%-*s %6d" % (w, s, sum(row.values())) +
                     "".join(" %7d" % row[c] for c in cols))
        for c in cols:
            total[c] += row[c]
    lines.append("%-*s %6d" % (w, "total", len(names)) +
                 "".join(" %7d" % total[c] for c in cols))
    return lines


def main():
    ap = argparse.ArgumentParser(
        description="Run the riscv-tests corpus on riscv-sim (run) or compare "
                    "it with sail-riscv (compare), against tests/corpus.expected.")
    ap.add_argument("mode", choices=["run", "compare"])
    ap.add_argument("--corpus", default=DEFAULT_CORPUS,
                    help="directory of prebuilt riscv-tests ELFs (default %(default)s)")
    ap.add_argument("--pattern", default=DEFAULT_PATTERN,
                    help="test names to run, a shell pattern (default %(default)s)")
    ap.add_argument("--expected", default=DEFAULT_EXPECTED,
                    help="expected-results file (default %(default)s)")
    ap.add_argument("--update", action="store_true",
                    help="rewrite this mode's column of the expected file")
    ap.add_argument("--riscv-sim", default=DEFAULT_RISCV_SIM,
                    help="riscv-sim binary (default %(default)s)")
    ap.add_argument("--compare", default=DEFAULT_COMPARE,
                    help="compare.py (default %(default)s)")
    ap.add_argument("--sail", default=DEFAULT_SAIL,
                    help="sail_riscv_sim binary (default: $SAIL_RISCV_SIM or %s)"
                    % DEFAULT_SAIL)
    ap.add_argument("--sail-config-override", action="append", default=None,
                    metavar="FILE",
                    help="passed to compare.py, repeatable (default %s; "
                         "'' for sail's built-in configuration)" % DEFAULT_SAIL_CONFIG)
    ap.add_argument("--max-insts", type=int, default=None,
                    help="step limit (default: 1000000 for run, compare.py's "
                         "default for compare)")
    ap.add_argument("--timeout", type=int, default=600,
                    help="seconds per test (default %(default)s)")
    ap.add_argument("-j", "--jobs", type=int, default=os.cpu_count() or 1,
                    help="tests run in parallel (default %(default)s)")
    ap.add_argument("-v", "--verbose", action="store_true",
                    help="print the outcome of every test (always on for compare)")
    opts = ap.parse_args()

    opts.max_insts_given = opts.max_insts is not None
    if opts.max_insts is None:
        opts.max_insts = 1000000
    if opts.sail_config_override is None:
        opts.sail_config_override = [DEFAULT_SAIL_CONFIG]
    opts.sail_config_override = [c for c in opts.sail_config_override if c]

    def error(msg):
        sys.stderr.write("corpus.py: %s\n" % msg)
        return 2

    if not os.access(opts.riscv_sim, os.X_OK):
        return error("no riscv-sim at %s (run make, or use --riscv-sim)" % opts.riscv_sim)
    if not os.path.isdir(opts.corpus):
        return error("no corpus directory %s (set CORPUS, or use --corpus)" % opts.corpus)
    if opts.mode == "compare":
        if not os.access(opts.sail, os.X_OK):
            return error("no sail_riscv_sim at %s (set SAIL, or use --sail)" % opts.sail)
        for c in opts.sail_config_override:
            if not os.path.isfile(c):
                return error("no sail configuration %s (set SAIL_CONFIG)" % c)
    try:
        expected = read_expected(opts.expected)
    except (OSError, ValueError) as e:
        return error(str(e))

    names = find_tests(opts.corpus, opts.pattern)
    if not names:
        return error("no ELF matching %s in %s" % (opts.pattern, opts.corpus))

    one = run_one if opts.mode == "run" else compare_one
    with concurrent.futures.ThreadPoolExecutor(max(1, opts.jobs)) as ex:
        results = dict(zip(names, ex.map(lambda n: one(opts, n), names)))

    col = COLUMNS[opts.mode]
    good = GOOD[opts.mode]
    what = "riscv-sim" if opts.mode == "run" else "compare.py against sail"
    out = sys.stdout
    out.write("%s: %d tests %s in %s\n" % (what, len(names), opts.pattern, opts.corpus))
    if opts.mode == "compare":
        out.write("sail: %s%s\n" % (opts.sail, "".join(
            " --config-override " + c for c in opts.sail_config_override)))

    w = max(len(n) for n in names)
    if opts.mode == "compare" or opts.verbose:
        out.write("\n")
        for n in names:
            o, d = results[n]
            if opts.mode == "compare":
                extra = "  " + d if o != good else ""
            else:
                extra = "  " + d if opts.verbose else ""
            out.write("%-*s  %s%s\n" % (w, n, o, extra))

    out.write("\n" + "\n".join(table(opts.mode, names, results)) + "\n")

    bad = [n for n in names if results[n][0] != good]
    out.write("\n%s (%d):\n" % ("failures" if opts.mode == "run" else "divergences",
                                len(bad)))
    wo = max([len(results[n][0]) for n in bad] + [0])
    for n in bad:
        o, d = results[n]
        note = expected.get(n, ["", "", "", ""])[3]
        out.write("  %-*s  %-*s  %s\n" % (w, n, wo, o, d))
        if note:
            out.write("  %-*s  %-*s  (%s)\n" % (w, "", wo, "", note))

    if opts.update:
        ran = set(names)
        for n in list(expected):
            # a test that the corpus no longer has
            if n not in ran and fnmatch.fnmatch(n, opts.pattern) \
               and not os.path.exists(os.path.join(opts.corpus, n)):
                del expected[n]
        for n in names:
            e = expected.setdefault(n, [n, UNKNOWN, UNKNOWN, ""])
            e[col] = results[n][0]
        write_expected(opts.expected, expected)
        out.write("\nwrote %s\n" % opts.expected)
        return 0

    changes = []
    for n in names:
        got = results[n][0]
        exp = expected[n][col] if n in expected else UNKNOWN
        if exp == got:
            continue
        if exp == UNKNOWN:
            kind = "NEW"
        elif got == good:
            kind = "UNEXPECTED PASS" if opts.mode == "run" else "UNEXPECTED AGREEMENT"
        elif exp == good:
            kind = "REGRESSION"
        else:
            kind = "CHANGED"
        changes.append("  %-*s  %s: expected %s, got %s" % (w, n, kind, exp, got))
    ran = set(names)
    for n in sorted(expected):
        if n not in ran and fnmatch.fnmatch(n, opts.pattern) \
           and expected[n][col] != UNKNOWN:
            changes.append("  %-*s  MISSING: expected %s, not in the corpus"
                           % (w, n, expected[n][col]))

    rel = os.path.relpath(opts.expected)
    if changes:
        out.write("\n%d change(s) against %s:\n" % (len(changes), rel))
        out.write("\n".join(changes) + "\n")
        out.write("(fix the model or the harness, or record the new outcome with "
                  "--update / make corpus-update)\n")
        return 1
    out.write("\nall %d outcomes as in %s\n" % (len(names), rel))
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main())
    except KeyboardInterrupt:
        sys.exit(130)
