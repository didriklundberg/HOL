# riscv-sim: a standalone emulator for the L3 RISC-V model in ../model, with
# a per-step trace for comparison against sail-riscv.  See README.md.
#
#   make            build riscv-sim (Poly/ML polyc, L3's runtime library)
#   make test       build the smoke tests and regression programs in tests/
#                   and check them; prints the trace of the floating-point test
#   make compare    run compare.py against sail-riscv on the smoke tests and
#                   regression programs
#   make corpus     run the riscv-tests corpus on riscv-sim and check the
#                   outcomes against tests/corpus.expected
#   make compare-corpus   the same with compare.py against sail-riscv
#   make corpus-update    rewrite tests/corpus.expected from both
#   make clean
#
# Variables:
#   L3LIBDIR   L3's lib directory (default: `l3 --lib-path` if l3 is on
#              PATH, else $(HOME)/Documents/riscv-tools/l3/L3-2018-02-09/lib)
#   MODELDIR   directory with the L3-generated riscv.sig/riscv.sml
#              (default ../model)
#   POLYC, CC, RISCV_PREFIX (riscv64-unknown-elf-), SAIL (sail_riscv_sim)
#   SAIL_CONFIG  sail --config-override file for the regression programs and
#              the corpus (default $(HOME)/Documents/riscv-tools/rv64gc_mu_pmp.json;
#              empty: sail's built-in configuration)
#   CORPUS     directory of prebuilt riscv-tests ELFs
#              (default $(HOME)/Documents/riscv-tools/corpus/riscv-tests)
#   CORPUS_FLAGS  extra corpus.py options, e.g. --pattern 'rv64ui-p-*' or -j 4

SHELL := /bin/bash

L3_ON_PATH := $(shell command -v l3 2>/dev/null)
ifneq ($(L3_ON_PATH),)
L3LIBDIR ?= $(shell l3 --lib-path)
else
L3LIBDIR ?= $(HOME)/Documents/riscv-tools/l3/L3-2018-02-09/lib
endif

MODELDIR     ?= ../model
POLYC        ?= polyc
CC           ?= cc
RISCV_PREFIX ?= riscv64-unknown-elf-
SAIL         ?= $(HOME)/Documents/riscv-tools/sail-riscv/build/c_emulator/sail_riscv_sim
SAIL_CONFIG  ?= $(HOME)/Documents/riscv-tools/rv64gc_mu_pmp.json
CORPUS       ?= $(HOME)/Documents/riscv-tools/corpus/riscv-tests
CORPUS_FLAGS ?=
PYTHON       ?= python3

RVCC    = $(RISCV_PREFIX)gcc
RVFLAGS = -nostdlib -nostartfiles -static -T tests/link.ld -I tests

SIM_SOURCES = poly_run.sml sim.sml lib/Elf.sig lib/Elf.sml lib/SSEFix.sml \
              lib/IntInfFix.sml $(MODELDIR)/riscv.sig $(MODELDIR)/riscv.sml

.PHONY: all test compare clean check-l3lib check-sail \
        corpus compare-corpus corpus-update

all: riscv-sim

check-l3lib:
	@test -f "$(L3LIBDIR)/BitsN.sml" && test -f "$(L3LIBDIR)/sse_float.c" || \
	  { echo "L3LIBDIR=$(L3LIBDIR) is not an L3 lib directory; set L3LIBDIR" >&2; exit 1; }

# See lib/sse_fp64_shim.c for why this exists.
sse_fp64_shim.so: lib/sse_fp64_shim.c | check-l3lib
	$(CC) -shared -fPIC -I"$(L3LIBDIR)" -o $@ lib/sse_fp64_shim.c "$(L3LIBDIR)/sse_float.c"

# polyc echoes every declaration; keep that in riscv-sim.log and show only
# errors and warnings.  riscv.sml has one known non-exhaustive match warning.
riscv-sim: $(SIM_SOURCES) sse_fp64_shim.so | check-l3lib
	@echo "polyc -o $@ poly_run.sml   (L3LIBDIR=$(L3LIBDIR), MODELDIR=$(MODELDIR))"
	@L3LIBDIR="$(L3LIBDIR)" RISCV_MODEL_DIR="$(MODELDIR)" \
	  SSE_SHIM="$(CURDIR)/sse_fp64_shim.so" \
	  $(POLYC) -o $@ poly_run.sml > riscv-sim.log 2>&1 \
	  || { grep -i -B1 -A6 'error\|exception' riscv-sim.log >&2; rm -f $@; exit 1; }
	@grep -i -A2 'warning' riscv-sim.log | grep -v '^--$$' >&2 || true
	@test -x $@

# ---------------------------------------------------------------------------
# Smoke tests
# ---------------------------------------------------------------------------

build:
	mkdir -p build

build/int.elf: tests/int.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64im -mabi=lp64 -o $@ $<

build/rvc.elf: tests/rvc.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64imac -mabi=lp64 -o $@ $<

# FS resets to Off (as in sail-riscv), so the test enables FP first
build/fp.elf: tests/fp.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64imafd_zicsr -mabi=lp64d -DENABLE_FS -o $@ $<

# the same program as fp.elf, under the name make compare uses
build/fp_fs.elf: tests/fp.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64imafd_zicsr -mabi=lp64d -DENABLE_FS -o $@ $<

build/fail.elf: tests/fail.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64im -mabi=lp64 -o $@ $<

# Regression programs (README.md, "Regression programs").  Self-checking
# like the smoke tests; the FP ones set mstatus.FS themselves (fsoff-all
# relies on its reset value, Off).
FP_REGRESS = fsoff-all fp-arith fp-conv fp-rmm
REGRESS    = $(FP_REGRESS) batch-a

$(FP_REGRESS:%=build/%.elf): build/%.elf: tests/%.S tests/test.h tests/fpmacros.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64imafdc_zicsr -mabi=lp64d -o $@ $<

build/batch-a.elf: tests/batch-a.S tests/test.h tests/link.ld | build
	$(RVCC) $(RVFLAGS) -march=rv64imac -mabi=lp64 -o $@ $<

TEST_ELFS = build/int.elf build/rvc.elf build/fp.elf build/fail.elf \
            $(REGRESS:%=build/%.elf)

# the address of fp-rmm.S's label rmm_fadd, 16 hex digits as in the traces
RMM_PC = $$($(RISCV_PREFIX)nm build/fp-rmm.elf | awk '$$3 == "rmm_fadd" { print $$1 }')

# expect STATUS CMD...: run CMD, check its exit status
define expect
	@echo '--- $(2)'; \
	$(2); s=$$?; \
	if [ $$s -ne $(1) ]; then echo "FAILED: exit status $$s, expected $(1)"; exit 1; fi
endef

test: riscv-sim $(TEST_ELFS)
	$(call expect,0,./riscv-sim --max-insts 10000 --signature build/int.sig build/int.elf)
	diff -u tests/int.sig.expected build/int.sig
	$(call expect,0,./riscv-sim --max-insts 10000 --signature build/rvc.sig build/rvc.elf)
	diff -u tests/rvc.sig.expected build/rvc.sig
	$(call expect,0,./riscv-sim --max-insts 10000 --signature build/fp.sig build/fp.elf)
	diff -u tests/fp.sig.expected build/fp.sig
	@# negative tests: failing check, --no-c on compressed code, step limit
	$(call expect,1,(./riscv-sim --max-insts 10000 build/fail.elf 2>&1 | tee build/fail.out; exit $${PIPESTATUS[0]}))
	grep -q '(test 3)' build/fail.out
	$(call expect,4,./riscv-sim --no-c --max-insts 10000 build/rvc.elf)
	$(call expect,2,./riscv-sim --max-insts 10 build/int.elf)
	@# regression programs: exit 0 and sail's signature
	@for t in fsoff-all fp-arith fp-conv batch-a; do \
	  echo "--- ./riscv-sim --max-insts 100000 --signature build/$$t.sig build/$$t.elf"; \
	  ./riscv-sim --max-insts 100000 --signature build/$$t.sig build/$$t.elf; s=$$?; \
	  if [ $$s -ne 0 ]; then echo "FAILED: exit status $$s, expected 0"; exit 1; fi; \
	  diff -u tests/$$t.sig.expected build/$$t.sig || exit 1; \
	done
	@# fp-rmm: the fadd.s with rmm is the first step that traps, with
	@# illegal instruction (audit F13, deferred); mtvec is 0, so the
	@# run ends in a trap loop
	$(call expect,4,./riscv-sim --max-insts 100000 build/fp-rmm.elf)
	@echo '--- fp-rmm: the first trap must be illegal instruction at rmm_fadd'
	@./riscv-sim --trace --no-asm --max-insts 100000 build/fp-rmm.elf 2>/dev/null \
	  | grep -m1 ' trap=' > build/fp-rmm.trap; \
	  grep -q "pc=0x$(RMM_PC) inst=0x003140d3 .*trap=2 " build/fp-rmm.trap \
	  || { cat build/fp-rmm.trap; echo "FAILED: the first trap is not fadd.s rmm"; exit 1; }
	@# the trace of the integer test must not change; CSR fields are left
	@# out (make compare checks them), as is the disassembly.
	@# tests/int.trace.expected is also sail's trace, normalised.
	./riscv-sim --trace --no-asm build/int.elf 2>/dev/null | grep '^S ' \
	  | sed 's/ csr\[[^]]*\]=0x[0-9a-f]*//g' > build/int.trace
	diff -u tests/int.trace.expected build/int.trace
	@echo "--- trace of build/fp.elf"
	./riscv-sim --trace build/fp.elf
	@echo "make test: all smoke tests and regression programs passed"

# ---------------------------------------------------------------------------
# Comparison with sail-riscv
# ---------------------------------------------------------------------------

SAIL_FLAGS = --sail "$(SAIL)" $(if $(SAIL_CONFIG),--sail-config-override "$(SAIL_CONFIG)")

check-sail:
	@test -x "$(SAIL)" || { echo "no sail_riscv_sim at $(SAIL); set SAIL" >&2; exit 1; }
	@test -z "$(SAIL_CONFIG)" || test -f "$(SAIL_CONFIG)" || \
	  { echo "no sail configuration $(SAIL_CONFIG); set SAIL_CONFIG" >&2; exit 1; }

# int, rvc and fp_fs must agree with sail (in its built-in configuration);
# fsoff-all and batch-a with SAIL_CONFIG, fp-arith and fp-conv also,
# with --ignore-csr fcsr (README.md, compare.py).  fp-rmm must diverge,
# and first at its fadd.s with rmm, which sail rounds and the model makes
# illegal (audit F13, deferred).
compare: riscv-sim build/int.elf build/rvc.elf build/fp_fs.elf $(REGRESS:%=build/%.elf) | check-sail
	$(PYTHON) compare.py --sail "$(SAIL)" build/int.elf
	$(PYTHON) compare.py --sail "$(SAIL)" build/rvc.elf
	$(PYTHON) compare.py --sail "$(SAIL)" build/fp_fs.elf
	$(PYTHON) compare.py $(SAIL_FLAGS) build/fsoff-all.elf
	$(PYTHON) compare.py $(SAIL_FLAGS) build/batch-a.elf
	$(PYTHON) compare.py $(SAIL_FLAGS) --ignore-csr fcsr build/fp-arith.elf
	$(PYTHON) compare.py $(SAIL_FLAGS) --ignore-csr fcsr build/fp-conv.elf
	@echo '--- compare.py $(SAIL_FLAGS) --ignore-csr fcsr --max-divergences 1 build/fp-rmm.elf'
	@$(PYTHON) compare.py $(SAIL_FLAGS) --ignore-csr fcsr --max-divergences 1 \
	  build/fp-rmm.elf > build/fp-rmm.cmp; s=$$?; \
	  step=$$(sed -n 's/^=== divergence at step //p' build/fp-rmm.cmp); pc=$(RMM_PC); \
	  if [ $$s -eq 1 ] && [ -n "$$step" ] && [ -n "$$pc" ] && \
	     grep -q "^    S $$step pc=0x$$pc inst=0x003140d3 " build/fp-rmm.cmp; then \
	    echo "fp-rmm: first divergence at step $$step, the fadd.s rmm at 0x$$pc, as expected"; \
	  else cat build/fp-rmm.cmp; \
	    echo "FAILED: fp-rmm must diverge first at its fadd.s rmm (rmm_fadd = 0x$$pc)"; exit 1; fi
	@echo "make compare: all traces as expected"

# ---------------------------------------------------------------------------
# The riscv-tests corpus (corpus.py; README.md, "The riscv-tests corpus")
# ---------------------------------------------------------------------------

CORPUS_PY = $(PYTHON) corpus.py --corpus "$(CORPUS)" --riscv-sim ./riscv-sim \
            --expected tests/corpus.expected $(CORPUS_FLAGS)
CORPUS_SAIL = --sail "$(SAIL)" \
              --sail-config-override "$(SAIL_CONFIG)"

corpus: riscv-sim
	$(CORPUS_PY) run

compare-corpus: riscv-sim | check-sail
	$(CORPUS_PY) compare $(CORPUS_SAIL)

corpus-update: riscv-sim | check-sail
	$(CORPUS_PY) run --update
	$(CORPUS_PY) compare $(CORPUS_SAIL) --update

clean:
	rm -rf build riscv-sim riscv-sim.log sse_fp64_shim.so
