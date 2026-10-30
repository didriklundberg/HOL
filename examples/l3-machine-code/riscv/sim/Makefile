# riscv-sim: a standalone emulator for the L3 RISC-V model in ../model, with
# a per-step trace for comparison against sail-riscv.  See README.md.
#
#   make            build riscv-sim (Poly/ML polyc, L3's runtime library)
#   make test       build the smoke tests in tests/ and check them; prints
#                   the trace of the floating-point test
#   make compare    run compare.py against sail-riscv on the smoke tests
#   make clean
#
# Variables:
#   L3LIBDIR   L3's lib directory (default: `l3 --lib-path` if l3 is on
#              PATH, else $(HOME)/Documents/riscv-tools/l3/L3-2018-02-09/lib)
#   MODELDIR   directory with the L3-generated riscv.sig/riscv.sml
#              (default ../model)
#   POLYC, CC, RISCV_PREFIX (riscv64-unknown-elf-), SAIL (sail_riscv_sim)

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
PYTHON       ?= python3

RVCC    = $(RISCV_PREFIX)gcc
RVFLAGS = -nostdlib -nostartfiles -static -T tests/link.ld -I tests

SIM_SOURCES = poly_run.sml sim.sml lib/Elf.sig lib/Elf.sml lib/SSEFix.sml \
              $(MODELDIR)/riscv.sig $(MODELDIR)/riscv.sml

.PHONY: all test compare clean check-l3lib

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

TEST_ELFS = build/int.elf build/rvc.elf build/fp.elf build/fail.elf

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
	@# the trace of the integer test must not change; CSR fields are left
	@# out (make compare checks them), as is the disassembly.
	@# tests/int.trace.expected is also sail's trace, normalised.
	./riscv-sim --trace --no-asm build/int.elf 2>/dev/null | grep '^S ' \
	  | sed 's/ csr\[[^]]*\]=0x[0-9a-f]*//g' > build/int.trace
	diff -u tests/int.trace.expected build/int.trace
	@echo "--- trace of build/fp.elf"
	./riscv-sim --trace build/fp.elf
	@echo "make test: all smoke tests passed"

# ---------------------------------------------------------------------------
# Comparison with sail-riscv
# ---------------------------------------------------------------------------

# int and rvc must agree with sail; fp_fs is expected to diverge while FLD
# does not set mstatus.FS to Dirty and FP exception flags are not modelled.
compare: riscv-sim build/int.elf build/rvc.elf build/fp_fs.elf
	@test -x "$(SAIL)" || { echo "no sail_riscv_sim at $(SAIL); set SAIL" >&2; exit 1; }
	$(PYTHON) compare.py --sail "$(SAIL)" build/int.elf
	$(PYTHON) compare.py --sail "$(SAIL)" build/rvc.elf
	-$(PYTHON) compare.py --sail "$(SAIL)" build/fp_fs.elf

clean:
	rm -rf build riscv-sim riscv-sim.log sse_fp64_shim.so
