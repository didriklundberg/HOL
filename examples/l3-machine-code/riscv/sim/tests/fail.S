/* Negative smoke test: check 3 fails on purpose, so riscv-sim must report
   "test 3" and exit with status 1. */
#include "test.h"

        TEST_START
        CHECK(1, zero, 0)
        CHECK(2, zero, 0)
        CHECK(3, zero, 1)
        j       pass

        TEST_END

        SIGNATURE(1)
