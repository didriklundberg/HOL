/* Linker script for the riscv-sim smoke tests: code at 0x80000000 (the
   riscv-tests and sail-riscv default), tohost in its own page, then data
   and the begin_signature/end_signature region. */
OUTPUT_ARCH("riscv")
ENTRY(_start)
SECTIONS
{
  . = 0x80000000;
  .text.init : { *(.text.init) }
  .text      : { *(.text) }
  . = ALIGN(0x1000);
  .tohost    : { *(.tohost) }
  . = ALIGN(0x1000);
  .data      : { *(.data) }
  .bss       : { *(.bss) }
  _end = .;
}
