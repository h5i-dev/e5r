/* Original e5r fixture, Apache-2.0. HiFive1 Rev B flash entry; no data. */
OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(5); }
SECTIONS {
  . = 0x20010000;
  .text : { *(.text._start) *(.text*) } :text
  /DISCARD/ : { *(.riscv.attributes) *(.comment) *(.data*) *(.bss*) *(.sdata*) *(.sbss*) }
}
