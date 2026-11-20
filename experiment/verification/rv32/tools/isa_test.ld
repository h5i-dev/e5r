/* Original e5r test linker script, Apache-2.0: text at 0x10000, .bss at 0x20000. */
OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(5); bss PT_LOAD FLAGS(6); }
SECTIONS {
  . = 0x10000;
  .text : { *(.text*) } :text
  . = 0x20000;
  .bss (NOLOAD) : { *(.bss*) } :bss
  /DISCARD/ : { *(.riscv.attributes) *(.comment) *(.data*) }
}
