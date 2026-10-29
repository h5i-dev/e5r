OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { text PT_LOAD FLAGS(5); data PT_LOAD FLAGS(6); }
SECTIONS {
  . = 0x1000;
  .text : { *(.text*) } :text
  . = 0x2000;
  .data : { KEEP(*(.data*)) KEEP(*(.sdata*)) } :data
  .bss : { *(.bss*) *(.sbss*) } :data
  /DISCARD/ : { *(.riscv.attributes) *(.comment) }
}
