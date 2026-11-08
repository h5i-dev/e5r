OUTPUT_ARCH(riscv)
ENTRY(_start)
PHDRS { control PT_LOAD FLAGS(5); text PT_LOAD FLAGS(5); rodata PT_LOAD FLAGS(4); data PT_LOAD FLAGS(6); }
SECTIONS {
 . = 0x80000000;
 .control : { KEEP(*(.text.boot)) *(.text.thermostat_heater_on) KEEP(*(.text.thermostat_transition)) KEEP(*(.text.thermostat_apply)) KEEP(*(.text.thermostat_read_only)) } :control
 .text : { *(.text*) } :text
 . = ALIGN(4);
 .rodata : { *(.rodata*) *(.srodata*) } :rodata
 . = ALIGN(4);
 .data : { *(.data*) *(.sdata*) } :data
 .bss (NOLOAD) : { . = ALIGN(4); __bss_start = .; *(.bss*) *(.sbss*) . = ALIGN(4); __bss_end = .; } :data
 __stack_top = 0x81000000;
 ASSERT(__bss_end + 65536 < __stack_top, "statics and stack exceed RAM")
 /DISCARD/ : { *(.eh_frame*) }
}
