#![no_std]
#![no_main]

// Original e5r fixture, Apache-2.0: a ring head stepped in a loop exactly as
// embassy-sync's channel steps it in the firmware, each new head driving the
// PWM. The first DTIM word is the ring head (arbitrary at boot).
use core::ptr::{read_volatile, write_volatile};

const HEAD: *mut u32 = 0x8000_0000 as *mut u32;
const PWMCMP1: *mut u32 = 0x1001_5024 as *mut u32;
const CAP: u32 = 4;

// The entry sets the stack pointer to the top of DTIM, as riscv-rt does.
core::arch::global_asm!(
    ".section .text._start",
    ".global _start",
    "_start:",
    "lui sp, 0x80004",
    "j ring_main",
);

#[unsafe(no_mangle)]
pub extern "C" fn ring_main() -> ! {
    unsafe {
        // Bring the head into range once.
        write_volatile(HEAD, read_volatile(HEAD) % CAP);
        loop {
            let head = read_volatile(HEAD);
            let next = if head + 1 == CAP { 0 } else { head + 1 };
            write_volatile(HEAD, next);
            write_volatile(PWMCMP1, next * 33);
        }
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
