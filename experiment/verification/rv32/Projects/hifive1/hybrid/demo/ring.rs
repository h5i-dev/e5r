#![no_std]
#![no_main]

// Original e5r fixture, Apache-2.0: a ring-head step as embassy-sync's
// channel emits it, followed by a loop that drives the PWM from the head.
// The first DTIM word is the ring head (arbitrary at boot).
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
        // Bring the head into range; black_box hides the bound from the
        // optimizer, as in the firmware, where the bound is a program
        // invariant the compiler cannot see.
        let head = core::hint::black_box(read_volatile(HEAD) % CAP);
        let next = if head + 1 == CAP { 0 } else { head + 1 };
        write_volatile(HEAD, next);
        loop {
            let h = read_volatile(HEAD);
            write_volatile(PWMCMP1, h * 33);
        }
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
