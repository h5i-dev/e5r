#![no_std]
#![no_main]

// Original e5r fixture, Apache-2.0. Absolute memory addresses are the explicit
// bare-metal ABI for this experiment, not a proof about arbitrary Rust callers.
core::arch::global_asm!(
    ".option norvc",
    ".section .text.done",
    ".global done",
    "done:",
    "j done",
    ".section .data",
    ".word 0",
    ".word 0xdeadbeef",
);

unsafe extern "C" {
    fn done() -> !;
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    unsafe {
        let input = core::ptr::read_volatile(0x2000 as *const u32);
        let output = input.wrapping_add(7).min(100);
        core::ptr::write_volatile(0x2004 as *mut u32, output);
        done()
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
