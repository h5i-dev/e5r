#![no_std]
#![no_main]

// Original e5r fixture, Apache-2.0: the V0 clamp, on the HiFive1 memory map.
// The input and output words are the first two words of DTIM.
core::arch::global_asm!(
    ".section .text.done",
    ".global done",
    "done:",
    "j done",
);

unsafe extern "C" {
    fn done() -> !;
}

#[unsafe(no_mangle)]
pub extern "C" fn _start() -> ! {
    unsafe {
        let input = core::ptr::read_volatile(0x8000_0000 as *const u32);
        let output = input.wrapping_add(7).min(100);
        core::ptr::write_volatile(0x8000_0004 as *mut u32, output);
        done()
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
