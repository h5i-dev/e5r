//! QEMU virt RV32 UART transport for the existing h5i thermostat (Apache-2.0).
#![no_std]
#![no_main]

use core::ptr::{read_volatile, write_volatile};
use core::{
    future::Future,
    pin::pin,
    task::{Context, Poll, Waker},
};
use embedded_io_async::{ErrorType, Read, Write};
use thermostat_app::{App, router};

core::arch::global_asm!(
    r#"
.section .text.boot
.global _start
_start:
 csrwi mie, 0
 csrci mstatus, 8
 la sp, __stack_top
 la t0, __bss_start
 la t1, __bss_end
1:
 bgeu t0, t1, 2f
 sw zero, 0(t0)
 addi t0, t0, 4
 j 1b
2:
 call main
3: j 3b
"#
);

// One hart, no interrupts enabled anywhere in this firmware.
struct SingleHart;
critical_section::set_impl!(SingleHart);
unsafe impl critical_section::Impl for SingleHart {
    unsafe fn acquire() -> critical_section::RawRestoreState {}
    unsafe fn release(_: critical_section::RawRestoreState) {}
}

struct Uart;
impl ErrorType for Uart {
    type Error = core::convert::Infallible;
}
impl Read for Uart {
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize, Self::Error> {
        if buf.is_empty() {
            return Ok(0);
        }
        unsafe {
            while read_volatile(0x10000005 as *const u8) & 1 == 0 {
                core::hint::spin_loop();
            }
            buf[0] = read_volatile(0x10000000 as *const u8);
        }
        Ok(1)
    }
}
impl Write for Uart {
    async fn write(&mut self, buf: &[u8]) -> Result<usize, Self::Error> {
        for &b in buf {
            unsafe {
                while read_volatile(0x10000005 as *const u8) & 0x20 == 0 {
                    core::hint::spin_loop();
                }
                write_volatile(0x10000000 as *mut u8, b);
            }
        }
        Ok(buf.len())
    }
    async fn flush(&mut self) -> Result<(), Self::Error> {
        Ok(())
    }
}

fn block_on<F: Future>(f: F) -> F::Output {
    let mut f = pin!(f);
    let mut cx = Context::from_waker(Waker::noop());
    loop {
        if let Poll::Ready(v) = f.as_mut().poll(&mut cx) {
            return v;
        }
    }
}

#[unsafe(no_mangle)]
extern "C" fn main() -> ! {
    let app = App::new(b"dev-key");
    let routes = router();
    let mut rx = [0; 2048];
    let mut tx = [0; 1024];
    let mut uart = Uart;
    loop {
        let _ = block_on(h5i_app_embedded::serve(
            &Default::default(),
            &routes,
            &app,
            &mut rx,
            &mut tx,
            &mut uart,
        ));
    }
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    loop {
        core::hint::spin_loop();
    }
}
