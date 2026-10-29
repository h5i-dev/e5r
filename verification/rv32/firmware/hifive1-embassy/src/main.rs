//! HiFive1 Rev B Embassy firmware, the first e5r binary-verification target.
//!
//! One thread-mode executor and two tasks. `sampler` wakes every 10 ms from the
//! CLINT machine-timer interrupt, reads one byte from UART0 if one is waiting
//! and sends it through a bounded channel. `actuator` keeps a moving window of
//! the last eight samples and writes a duty value to PWM0's compare register.
//! The property proved about the emitted binary is that every value written to
//! that register is at most `MAX_DUTY`, and that the firmware never faults.
#![no_std]
#![no_main]

use core::cell::RefCell;
use core::ptr::{read_volatile, write_volatile};
use core::task::Waker;

use critical_section::Mutex;
use embassy_executor::Spawner;
use embassy_sync::blocking_mutex::raw::CriticalSectionRawMutex;
use embassy_sync::channel::Channel;
use embassy_time::Timer;
use embassy_time_driver::Driver;
use embassy_time_queue_utils::Queue;
use riscv::interrupt::Interrupt;

const CLINT_MTIMECMP: usize = 0x0200_4000;
const CLINT_MTIME: usize = 0x0200_bff8;
const UART0_RXDATA: usize = 0x1001_3004;
const PWM0_CMP1: usize = 0x1001_5024;
const RXDATA_EMPTY: u32 = 1 << 31;
const MAX_DUTY: u32 = 100;
const WINDOW: usize = 8;

static SAMPLES: Channel<CriticalSectionRawMutex, u8, 4> = Channel::new();

fn mtime() -> u64 {
    // The 64-bit counter is two 32-bit registers on RV32: re-read the high
    // half until it is stable so a carry between the reads is not torn.
    loop {
        let hi = unsafe { read_volatile((CLINT_MTIME + 4) as *const u32) };
        let lo = unsafe { read_volatile(CLINT_MTIME as *const u32) };
        if hi == unsafe { read_volatile((CLINT_MTIME + 4) as *const u32) } {
            return (u64::from(hi) << 32) | u64::from(lo);
        }
    }
}

fn set_mtimecmp(at: u64) {
    // Raise the high half first so no intermediate value fires early.
    unsafe {
        write_volatile((CLINT_MTIMECMP + 4) as *mut u32, u32::MAX);
        write_volatile(CLINT_MTIMECMP as *mut u32, at as u32);
        write_volatile((CLINT_MTIMECMP + 4) as *mut u32, (at >> 32) as u32);
    }
}

struct Clint {
    queue: Mutex<RefCell<Queue>>,
}

impl Clint {
    fn rearm(&self, cs: critical_section::CriticalSection) {
        let mut queue = self.queue.borrow(cs).borrow_mut();
        // `next_expiration` wakes everything already due and returns the next
        // deadline, or u64::MAX when nothing is waiting.
        set_mtimecmp(queue.next_expiration(mtime()));
    }
}

impl Driver for Clint {
    fn now(&self) -> u64 {
        mtime()
    }

    fn schedule_wake(&self, at: u64, waker: &Waker) {
        critical_section::with(|cs| {
            if self.queue.borrow(cs).borrow_mut().schedule_wake(at, waker) {
                self.rearm(cs);
            }
        });
    }
}

embassy_time_driver::time_driver_impl!(static DRIVER: Clint = Clint {
    queue: Mutex::new(RefCell::new(Queue::new())),
});

#[riscv_rt::core_interrupt(Interrupt::MachineTimer)]
fn machine_timer() {
    critical_section::with(|cs| DRIVER.rearm(cs));
}

#[embassy_executor::task]
async fn sampler() {
    loop {
        Timer::after_millis(10).await;
        let raw = unsafe { read_volatile(UART0_RXDATA as *const u32) };
        if raw & RXDATA_EMPTY == 0 {
            SAMPLES.send(raw as u8).await;
        }
    }
}

/// The duty for a window of samples: their mean, offset and clamped.
#[inline(never)]
fn duty(window: &[u8; WINDOW]) -> u32 {
    let sum: u32 = window.iter().map(|&s| u32::from(s)).sum();
    (sum / WINDOW as u32 + 7).min(MAX_DUTY)
}

#[embassy_executor::task]
async fn actuator() {
    let mut window = [0u8; WINDOW];
    let mut next = 0;
    loop {
        window[next] = SAMPLES.receive().await;
        next += 1;
        if next == WINDOW {
            next = 0;
        }
        unsafe { write_volatile(PWM0_CMP1 as *mut u32, duty(&window)) };
    }
}

#[embassy_executor::main]
async fn main(spawner: Spawner) {
    set_mtimecmp(u64::MAX);
    unsafe {
        riscv::register::mie::set_mtimer();
        riscv::interrupt::enable();
    }
    spawner.spawn(sampler().unwrap());
    spawner.spawn(actuator().unwrap());
}

#[panic_handler]
fn panic(_: &core::panic::PanicInfo<'_>) -> ! {
    loop {}
}
