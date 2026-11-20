//! Entry points into the candidate crates, so that their code is generated:
//! each `#[no_mangle] extern "C"` function calls one public function of a
//! crate on a buffer given as pointer and length. These wrappers are
//! counted separately from the crates' own functions.
#![no_std]

use core::slice;

unsafe fn sl<'a>(p: *const u8, n: usize) -> &'a [u8] {
    unsafe { slice::from_raw_parts(p, n) }
}
unsafe fn sl_mut<'a>(p: *mut u8, n: usize) -> &'a mut [u8] {
    unsafe { slice::from_raw_parts_mut(p, n) }
}

// cobs
#[no_mangle]
pub unsafe extern "C" fn w_cobs_encode(s: *const u8, n: usize, d: *mut u8, m: usize) -> usize {
    unsafe { cobs::try_encode(sl(s, n), sl_mut(d, m)).unwrap_or(usize::MAX) }
}
#[no_mangle]
pub unsafe extern "C" fn w_cobs_decode(s: *const u8, n: usize, d: *mut u8, m: usize) -> usize {
    unsafe { cobs::decode(sl(s, n), sl_mut(d, m)).map(|r| r.frame_size()).unwrap_or(usize::MAX) }
}
#[no_mangle]
pub unsafe extern "C" fn w_cobs_decode_in_place(b: *mut u8, n: usize) -> usize {
    unsafe { cobs::decode_in_place(sl_mut(b, n)).unwrap_or(usize::MAX) }
}

// memchr
#[no_mangle]
pub unsafe extern "C" fn w_memchr(c: u8, h: *const u8, n: usize) -> usize {
    unsafe { memchr::memchr(c, sl(h, n)).unwrap_or(usize::MAX) }
}
#[no_mangle]
pub unsafe extern "C" fn w_memrchr(c: u8, h: *const u8, n: usize) -> usize {
    unsafe { memchr::memrchr(c, sl(h, n)).unwrap_or(usize::MAX) }
}
#[no_mangle]
pub unsafe extern "C" fn w_memchr2(a: u8, b: u8, h: *const u8, n: usize) -> usize {
    unsafe { memchr::memchr2(a, b, sl(h, n)).unwrap_or(usize::MAX) }
}
#[no_mangle]
pub unsafe extern "C" fn w_memmem(h: *const u8, n: usize, x: *const u8, m: usize) -> usize {
    unsafe { memchr::memmem::find(sl(h, n), sl(x, m)).unwrap_or(usize::MAX) }
}

// httparse
#[no_mangle]
pub unsafe extern "C" fn w_httparse_request(b: *const u8, n: usize) -> usize {
    let mut hs = [httparse::EMPTY_HEADER; 16];
    let mut r = httparse::Request::new(&mut hs);
    match r.parse(unsafe { sl(b, n) }) {
        Ok(httparse::Status::Complete(k)) => k,
        Ok(httparse::Status::Partial) => usize::MAX - 1,
        Err(_) => usize::MAX,
    }
}

// bytecount (uutils wc counts lines with it)
#[no_mangle]
pub unsafe extern "C" fn w_bytecount(h: *const u8, n: usize, c: u8) -> usize {
    unsafe { bytecount::count(sl(h, n), c) }
}
#[no_mangle]
pub unsafe extern "C" fn w_num_chars(h: *const u8, n: usize) -> usize {
    unsafe { bytecount::num_chars(sl(h, n)) }
}

// crc32fast
#[no_mangle]
pub unsafe extern "C" fn w_crc32(h: *const u8, n: usize) -> u32 {
    let mut c = crc32fast::Hasher::new();
    c.update(unsafe { sl(h, n) });
    c.finalize()
}

// base64
#[no_mangle]
pub unsafe extern "C" fn w_base64_encode(s: *const u8, n: usize, d: *mut u8, m: usize) -> usize {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD.encode_slice(unsafe { sl(s, n) }, unsafe { sl_mut(d, m) }).unwrap_or(usize::MAX)
}
#[no_mangle]
pub unsafe extern "C" fn w_base64_decode(s: *const u8, n: usize, d: *mut u8, m: usize) -> usize {
    use base64::Engine;
    base64::engine::general_purpose::STANDARD.decode_slice(unsafe { sl(s, n) }, unsafe { sl_mut(d, m) }).unwrap_or(usize::MAX)
}

// compiler-builtins mem (memcpy, memmove, memset, memcmp, bcmp, strlen): rustc
// lowers these to calls into compiler_builtins.
#[no_mangle]
pub unsafe extern "C" fn w_copy(d: *mut u8, s: *const u8, n: usize) {
    unsafe { core::ptr::copy_nonoverlapping(s, d, n) }
}
#[no_mangle]
pub unsafe extern "C" fn w_move(d: *mut u8, s: *const u8, n: usize) {
    unsafe { core::ptr::copy(s, d, n) }
}
#[no_mangle]
pub unsafe extern "C" fn w_fill(d: *mut u8, c: u8, n: usize) {
    unsafe { core::ptr::write_bytes(d, c, n) }
}
#[no_mangle]
pub unsafe extern "C" fn w_cmp(a: *const u8, b: *const u8, n: usize) -> i32 {
    match unsafe { sl(a, n) }.cmp(unsafe { sl(b, n) }) {
        core::cmp::Ordering::Less => -1,
        core::cmp::Ordering::Equal => 0,
        core::cmp::Ordering::Greater => 1,
    }
}
#[no_mangle]
pub unsafe extern "C" fn w_eq(a: *const u8, b: *const u8, n: usize) -> bool {
    unsafe { sl(a, n) == sl(b, n) }
}

/// Exit with a status, through the environment model's exit.
fn exit(code: usize) -> ! {
    unsafe { core::arch::asm!("ecall", in("a0") code, in("a7") 93, options(noreturn)) }
}

/// A panic is an abort: exit status 101, nothing printed (no core::fmt).
#[panic_handler]
fn panic(_: &core::panic::PanicInfo) -> ! {
    exit(101)
}

#[no_mangle]
pub extern "C" fn _start() -> ! {
    exit(0)
}
