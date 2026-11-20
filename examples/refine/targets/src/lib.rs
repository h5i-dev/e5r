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

/// Benchmark drivers (bench/refine): each reads its input from stdin into a
/// static buffer, calls one target function, writes the 8-byte result to
/// stdout and exits. Written so that the whole linked task binary stays at L1
/// or above (no panic paths: unchecked slices, `ecall` for I/O), which keeps
/// `disasm`/`asm` round-tripping it.
pub mod bench {
    static mut BUF: [u8; 1 << 16] = [0; 1 << 16];

    #[inline(always)]
    fn sys(n: usize, a0: usize, a1: usize, a2: usize) -> usize {
        let r;
        unsafe { core::arch::asm!("ecall", inlateout("a0") a0 => r, in("a1") a1, in("a2") a2, in("a7") n) };
        r
    }

    /// Read all of stdin (at most 64 KiB) into BUF.
    #[inline(always)]
    fn input() -> (*mut u8, usize) {
        let p = core::ptr::addr_of_mut!(BUF) as *mut u8;
        let mut n = 0;
        loop {
            let r = sys(63, 0, p as usize + n, (1 << 16) - n);
            if r == 0 || r > (1 << 16) {
                break;
            }
            n += r;
        }
        (p, n)
    }

    #[inline(always)]
    fn output(v: u64) {
        let b = v.to_le_bytes();
        sys(64, 1, b.as_ptr() as usize, 8);
        sys(93, 0, 0, 0);
    }

    macro_rules! driver {
        ($name:ident, |$p:ident, $n:ident| $e:expr) => {
            #[no_mangle]
            pub extern "C" fn $name() {
                let ($p, $n) = input();
                #[allow(unused_unsafe)]
                let v = unsafe { $e };
                output(v as u64);
            }
        };
    }

    /// The input after its first byte, and that byte.
    #[inline(always)]
    unsafe fn rest<'a>(p: *mut u8, n: usize) -> &'a [u8] {
        unsafe { core::slice::from_raw_parts(p.add(1), n.saturating_sub(1)) }
    }
    #[inline(always)]
    unsafe fn all<'a>(p: *mut u8, n: usize) -> &'a [u8] {
        unsafe { core::slice::from_raw_parts(p, n) }
    }

    driver!(bench_naive_count, |p, n| bytecount::naive_count(rest(p, n), *p));
    driver!(bench_naive_count_32, |p, n| bytecount::naive_count_32(rest(p, n), *p));
    driver!(bench_naive_num_chars, |p, n| bytecount::naive_num_chars(all(p, n)));
    driver!(bench_adler32, |p, n| adler::adler32_slice(all(p, n)));
    driver!(bench_fnv, |p, n| {
        use core::hash::Hasher;
        let mut h = fnv::FnvHasher::default();
        h.write(all(p, n));
        h.finish()
    });
    driver!(bench_xxh64, |p, n| twox_hash::XxHash64::oneshot(0, all(p, n)));
    driver!(bench_xxh32, |p, n| twox_hash::XxHash32::oneshot(0, all(p, n)));
    driver!(bench_sip13, |p, n| {
        use core::hash::Hasher;
        let mut h = siphasher::sip::SipHasher13::new_with_keys(1, 2);
        h.write(all(p, n));
        h.finish()
    });
    driver!(bench_itoa, |p, n| {
        let mut v = 0u64;
        for k in 0..n.min(8) {
            v |= (*p.add(k) as u64) << (8 * k);
        }
        let mut b = itoa::Buffer::new();
        let s = b.format(v);
        s.len() as u64 | (s.as_bytes()[0] as u64) << 8
    });
    driver!(bench_hex, |p, n| {
        let src = all(p, n.min(1 << 14));
        let dst = core::slice::from_raw_parts_mut(p.add(1 << 15), 2 * src.len());
        match hex::encode_to_slice(src, dst) {
            Ok(()) => dst.iter().fold(0u64, |a, &x| a.wrapping_mul(31).wrapping_add(x as u64)),
            Err(_) => u64::MAX,
        }
    });
    driver!(bench_memset, |p, n| {
        core::ptr::write_bytes(p.add(1), *p, n.saturating_sub(1));
        *p.add(n / 2) as u64
    });
    driver!(bench_memcpy, |p, n| {
        let h = n / 2;
        core::ptr::copy_nonoverlapping(p, p.add(1 << 15), h);
        *p.add((1 << 15) + h / 2) as u64
    });
    driver!(bench_memmove, |p, n| {
        core::ptr::copy(p, p.add(3), n.saturating_sub(3));
        *p.add(n / 2) as u64
    });
    driver!(bench_bcmp, |p, n| (all(p, n / 2) == core::slice::from_raw_parts(p.add(n / 2), n / 2)) as u64);
    driver!(bench_strlen, |p, n| {
        *p.add(n.min((1 << 16) - 1)) = 0;
        unsafe extern "C" {
            fn strlen(s: *const u8) -> usize;
        }
        strlen(p)
    });
}
