//! `e5r-verify ptx run`: the differential-test cases on the concrete
//! interpreter of `e5r-ptx`, printed in the format of `gpurun` and
//! `ptxdiff` so scripts/check-ptx-difftest.sh can compare all of them. The
//! interpreter is untrusted; this is how it is checked against the GPU and
//! the Lean model.

use e5r_ptx::ast::Module;
use e5r_ptx::interp::{Ctx, Dim3, End, Mem, Region, run_solo};
use std::collections::HashMap;
use std::fmt::Write;

const IN: u64 = 0x1_0000_0000;
const OUT: u64 = 0x2_0000_0000;

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap_or(0))
        .collect()
}

pub fn run_cases(m: &Module, text: &str) -> Result<String, String> {
    let mut out = String::new();
    for line in text.lines().filter(|l| !l.is_empty()) {
        let w: Vec<&str> = line.split(' ').collect();
        let [_, k, gx, gy, gz, bx, by, bz, s, inhex, outn] = w.as_slice() else {
            return Err(format!("bad case line: {}", &line[..line.len().min(60)]));
        };
        let num = |x: &str| x.parse::<u32>().map_err(|e| format!("{x}: {e}"));
        let kern = m
            .kernels
            .iter()
            .find(|x| x.name == *k)
            .ok_or(format!("no kernel {k}"))?;
        let (grid, block) = (
            Dim3 {
                x: num(gx)?,
                y: num(gy)?,
                z: num(gz)?,
            },
            Dim3 {
                x: num(bx)?,
                y: num(by)?,
                z: num(bz)?,
            },
        );
        let inb = if *inhex == "00" {
            Vec::new()
        } else {
            unhex(inhex)
        };
        let outn: usize = outn.parse().map_err(|_| "bad output size".to_string())?;
        let mut mem = Mem::default();
        for (i, b) in inb.iter().enumerate() {
            mem.bytes.insert(IN + i as u64, *b);
        }
        for i in 0..outn {
            mem.bytes.insert(OUT + i as u64, 0xA5);
        }
        let al = [
            Region {
                base: IN,
                size: inb.len() as u128,
            },
            Region {
                base: OUT,
                size: outn as u128,
            },
        ];
        let mut params = HashMap::new();
        params.insert(format!("{k}_in"), IN);
        params.insert(format!("{k}_out"), OUT);
        params.insert(format!("{k}_s"), num(s)? as u64);
        let mut fault = false;
        // the order of `Launch.threads`: CTAs, then threads, z outermost
        'all: for cz in 0..grid.z {
            for cy in 0..grid.y {
                for cx in 0..grid.x {
                    for tz in 0..block.z {
                        for ty in 0..block.y {
                            for tx in 0..block.x {
                                let c = Ctx {
                                    tid: Dim3 {
                                        x: tx,
                                        y: ty,
                                        z: tz,
                                    },
                                    ntid: block,
                                    ctaid: Dim3 {
                                        x: cx,
                                        y: cy,
                                        z: cz,
                                    },
                                    nctaid: grid,
                                    params: params.clone(),
                                };
                                if !matches!(
                                    run_solo(kern, &al, &c, &mut mem, 100_000).0,
                                    End::Halted(_)
                                ) {
                                    fault = true;
                                    break 'all;
                                }
                            }
                        }
                    }
                }
            }
        }
        if fault {
            writeln!(out, "fault {k}").unwrap();
        } else {
            write!(out, "result {k} ").unwrap();
            for i in 0..outn {
                write!(out, "{:02x}", mem.get(OUT + i as u64)).unwrap();
            }
            out.push('\n');
        }
    }
    Ok(out)
}
