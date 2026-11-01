//! `e5r-verify ptx run`: the differential-test cases on the concrete
//! interpreter of `e5r-ptx`, printed in the format of `gpurun` and
//! `ptxdiff` so scripts/check-ptx-difftest.sh can compare all of them. The
//! interpreter is untrusted; this is how it is checked against the GPU and
//! the Lean model.

use e5r_ptx::ast::Module;
use e5r_ptx::interp::{Dim3, GridEnd, Launch, Mem, Region, layout, run_grid};
use std::collections::HashMap;
use std::fmt::Write;

const IN: u64 = 0x1_0000_0000;
const OUT: u64 = 0x2_0000_0000;

fn unhex(s: &str) -> Vec<u8> {
    (0..s.len() / 2)
        .map(|i| u8::from_str_radix(&s[2 * i..2 * i + 2], 16).unwrap_or(0))
        .collect()
}

/// Run every case line of `text` and print one result line per case.
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
        // shared variables from offset 0 in declaration order, as ptxas
        // places them; the test kernels' outputs do not depend on it
        let l = Launch {
            grid,
            block,
            params,
            sym: layout(kern, 0),
            alloc: al.to_vec(),
        };
        // one schedule of the model (`run_grid`): CTA after CTA, each
        // thread to its next barrier in `Launch.threads` order
        let fault = !matches!(
            run_grid(kern, &l, &mut mem, &Mem::default(), 10_000_000).0,
            GridEnd::Done
        );
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
