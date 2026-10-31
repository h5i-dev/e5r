//! The machine-readable board description (`verification/rv32/boards/*.json`).

use serde::Deserialize;

use crate::flash::Windows;

#[derive(Debug, Deserialize)]
pub struct Board {
    pub schema: String,
    pub id: String,
    pub memory: Vec<Region>,
    pub devices: Vec<Device>,
}

#[derive(Debug, Deserialize)]
pub struct Region {
    pub name: String,
    pub base: String,
    pub size: String,
    pub kind: String,
}

#[derive(Debug, Deserialize)]
pub struct Device {
    pub name: String,
    pub addr: String,
    pub read: bool,
    pub write: bool,
}

pub const SCHEMA: &str = "e5r.board.v1";

fn hex(s: &str) -> Result<u64, String> {
    let digits = s
        .strip_prefix("0x")
        .ok_or_else(|| format!("{s}: expected 0x-prefixed hex"))?;
    u64::from_str_radix(digits, 16).map_err(|e| format!("{s}: {e}"))
}

impl Board {
    pub fn parse(text: &str) -> Result<Board, String> {
        let b: Board = serde_json::from_str(text).map_err(|e| format!("board: {e}"))?;
        if b.schema != SCHEMA {
            return Err(format!("board schema {} is not {SCHEMA}", b.schema));
        }
        Ok(b)
    }

    fn one(&self, kind: &str) -> Result<(u64, u64), String> {
        let mut it = self.memory.iter().filter(|r| r.kind == kind);
        match (it.next(), it.next()) {
            (Some(r), None) => Ok((hex(&r.base)?, hex(&r.size)?)),
            _ => Err(format!("board {} needs exactly one {kind} region", self.id)),
        }
    }

    pub fn windows(&self) -> Result<Windows, String> {
        let (flash_base, flash_size) = self.one("image")?;
        let (ram_base, ram_size) = self.one("ram")?;
        Ok(Windows {
            flash_base,
            flash_size,
            ram_base,
            ram_size,
        })
    }
}
