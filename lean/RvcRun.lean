import NoCompiler.Ext.Rvc
import NoCompiler.Elf

/-
For examples/demo/test/rvc_exec.py: run a function of a compressed binary in the
extension's semantics (`CCode.instr`, `execC`), on inputs read from stdin,
so that the result can be compared with qemu-riscv64 running the same bytes.

  rvc-run ELF ENTRY < records      (records: u64 len, len bytes; as cobs_test_main.c)

Each call is `f(a0 = slot, a1 = buf, a2 = len)` with the 24-byte slot filled
with 0xaa/0xbb/0xcc words, as the qemu driver does. Writes the slot and the
buffer afterwards, as the driver does. Not used by any proof.
-/
open NoCompiler

def slot : Word := 0x200000#64
def bufAt : Word := 0x300000#64
def retAddr : Word := 0x4000#64

partial def runC (c : CCode) (fuel : Nat) (s : State) : Option State :=
  if s.pc = retAddr then some s else
  match fuel, c.instr s.pc with
  | 0, _ => none
  | _, none => none
  | _, some (.ecall, _) => none
  | n + 1, some (i, len) => (execC len i s).bind (runC c n)

def main (args : List String) : IO UInt32 := do
  let [elf, entryS] := args | IO.eprintln "usage: ELF ENTRY"; return 2
  let some entry := entryS.toNat? | return 2
  let b ← IO.FS.readBinFile elf
  let .ok secs := Elf.sections b | return 1
  let some t := secs.find? (·.name == ".text") | return 1
  let halves := (List.range (t.size / 2)).map fun i =>
    BitVec.ofNat 16 ((b.get! (t.offset + 2 * i)).toNat + 256 * (b.get! (t.offset + 2 * i + 1)).toNat)
  let code : CCode := ⟨BitVec.ofNat 64 t.addr, halves.toArray⟩
  let input ← (← IO.getStdin).readBinToEnd
  let out ← IO.getStdout
  let mut pos := 0
  while pos + 8 ≤ input.size do
    let len := (List.range 8).foldl (fun acc k => acc + (input.get! (pos + k)).toNat * 256 ^ k) 0
    let bytes := input.extract (pos + 8) (pos + 8 + len)
    pos := pos + 8 + len
    let init : Word → Byte := fun a =>
      let o := (a - bufAt).toNat
      if o < len then BitVec.ofNat 8 (bytes.get! o).toNat
      else
        let so := (a - slot).toNat
        if so < 24 then (if so < 8 then 0xaa#8 else if so < 16 then 0xbb#8 else 0xcc#8) else 0
    let regs : Reg → Word := fun r =>
      if r.val = 10 then slot else if r.val = 11 then bufAt else if r.val = 12 then BitVec.ofNat 64 len
      else if r.val = 1 then retAddr else if r.val = 2 then 0x800000#64 else 0
    let s : State := { regs, pc := BitVec.ofNat 64 entry, mem := init, trace := [], exit := none }
    match runC code 10000000 s with
    | none => IO.eprintln "fault or no return"; return 1
    | some s' =>
      let res := (readBytes s'.mem slot 24) ++ readBytes s'.mem bufAt len
      out.write (ByteArray.mk (res.map (fun x => x.toNat.toUInt8)).toArray)
  out.flush
  return 0
