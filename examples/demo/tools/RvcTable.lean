import NoCompiler.Ext.Rvc

/-
For examples/demo/test/rvc_decode.py: every 16-bit word that is not the low half of a
32-bit instruction, and what `decodeC` makes of it, as the 32-bit word of
the same instruction (or `none`), written by `NoCompiler.encode`. Each word is
checked here to decode (by the trusted 32-bit `decode`) to exactly the
instruction `decodeC` gave, so the comparison with
llvm-mc is a comparison of `decodeC` itself.

  lake env lean --run ../examples/demo/tools/RvcTable.lean > table.txt
-/
open NoCompiler

def main : IO UInt32 := do
  let mut bad := 0
  for h in List.range 65536 do
    if h % 4 = 3 then continue
    match decodeC (BitVec.ofNat 16 h) with
    | none => IO.println s!"{h} none"
    | some i =>
      let w := NoCompiler.encode i
      if decode w = some i then IO.println s!"{h} {w.toNat}"
      else IO.println s!"{h} misencoded {repr i}"; bad := bad + 1
  return if bad = 0 then 0 else 1
