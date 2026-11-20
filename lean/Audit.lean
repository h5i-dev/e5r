import Examples

/-
`lake build e5r-audit && lake exe e5r-audit` (from lean/): the checks that tie
the proofs to the binaries.

At build time, `#assert_standard_axioms` fails the build if a listed theorem
depends on any axiom beyond Lean's three standard ones (propext,
Classical.choice, Quot.sound): no `sorry`, no `native_decide`, no
`ofReduceBool`, no axiom of our own. At run time, `main` reads each committed ELF file with the
Lean reader in E5R/Elf.lean and checks that its `.text` is word for word the
image the proofs are about, and that every data section (`.rodata`, `.data`,
`.bss`, ...) is byte for byte the exported segment.
-/
open E5R

open Lean Elab Command in
/-- Fail unless the theorem depends on no axiom beyond Lean's standard three. -/
elab "#assert_standard_axioms " id:ident : command => do
  let n ← liftCoreM (realizeGlobalConstNoOverload id)
  let axs ← liftCoreM (Lean.collectAxioms n)
  let bad := axs.filter (fun a => !([``propext, ``Classical.choice, ``Quot.sound].contains a))
  unless bad.isEmpty do throwError "{n} depends on {bad.toList}"

-- The adequacy theorems and the program-logic rules every proof builds on.
#assert_standard_axioms E5R.Exec.hw_safe
#assert_standard_axioms E5R.Exec.hw_final
#assert_standard_axioms E5R.Exec.hw_terminates
#assert_standard_axioms E5R.Reach.bind
#assert_standard_axioms E5R.Reach.loop
#assert_standard_axioms E5R.Reach.exec_step
#assert_standard_axioms E5R.Reach.sys_step
#assert_standard_axioms E5R.Reach.frame
#assert_standard_axioms E5R.Verified.call
#assert_standard_axioms E5R.Verified.frame
#assert_standard_axioms E5R.Verified.hw
-- The examples.
#assert_standard_axioms Examples.Sum.sum_verified
#assert_standard_axioms Examples.Sum.sum_hw
#assert_standard_axioms Examples.Sum2.sum2_verified
#assert_standard_axioms Examples.Hello.write_all_verified
#assert_standard_axioms Examples.Hello.hello_verified

/-- Each committed binary (relative to the repository root), and the code
    image and data segments its proofs use. -/
def images : List (String × Code × List Segment) :=
  [("examples/elf/sum.elf", Examples.Sum.Image.code, Examples.Sum.Image.segments),
   ("examples/elf/hello.elf", Examples.Hello.Image.code, Examples.Hello.Image.segments)]

def checkImage (root : System.FilePath) (path : String) (c : Code) (segs : List Segment) :
    IO Bool := do
  let bytes ← IO.FS.readBinFile (root / path)
  match Elf.text bytes, Elf.segments bytes with
  | .error e, _ | _, .error e => IO.println s!"FAIL {path}: {e}"; return false
  | .ok t, .ok ds =>
    if t.base != c.base then
      IO.println s!"FAIL {path}: .text at {t.base.toNat}, image at {c.base.toNat}"; return false
    if t.words != c.words then
      IO.println s!"FAIL {path}: .text differs from the image ({t.words.size} words, image {c.words.size})"
      return false
    if ds.map (·.name) != segs.map (·.name) then
      IO.println s!"FAIL {path}: data sections {ds.map (·.name)}, image {segs.map (·.name)}"
      return false
    for (d, g) in ds.zip segs do
      if d != g then
        IO.println s!"FAIL {path}: {d.name} differs from the image (address, size, contents or writability)"
        return false
    let n := (segs.map (·.bytes.size)).foldl (· + ·) 0
    IO.println s!"ok   {path}: {c.words.size} words at {c.base.toNat} and {segs.length} data sections ({n} bytes) match the image"
    return true

def main (args : List String) : IO UInt32 := do
  let root : System.FilePath := args.headD ".."
  let mut ok := true
  for (p, c, segs) in images do
    ok := (← checkImage root p c segs) && ok
  return if ok then 0 else 1
