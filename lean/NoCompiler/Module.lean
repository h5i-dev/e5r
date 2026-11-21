import NoCompiler.Spec
import NoCompiler.Image

/-
Modules, layouts and linking (docs/isa/v1.md, "Verified takes the placement").

The unit of proof is a module: relocatable functions (their words, with the
fields a relocation fills left zero, and the relocations) and data. A layout
`L` gives every symbol an address; `M.link L` computes the code image the
functions make at that layout, and `M.segments L` the data.

`Verified M f spec` quantifies over every layout the module can be linked at
(`M.Ok L`), with a specification `spec : Layout → Spec α` that may name the
layout's addresses (a function's data moves with the layout): the claim is still about the machine's `Exec` over the linked
image, so the adequacy theorems apply at each layout unchanged. `link` is not
trusted: `nocompiler-audit` evaluates it at the layout read from an ELF's
symbol table and compares it with the ELF's bytes.

The relocations are the ones medany code has (docs/isa/toolchain.md):
`R_RISCV_CALL_PLT` (an `auipc`/`jalr` pair), `R_RISCV_PCREL_HI20` (an
`auipc`), and `R_RISCV_PCREL_LO12_I`/`_S` (the low part, in an I- or S-type
immediate, measured from the pc of the `auipc` it pairs with).
-/
namespace NoCompiler

/-- A symbol: a function or a data section, by name. -/
abbrev Sym := String

inductive RelocKind
  /-- `auipc` + `jalr`: both words, the distance from the `auipc`. -/
  | call
  /-- `auipc`: the high 20 bits of the distance. -/
  | pcrelHi
  /-- The low 12 bits, in an I-type immediate (`addi`, loads, `jalr`). -/
  | pcrelLoI
  /-- The low 12 bits, in an S-type immediate (stores). -/
  | pcrelLoS
  deriving DecidableEq, Repr

structure Reloc where
  /-- Byte offset in the function of the word patched (for `call`, of the `auipc`). -/
  off : Nat
  kind : RelocKind
  sym : Sym
  addend : Int := 0
  /-- Byte offset of the `auipc` whose pc the distance is measured from
      (`off` itself for `call` and `pcrelHi`). -/
  hiOff : Nat := off
  deriving DecidableEq, Repr

/-- A relocatable function: its words, with every relocated field zero. -/
structure RFunc where
  name : Sym
  words : List (BitVec 32)
  relocs : List Reloc := []
  deriving DecidableEq, Repr

/-- A data section, as a symbol. -/
structure RData where
  name : Sym
  bytes : List Byte
  writable : Bool := false
  deriving DecidableEq, Repr

structure Module where
  funcs : List RFunc
  data : List RData := []
  deriving DecidableEq, Repr

instance : Append Module := ⟨fun M M' => ⟨M.funcs ++ M'.funcs, M.data ++ M'.data⟩⟩

/-- Where everything goes: an address per symbol, and the extent of `.text`. -/
structure Layout where
  addr : Sym → Word
  /-- The start of the code image. -/
  base : Word
  /-- Its length in words. -/
  size : Nat

/-! ## Patching -/

namespace Reloc

/-- The high part of a pc-relative distance, as `auipc` adds it back. -/
def hi20 (d : Word) : BitVec 32 := ((d + 0x800#64) >>> 12).setWidth 32 <<< 12
/-- The low part, sign-extended by the instruction. -/
def lo12 (d : Word) : BitVec 32 := (d.setWidth 12).setWidth 32

def patchU (w : BitVec 32) (d : Word) : BitVec 32 := w ||| hi20 d
def patchI (w : BitVec 32) (d : Word) : BitVec 32 := w ||| (lo12 d <<< 20)
def patchS (w : BitVec 32) (d : Word) : BitVec 32 :=
  w ||| ((lo12 d &&& 0x1f#32) <<< 7) ||| ((lo12 d >>> 5) <<< 25)

/-- The distance this relocation encodes, for function `f` at layout `L`. -/
def dist (r : Reloc) (L : Layout) (f : Sym) : Word :=
  L.addr r.sym + BitVec.ofInt 64 r.addend - (L.addr f + BitVec.ofNat 64 r.hiOff)

def apply (r : Reloc) (L : Layout) (f : Sym) (ws : List (BitVec 32)) : List (BitVec 32) :=
  let d := r.dist L f
  let k := r.off / 4
  match r.kind with
  | .call => (ws.modify k (patchU · d)).modify (k + 1) (patchI · d)
  | .pcrelHi => ws.modify k (patchU · d)
  | .pcrelLoI => ws.modify k (patchI · d)
  | .pcrelLoS => ws.modify k (patchS · d)

/-- The distance fits: `auipc` + a 12-bit immediate reach about ±2 GiB. -/
def InRange (r : Reloc) (L : Layout) (f : Sym) : Prop :=
  -(2 : Int) ^ 31 - 2 ^ 11 ≤ (r.dist L f).toInt ∧ (r.dist L f).toInt < 2 ^ 31 - 2 ^ 11

instance (r : Reloc) (L : Layout) (f : Sym) : Decidable (r.InRange L f) :=
  inferInstanceAs (Decidable (_ ∧ _))

end Reloc

/-- The words of `f` at layout `L`. -/
def RFunc.patched (f : RFunc) (L : Layout) : List (BitVec 32) :=
  f.relocs.foldl (fun ws r => r.apply L f.name ws) f.words

/-- The code bytes of `f` at `L`. -/
def RFunc.region (f : RFunc) (L : Layout) : Word × Nat := (L.addr f.name, 4 * f.words.length)

/-- The functions `f` calls or tail-calls. -/
def RFunc.callees (f : RFunc) : List Sym :=
  (f.relocs.filter (·.kind = .call)).map (·.sym)

/-! ## The linked image -/

namespace Module

def func? (M : Module) (f : Sym) : Option RFunc := M.funcs.find? (·.name = f)

/-- The word at `x`: from the function whose code covers it, else 0. -/
def wordAt (M : Module) (L : Layout) (x : Word) : BitVec 32 :=
  match M.funcs.find? (fun f => decide ((x - L.addr f.name).toNat < 4 * f.words.length)) with
  | some f => (f.patched L).getD ((x - L.addr f.name).toNat / 4) 0
  | none => 0

def link (M : Module) (L : Layout) : Code :=
  ⟨L.base, ((List.range L.size).map fun i => M.wordAt L (L.base + BitVec.ofNat 64 (4 * i))).toArray⟩

/-- The data sections at `L`. -/
def segments (M : Module) (L : Layout) : List Segment :=
  M.data.map fun d => ⟨d.name, L.addr d.name, d.bytes.toArray, d.writable⟩

/-- The functions `f` reaches through calls, `f` first (at most `n` levels:
    the call graph of a module is acyclic in v1, so `M.funcs.length` levels are
    all of it). -/
def reach (M : Module) : Nat → Sym → List Sym
  | 0, f => [f]
  | n + 1, f => f :: ((M.func? f).map (fun g => g.callees.flatMap (M.reach n))).getD []

/-- The code region of `f` and of everything it calls. -/
def dom (M : Module) (L : Layout) (f : Sym) : Dom :=
  ((M.reach M.funcs.length f).filterMap M.func?).map (·.region L)

/-- The layout is one the module can be linked at: the code image is aligned
    and fits the address space, every function is 4-byte aligned, inside the
    image and disjoint from every other, names are unique, every relocation is
    in reach and inside its function. (A relocation may name a symbol of
    another module: `Verified.mono` adds modules.) -/
structure Ok (M : Module) (L : Layout) : Prop where
  base : aligned L.base 4
  size : 4 * L.size < 2 ^ 64
  names : (M.funcs.map (·.name)).Nodup
  funcs : ∀ f ∈ M.funcs, aligned (L.addr f.name) 4 ∧
    (L.addr f.name - L.base).toNat + 4 * f.words.length ≤ 4 * L.size
  disjoint : ∀ f ∈ M.funcs, ∀ g ∈ M.funcs, f.name ≠ g.name →
    4 * f.words.length ≤ (L.addr g.name - L.addr f.name).toNat
  relocs : ∀ f ∈ M.funcs, ∀ r ∈ f.relocs, r.InRange L f.name ∧
    r.off % 4 = 0 ∧ r.off + (if r.kind = .call then 8 else 4) ≤ 4 * f.words.length

instance (M : Module) (L : Layout) : Decidable (M.Ok L) :=
  decidable_of_iff (aligned L.base 4 ∧ 4 * L.size < 2 ^ 64 ∧ (M.funcs.map (·.name)).Nodup ∧
      (∀ f ∈ M.funcs, aligned (L.addr f.name) 4 ∧
        (L.addr f.name - L.base).toNat + 4 * f.words.length ≤ 4 * L.size) ∧
      (∀ f ∈ M.funcs, ∀ g ∈ M.funcs, f.name ≠ g.name →
        4 * f.words.length ≤ (L.addr g.name - L.addr f.name).toNat) ∧
      (∀ f ∈ M.funcs, ∀ r ∈ f.relocs, r.InRange L f.name ∧
        r.off % 4 = 0 ∧ r.off + (if r.kind = .call then 8 else 4) ≤ 4 * f.words.length))
    ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩, fun ⟨a, b, c, d, e, f⟩ => ⟨a, b, c, d, e, f⟩⟩

end Module

/-! ## Verified, over every layout -/

/-- `f` meets `spec L` wherever the module is linked (docs/isa/v1.md): for
    every layout `L` the module can be linked at, `f`'s code in the image
    `M.link L`, entered at `L.addr f`, is `VerifiedImg` (NoCompiler/Spec.lean)
    for the specification at that layout. The specification depends on the
    layout because a function's data does: a spec about a table names it as
    `L.addr "table"`. One that names no address is `fun _ => sp`. -/
def Verified {α : Type} (M : Module) (f : Sym) (spec : Layout → Spec α) : Prop :=
  ∀ L, M.Ok L → VerifiedImg (M.link L) (M.dom L f) (L.addr f) (spec L)

/-- At one layout: the code-level statement, about that image. -/
theorem Verified.img {α : Type} {M : Module} {f : Sym} {spec : Layout → Spec α}
    (h : Verified M f spec) {L : Layout} (hL : M.Ok L) :
    VerifiedImg (M.link L) (M.dom L f) (L.addr f) (spec L) :=
  h L hL

/-! ## Code that agrees on a region -/

/-- A run inside `D` only fetches instructions in `D`: two images that agree
    there have the same runs. -/
theorem Reach.congr_code {c c' : Code} {P : Perm} {D : Dom} {Q : State → Prop}
    (hc : ∀ x, D.mem x → c'.instr x = c.instr x) {s : State} (h : Reach c P D Q s) :
    Reach c' P D Q s := by
  have hstep : ∀ {u u'}, D.mem u.pc → Step c' P u u' → Step c P u u' := by
    intro u u' hd st
    cases st with
    | exec he hi hok hx => exact .exec he (hc _ hd ▸ hi) hok hx
    | sys he hi hok hy => exact .sys he (hc _ hd ▸ hi) hok hy
  induction h with
  | done hq => exact .done hq
  | step hd hex _ ih =>
    obtain ⟨u, st⟩ := hex
    refine .step hd ⟨u, ?_⟩ (fun u' st' => ih u' (hstep hd st'))
    cases st with
    | exec he hi hok hx => exact .exec he ((hc _ hd).symm ▸ hi) hok hx
    | sys he hi hok hy => exact .sys he ((hc _ hd).symm ▸ hi) hok hy

theorem VerifiedImg.congr_code {α : Type} {c c' : Code} {D : Dom} {e : Word} {spec : Spec α}
    (hc : ∀ x, D.mem x → c'.instr x = c.instr x) (h : VerifiedImg c D e spec) :
    VerifiedImg c' D e spec :=
  fun a s he hpre => Reach.congr_code hc (h a s he hpre)

end NoCompiler
