import NoCompiler.Tactic

/-
The structural rules of the profile in Lean (docs/isa/profile.md, rules R1
to R3), as an executable checker, and the theorem that makes them mean
something: a checked function only ever transfers control the way the rules
say (`Struct.cfi`).

The Rust checker (crates/nocompiler/src/profile.rs) decides the same rules; the
register, stack and frame rules R4 to R6 are in NoCompiler/Frame.lean. `nocompiler export` writes each conforming function's
structure as a `Struct.Func` and a `<name>_checked` theorem proved by
`decide`, so a function's conformance is a fact the kernel has checked.
-/
namespace NoCompiler
namespace Struct

inductive Kind | block | loop
  deriving DecidableEq, Repr

/-- A `block` or `loop` covering `[start, stop)`. -/
structure Node where
  kind : Kind
  start : Word
  stop : Word
  deriving DecidableEq, Repr

/-- A function: `len` instructions from `entry`, and its block/loop nodes. -/
structure Func where
  entry : Word
  len : Nat
  nodes : List Node
  deriving DecidableEq, Repr

namespace Func

/-- `pc` is one of the function's instruction addresses. -/
def contains (f : Func) (pc : Word) : Bool :=
  (pc - f.entry).toNat < 4 * f.len && (pc - f.entry).toNat % 4 == 0

/-- `t` is a structured target of a branch at `pc`: the end of a block
    enclosing `pc`, or the head of a loop enclosing `pc`. -/
def target (f : Func) (pc t : Word) : Bool :=
  f.nodes.any fun n =>
    (pc - n.start).toNat < (n.stop - n.start).toNat &&
      match n.kind with
      | .block => n.stop == t
      | .loop => n.start == t

end Func

def auipcVal (pc : Word) (hi : BitVec 20) : Word := pc + (hi.setWidth 32 <<< 12).signExtend 64

/-- The base register of a `jalr`. -/
def _root_.NoCompiler.Instr.jalrBase : Instr → Option Reg
  | .jalr _ rs1 _ => some rs1
  | _ => none

/-- The destination and immediate of an `auipc`. -/
def _root_.NoCompiler.Instr.auipcOf : Instr → Option (Reg × BitVec 20)
  | .auipc rd hi => some (rd, hi)
  | _ => none

theorem _root_.NoCompiler.Instr.jalrBase_some {i : Instr} {r : Reg} (h : i.jalrBase = some r) :
    ∃ rd off, i = .jalr rd r off := by
  cases i <;> (try cases h)
  exact ⟨_, _, rfl⟩

theorem _root_.NoCompiler.Instr.auipcOf_some {i : Instr} {r : Reg} {hi : BitVec 20} (h : i.auipcOf = some (r, hi)) :
    i = .auipc r hi := by
  cases i <;> (try cases h)
  rfl

/-- `jalr` at `j`, preceded by `auipc` into its base register at `p`. -/
def pairOf (j a : Option Instr) (p : Word) : Option (Reg × Word) :=
  match j.bind Instr.jalrBase, a.bind Instr.auipcOf with
  | some r, some (rd, hi) => if rd = r then some (r, auipcVal p hi) else none
  | _, _ => none

theorem pairOf_some {j a : Option Instr} {p : Word} {r : Reg} {v : Word}
    (h : pairOf j a p = some (r, v)) :
    (∃ rd off, j = some (.jalr rd r off)) ∧ ∃ hi, a = some (.auipc r hi) ∧ v = auipcVal p hi := by
  cases j with
  | none => simp [pairOf] at h
  | some j =>
    cases a with
    | none => simp [pairOf] at h
    | some a =>
      cases hj : j.jalrBase with
      | none => simp [pairOf, hj] at h
      | some r' =>
        cases ha : a.auipcOf with
        | none => simp [pairOf, hj, ha] at h
        | some rh =>
          obtain ⟨rd, hi⟩ := rh
          simp only [pairOf, Option.bind_some, hj, ha] at h
          split at h
          · rename_i heq
            cases h
            obtain ⟨rd', off, rfl⟩ := Instr.jalrBase_some hj
            subst heq
            exact ⟨⟨rd', off, rfl⟩, hi, by rw [Instr.auipcOf_some ha], rfl⟩
          · cases h

/-- `pc` is the `jalr` of an `auipc r, hi; jalr .., lo(r)` pair inside the
    function: the register and the value `auipc` left in it. -/
def pairAt (c : Code) (f : Func) (pc : Word) : Option (Reg × Word) :=
  if f.contains (pc - 4) then pairOf (c.instr pc) (c.instr (pc - 4)) (pc - 4) else none

theorem pairAt_some {c : Code} {f : Func} {pc : Word} {r : Reg} {v : Word}
    (h : pairAt c f pc = some (r, v)) :
    (∃ rd off, c.instr pc = some (.jalr rd r off)) ∧
      ∃ hi, c.instr (pc - 4) = some (.auipc r hi) ∧ v = auipcVal (pc - 4) hi := by
  unfold pairAt at h
  split at h
  · exact pairOf_some h
  · cases h

/-- Instructions after which control goes to the next one, and nowhere else. -/
def _root_.NoCompiler.Instr.plain : Instr → Bool
  | .branch .. | .jal .. | .jalr .. | .ecall => false
  | _ => true

/-- The rules at one address. -/
def instrOk (c : Code) (f : Func) (entries : List Word) (pc : Word) : Bool :=
  match c.instr pc with
  | none => false
  | some i =>
    let fall := f.contains (pc + 4)
    let local_ (t : Word) := f.contains t && f.target pc t && (pairAt c f t).isNone
    match i with
    | .branch _ _ _ off => fall && local_ (pc + off.signExtend 64)
    | .jal rd off =>
      let t := pc + off.signExtend 64
      if rd = 0 then local_ t || entries.contains t
      else rd == 1 && entries.contains t && fall
    | .jalr rd rs1 off =>
      if rd = 0 && rs1 = 1 && off = 0 then true
      else match pairAt c f pc with
        | some (r, v) =>
          let t := (v + off.signExtend 64) &&& ~~~1
          entries.contains t && ((rd == 1 && r == 1 && fall) || (rd == 0 && r == 6))
        | none => false
    | _ => fall

/-- R1 to R3 for every instruction of `f`. -/
def check (c : Code) (f : Func) (entries : List Word) : Bool :=
  (List.range f.len).all fun i => instrOk c f entries (f.entry + BitVec.ofNat 64 (4 * i))

/-! ## What a step does to the pc -/

theorem exec_plain {i : Instr} {s s' : State} (hp : Instr.plain i = true) (h : exec i s = some s') :
    s'.pc = s.pc + 4 := by
  cases i with
  | branch => cases hp
  | jal => cases hp
  | jalr => cases hp
  | ecall => cases hp
  | load op rd rs1 off =>
    unfold exec at h; dsimp only at h; split at h
    · cases h; simp
    · cases h
  | store op rs1 rs2 off =>
    unfold exec at h; dsimp only at h; split at h
    · cases h; simp
    · cases h
  | _ => unfold exec at h; cases h; simp

theorem exec_branch {op a b off} {s s' : State} (h : exec (.branch op a b off) s = some s') :
    s'.pc = s.pc + 4 ∨ s'.pc = s.pc + off.signExtend 64 := by
  simp only [exec, jumpTo] at h
  split at h
  · split at h
    · cases h; right; simp
    · cases h
  · cases h; left; simp

theorem exec_jal {rd off} {s s' : State} (h : exec (.jal rd off) s = some s') :
    s'.pc = s.pc + off.signExtend 64 ∧ (rd ≠ 0 → s'.reg rd = s.pc + 4) := by
  simp only [exec, jumpTo] at h
  split at h
  · cases h; exact ⟨by simp, fun h0 => by simp [State.reg_setReg_same _ _ _ h0]⟩
  · cases h

theorem exec_jalr {rd rs1 off} {s s' : State} (h : exec (.jalr rd rs1 off) s = some s') :
    s'.pc = (s.reg rs1 + off.signExtend 64) &&& ~~~1 ∧ (rd ≠ 0 → s'.reg rd = s.pc + 4) := by
  simp only [exec, jumpTo] at h
  split at h
  · cases h; exact ⟨by simp, fun h0 => by simp [State.reg_setReg_same _ _ _ h0]⟩
  · cases h

theorem exec_auipc {rd hi} {s s' : State} (h : exec (.auipc rd hi) s = some s') (h0 : rd ≠ 0) :
    s'.reg rd = auipcVal s.pc hi := by
  simp only [exec] at h
  cases h
  simp [State.reg_setReg_same _ _ _ h0, auipcVal]

theorem sys_pc {s s' : State} (h : Sys s s') : s'.pc = s.pc + 4 ∨ s'.exit ≠ none := by
  cases h <;> simp

/-! ## The theorem -/

/-- Inside the function, and if at the `jalr` of a pair, its register holds
    what the `auipc` put there. -/
def Inv (c : Code) (f : Func) (s : State) : Prop :=
  f.contains s.pc = true ∧ ∀ r v, pairAt c f s.pc = some (r, v) → s.reg r = v

/-- The ways control may leave an instruction of a checked function. -/
inductive Transfer (c : Code) (f : Func) (entries : List Word) (s s' : State) : Prop
  /-- To the next instruction. -/
  | next : s'.pc = s.pc + 4 → Inv c f s' → Transfer c f entries s s'
  /-- A branch or jump to the end of an enclosing block or the head of an
      enclosing loop. -/
  | local_ : f.target s.pc s'.pc = true → Inv c f s' → Transfer c f entries s s'
  /-- A call: to a function entry, returning to the next instruction. -/
  | call : entries.contains s'.pc = true → s'.reg Reg.ra = s.pc + 4 → Transfer c f entries s s'
  /-- A tail call to a function entry. -/
  | tail : entries.contains s'.pc = true → Transfer c f entries s s'
  /-- A return, to the address in ra. -/
  | ret : s'.pc = s.reg Reg.ra &&& ~~~1 → Transfer c f entries s s'
  /-- The process ended. -/
  | exit : s'.exit ≠ none → Transfer c f entries s s'

theorem check_at {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {pc : Word} (hpc : f.contains pc = true) : instrOk c f entries pc = true := by
  unfold check at hc
  unfold Func.contains at hpc
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hpc
  have hi := List.all_eq_true.1 hc ((pc - f.entry).toNat / 4) (List.mem_range.2 (by omega))
  have e : f.entry + BitVec.ofNat 64 (4 * ((pc - f.entry).toNat / 4)) = pc := by
    have : 4 * ((pc - f.entry).toNat / 4) = (pc - f.entry).toNat := by omega
    rw [this]; apply BitVec.eq_of_toNat_eq; simp; bv_omega
  rwa [e] at hi

theorem pairAt_next {c : Code} {f : Func} {pc : Word} {i : Instr} (hi : c.instr pc = some i)
    {r : Reg} {v : Word} (hp : pairAt c f (pc + 4) = some (r, v)) :
    ∃ hi', i = .auipc r hi' ∧ v = auipcVal pc hi' := by
  obtain ⟨_, hi', ha, hv⟩ := pairAt_some hp
  rw [show pc + 4 - 4 = pc by bv_omega] at ha hv
  rw [hi] at ha
  cases ha
  exact ⟨hi', rfl, hv⟩

/-- An inner register write keeps `Inv` at the next instruction unless the
    instruction is the `auipc` of a pair, which sets up exactly what `Inv`
    asks. -/
theorem inv_next {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {s s' : State} {i : Instr} (hi : c.instr s.pc = some i) (hx : exec i s = some s')
    (hpc : s'.pc = s.pc + 4) (hin : f.contains (s.pc + 4) = true) : Inv c f s' := by
  refine ⟨hpc ▸ hin, fun r v hp => ?_⟩
  rw [hpc] at hp
  obtain ⟨hi', rfl, rfl⟩ := pairAt_next hi hp
  -- The jalr after the auipc passed the check, so r is ra or t1, never x0.
  have hok := check_at hc hin
  have hr0 : r ≠ 0 := by
    intro h0; subst h0
    obtain ⟨⟨rd, off, hj⟩, _⟩ := pairAt_some hp
    unfold instrOk at hok
    rw [hj] at hok
    dsimp only at hok
    rw [hp] at hok
    simp at hok
  exact exec_auipc hx hr0

theorem cfi {c : Code} {f : Func} {entries : List Word} (hc : check c f entries = true)
    {P : Perm} {s s' : State} (hinv : Inv c f s) (hs : Step c P s s') :
    Transfer c f entries s s' := by
  obtain ⟨hin, hpair⟩ := hinv
  have hok := check_at hc hin
  cases hs with
  | sys _ hi _ hy =>
    unfold instrOk at hok
    rw [hi] at hok
    rcases sys_pc hy with hpc | hex
    · refine .next hpc ⟨hpc ▸ hok, fun r v hp => ?_⟩
      rw [hpc] at hp
      obtain ⟨_, h, _⟩ := pairAt_next hi hp
      cases h
    · exact .exit hex
  | @exec i _ hi _ hx =>
    unfold instrOk at hok
    rw [hi] at hok
    cases i with
    | branch op a b off =>
      simp only [Bool.and_eq_true] at hok
      obtain ⟨hfall, ⟨⟨htin, htgt⟩, hnone⟩⟩ := hok
      rcases exec_branch hx with hpc | hpc
      · exact .next hpc (inv_next hc hi hx hpc hfall)
      · refine .local_ (hpc ▸ htgt) ⟨hpc ▸ htin, fun r v hp => ?_⟩
        rw [hpc] at hp; rw [hp] at hnone; cases hnone
    | jal rd off =>
      obtain ⟨hpc, hlink⟩ := exec_jal hx
      by_cases h0 : rd = 0
      · simp only [h0, ite_true, Bool.or_eq_true, Bool.and_eq_true] at hok
        rcases hok with ⟨⟨htin, htgt⟩, hnone⟩ | hent
        · refine .local_ (hpc ▸ htgt) ⟨hpc ▸ htin, fun r v hp => ?_⟩
          rw [hpc] at hp; rw [hp] at hnone; cases hnone
        · exact .tail (hpc ▸ hent)
      · simp only [h0, ite_false, Bool.and_eq_true, beq_iff_eq] at hok
        obtain ⟨⟨rfl, hent⟩, _⟩ := hok
        exact .call (hpc ▸ hent) (hlink h0)
    | jalr rd rs1 off =>
      obtain ⟨hpc, hlink⟩ := exec_jalr hx
      by_cases hret : rd = 0 ∧ rs1 = 1 ∧ off = 0
      · obtain ⟨rfl, rfl, rfl⟩ := hret
        exact .ret (by rw [hpc]; simp)
      · have hret' : (decide (rd = 0) && decide (rs1 = 1) && decide (off = 0)) = false := by
          cases h1 : decide (rd = 0) <;> cases h2 : decide (rs1 = 1) <;>
            cases h3 : decide (off = 0) <;> simp_all
        simp only [hret', Bool.false_eq_true, ite_false] at hok
        cases hp : pairAt c f s.pc with
        | none => rw [hp] at hok; cases hok
        | some rv =>
          obtain ⟨r, v⟩ := rv
          rw [hp] at hok
          simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hok
          obtain ⟨hent, hk⟩ := hok
          -- The register holds what the auipc put there, and it is rs1.
          have hrs : r = rs1 := by
            obtain ⟨⟨_, _, hj⟩, _⟩ := pairAt_some hp
            rw [hi] at hj; cases hj; rfl
          subst hrs
          have hv := hpair r v hp
          have ht : s'.pc = (v + off.signExtend 64) &&& ~~~1 := by rw [hpc, hv]
          rcases hk with ⟨⟨rfl, rfl⟩, _⟩ | ⟨rfl, rfl⟩
          · exact .call (ht ▸ hent) (hlink (by decide))
          · exact .tail (ht ▸ hent)
    | ecall => simp [exec_ecall] at hx
    | _ =>
      have hpc := exec_plain rfl hx
      exact .next hpc (inv_next hc hi hx hpc hok)

/-- A run of the function starts in `Inv`. -/
theorem inv_entry {c : Code} {f : Func} {s : State} (hlen : 0 < f.len) (hsz : 4 * f.len ≤ 2 ^ 63)
    (hpc : s.pc = f.entry) :
    Inv c f s := by
  refine ⟨?_, fun r v hp => ?_⟩
  · rw [hpc]; simp [Func.contains]; omega
  · unfold pairAt at hp
    rw [hpc] at hp
    have : f.contains (f.entry - 4) = false := by
      simp only [Func.contains, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      left
      rw [show f.entry - 4 - f.entry = (-4 : Word) by bv_omega]
      have : ((-4 : Word)).toNat = 2 ^ 64 - 4 := by decide
      rw [this]
      omega
    rw [this] at hp; cases hp

end Struct
end NoCompiler
