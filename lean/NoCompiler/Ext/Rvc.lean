import NoCompiler.Auto

/-
EXTENSION, NOT PART OF THE nocompiler PROFILE: compressed (RVC) code.

The profile has fixed 32-bit instructions (docs/isa/profile.md). Ordinary
RV64GC code, which clang emits for `-march=rv64gc`, mixes 16-bit and 32-bit
instructions on 2-byte boundaries. This file extends the semantics as far as
proving such code in the same logic needs, and no further:

* `decodeC` expands a 16-bit RV64C instruction into the existing `Instr`
  (the expansion the RISC-V specification defines; the floating-point ones,
  C.EBREAK and the reserved encodings decode to nothing);
* `CCode` is a code image of halfwords: an instruction is fetched at a 2-byte
  aligned pc, and is 32-bit when its low two bits are 11, 16-bit otherwise;
* `execC n` is `exec` with the next pc and the link address at `pc + n`, and
  jump targets 2-byte aligned (instruction-address-misaligned with C enabled);
* `StepC`, `ReachC`, `ExecC` and `VerifiedC` are `Step`, `Reach`, `Exec` and
  `VerifiedImg` over `CCode`, with the same `Spec`, `Entry`, `Perm` and `Done`.
  The rules a proof uses (`trans`, `loop`, `cutpoints`, `exec_step`) are
  proved again here, the same way.

What this adds to the trusted base, for results about compressed code only:
`decodeC`, `CCode.instr` and `execC` (and the four definitions above). The
results about nocompiler binaries do not import this file. Checked against llvm-mc
(every 16-bit word, examples/demo/test/rvc_decode.py) and against qemu-riscv64 (the
compressed `cobs_decode` run in Lean and in qemu on the same inputs,
examples/demo/test/rvc_exec.py). Not done here: the adequacy theorems of
NoCompiler/Adequacy.lean for `StepC`.
-/
namespace NoCompiler

/-! ## Decoding -/

/-- Bits `lo .. lo+len-1` of a halfword. -/
@[inline] def cbits (h : BitVec 16) (lo len : Nat) : Nat := (h.toNat >>> lo) % 2 ^ len

/-- A register x8..x15, from a 3-bit field. -/
@[inline] def cregAt (h : BitVec 16) (lo : Nat) : Reg := ⟨8 + cbits h lo 3, by unfold cbits; omega⟩
@[inline] def cregFull (h : BitVec 16) (lo : Nat) : Reg := ⟨cbits h lo 5, Nat.mod_lt _ (by decide)⟩

/-- A sign-extended immediate of `n` bits as a 12-bit field. -/
def sx12 (v n : Nat) : BitVec 12 := (BitVec.ofNat n v).signExtend 12

/-- The 16-bit instructions of RV64C, as the 32-bit instructions they expand to. -/
def decodeC (h : BitVec 16) : Option Instr :=
  let op := cbits h 0 2
  let f3 := cbits h 13 3
  let rd := cregFull h 7
  let rs2 := cregFull h 2
  let rdp := cregAt h 7     -- rd'/rs1' in bits 9:7
  let rs2p := cregAt h 2    -- rd'/rs2' in bits 4:2
  -- the 6-bit immediate imm[5] = h[12], imm[4:0] = h[6:2]
  let imm6 := cbits h 12 1 * 32 + cbits h 2 5
  match op, f3 with
  -- Quadrant 0
  | 0, 0 =>
    let nz := cbits h 6 1 * 4 + cbits h 5 1 * 8 + cbits h 11 2 * 16 + cbits h 7 4 * 64
    if nz = 0 then none else some (.iop .addi rs2p 2 (BitVec.ofNat 12 nz))
  | 0, 2 => some (.load .lw rs2p rdp (BitVec.ofNat 12 (cbits h 6 1 * 4 + cbits h 10 3 * 8 + cbits h 5 1 * 64)))
  | 0, 3 => some (.load .ld rs2p rdp (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 5 2 * 64)))
  | 0, 6 => some (.store .sw rdp rs2p (BitVec.ofNat 12 (cbits h 6 1 * 4 + cbits h 10 3 * 8 + cbits h 5 1 * 64)))
  | 0, 7 => some (.store .sd rdp rs2p (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 5 2 * 64)))
  -- Quadrant 1
  | 1, 0 => some (.iop .addi rd rd (sx12 imm6 6))
  | 1, 1 => if rd.val = 0 then none else some (.addiw rd rd (sx12 imm6 6))
  | 1, 2 => some (.iop .addi rd 0 (sx12 imm6 6))
  | 1, 3 =>
    if rd.val = 2 then
      let nz := cbits h 6 1 * 16 + cbits h 2 1 * 32 + cbits h 5 1 * 64 + cbits h 3 2 * 128 +
        cbits h 12 1 * 512
      if nz = 0 then none else some (.iop .addi 2 2 (sx12 nz 10))
    else
      if imm6 = 0 then none else some (.lui rd ((BitVec.ofNat 6 imm6).signExtend 20))
  | 1, 4 =>
    match cbits h 10 2 with
    | 0 => some (.shift .srli rdp rdp (BitVec.ofNat 6 imm6))
    | 1 => some (.shift .srai rdp rdp (BitVec.ofNat 6 imm6))
    | 2 => some (.iop .andi rdp rdp (sx12 imm6 6))
    | _ =>
      match cbits h 12 1, cbits h 5 2 with
      | 0, 0 => some (.rop .sub rdp rdp rs2p)
      | 0, 1 => some (.rop .xor rdp rdp rs2p)
      | 0, 2 => some (.rop .or rdp rdp rs2p)
      | 0, 3 => some (.rop .and rdp rdp rs2p)
      | 1, 0 => some (.rwop .subw rdp rdp rs2p)
      | 1, 1 => some (.rwop .addw rdp rdp rs2p)
      | _, _ => none
  | 1, 5 =>
    let off := cbits h 3 3 * 2 + cbits h 11 1 * 16 + cbits h 2 1 * 32 + cbits h 7 1 * 64 +
      cbits h 6 1 * 128 + cbits h 9 2 * 256 + cbits h 8 1 * 1024 + cbits h 12 1 * 2048
    some (.jal 0 ((BitVec.ofNat 12 off).signExtend 21))
  | 1, 6 | 1, 7 =>
    let off := cbits h 3 2 * 2 + cbits h 10 2 * 8 + cbits h 2 1 * 32 + cbits h 5 2 * 64 +
      cbits h 12 1 * 256
    some (.branch (if f3 = 6 then .beq else .bne) rdp 0 ((BitVec.ofNat 9 off).signExtend 13))
  -- Quadrant 2
  | 2, 0 => some (.shift .slli rd rd (BitVec.ofNat 6 imm6))
  | 2, 2 =>
    if rd.val = 0 then none
    else some (.load .lw rd 2 (BitVec.ofNat 12 (cbits h 4 3 * 4 + cbits h 12 1 * 32 + cbits h 2 2 * 64)))
  | 2, 3 =>
    if rd.val = 0 then none
    else some (.load .ld rd 2 (BitVec.ofNat 12 (cbits h 5 2 * 8 + cbits h 12 1 * 32 + cbits h 2 3 * 64)))
  | 2, 4 =>
    match cbits h 12 1, rd.val, rs2.val with
    | 0, 0, 0 => none
    | 0, _, 0 => some (.jalr 0 rd 0)
    | 0, _, _ => some (.rop .add rd 0 rs2)
    | _, 0, 0 => none
    | _, _, 0 => some (.jalr 1 rd 0)
    | _, _, _ => some (.rop .add rd rd rs2)
  | 2, 6 => some (.store .sw 2 rs2 (BitVec.ofNat 12 (cbits h 9 4 * 4 + cbits h 7 2 * 64)))
  | 2, 7 => some (.store .sd 2 rs2 (BitVec.ofNat 12 (cbits h 10 3 * 8 + cbits h 7 3 * 64)))
  | _, _ => none

/-! ## Code images of halfwords -/

structure CCode where
  base : Word
  halves : Array (BitVec 16)

namespace CCode
def half (c : CCode) (pc : Word) : Option (BitVec 16) :=
  let off := (pc - c.base).toNat
  if off % 2 = 0 then c.halves[off / 2]? else none

/-- The instruction at `pc` and its length in bytes. -/
def instr (c : CCode) (pc : Word) : Option (Instr × Nat) :=
  match c.half pc with
  | none => none
  | some lo =>
    if lo.toNat % 4 = 3 then
      match c.half (pc + 2) with
      | none => none
      | some hi => (decode (hi ++ lo)).map (·, 4)
    else (decodeC lo).map (·, 2)
end CCode

/-! ## Semantics -/

/-- Continue at `t`, which must be 2-byte aligned. -/
def jumpToC (s : State) (t : Word) : Option State :=
  if aligned t 2 then some (s.setPc t) else none

/-- One step of an instruction `n` bytes long: control transfers as in
    `exec` with `pc + n` for the next instruction and 2-byte alignment;
    every other instruction is `exec`, followed by the pc `pc + n`. -/
def execC (n : Nat) (i : Instr) (s : State) : Option State :=
  let next := s.pc + BitVec.ofNat 64 n
  match i with
  | .jal rd off => jumpToC (s.setReg rd next) (s.pc + off.signExtend 64)
  | .jalr rd rs1 off =>
    let t := (s.reg rs1 + off.signExtend 64) &&& ~~~1
    jumpToC (s.setReg rd next) t
  | .branch op rs1 rs2 off =>
    if evalBr op (s.reg rs1) (s.reg rs2) then jumpToC s (s.pc + off.signExtend 64)
    else some (s.setPc next)
  | i => (exec i s).map (·.setPc next)

theorem Option.map_ite' {α β : Type} (f : α → β) (c : Prop) [Decidable c] (a b : Option α) :
    Option.map f (if c then a else b) = if c then Option.map f a else Option.map f b := by
  split <;> rfl

attribute [nocompiler_state] Option.map_ite' Option.map_some Option.map_none
attribute [irreducible] execC
attribute [nocompiler_sem] execC jumpToC Option.map_some Option.map_none

inductive StepC (c : CCode) (P : Perm) : State → State → Prop
  | exec {s s' : State} {i : Instr} {n : Nat} :
      s.exit = none → c.instr s.pc = some (i, n) → InstrOk P i s → execC n i s = some s' →
      StepC c P s s'
  | sys {s s' : State} :
      s.exit = none → c.instr s.pc = some (.ecall, 4) → SysOk P s → Sys s s' → StepC c P s s'

inductive ReachC (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) : State → Prop
  | done {s : State} : Q s → ReachC c P D Q s
  | step {s : State} :
      D.mem s.pc → (∃ s', StepC c P s s') → (∀ s', StepC c P s s' → ReachC c P D Q s') →
      ReachC c P D Q s

def ExecC (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) (s : State) : Prop :=
  ReachC c P D (fun s => Final D s ∧ Q s) s

/-- `Entry` for compressed code: the return address need only be 2-byte
    aligned, since a call in compressed code may sit at an address that is 2
    modulo 4 (and `jalr` clears only bit 0). Weaker than `Entry`, so a
    `VerifiedC` proof assumes less. -/
structure EntryC (D : Dom) (entry : Word) (s : State) : Prop where
  pc : s.pc = entry
  live : s.exit = none
  ret : ¬ D.mem (s.reg Reg.ra)
  retAligned : aligned (s.reg Reg.ra) 2
  sp : aligned (s.reg Reg.sp) 16

theorem and_not_one_of_aligned2 {x : Word} (h : aligned x 2) : x &&& ~~~1#64 = x := by
  unfold aligned at h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not]
  by_cases h0 : i = 0
  · subst h0
    have : x.getLsbD 0 = false := by
      rw [BitVec.getLsbD, Nat.testBit_zero]; simp; omega
    simpa [BitVec.getLsbD_eq_getElem] using this
  · simp [h0, hi]

/-- `jalr` returns to a 2-aligned address unchanged. -/
theorem ret_mask2 {x : Word} (h : aligned x 2) : x &&& 0xfffffffffffffffe#64 = x :=
  and_not_one_of_aligned2 h

/-- `VerifiedImg` for compressed code: the same specification and conclusion,
    entered under `EntryC`. -/
def VerifiedC {α : Type} (c : CCode) (D : Dom) (entry : Word) (sp : Spec α) : Prop :=
  ∀ a s, EntryC D entry s → sp.pre a s → ExecC c (sp.perm a s) D (sp.Done a s) s

/-! ## The rules, again -/

namespace ReachC
variable {c : CCode} {P : Perm} {D : Dom}

theorem trans {Q₁ Q₂ : State → Prop} {s} (h : ReachC c P D Q₁ s)
    (k : ∀ s', Q₁ s' → ReachC c P D Q₂ s') : ReachC c P D Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih => exact .step hd hex ih

theorem loop {Q : State → Prop} (I : State → Prop) (μ : State → Nat)
    (body : ∀ s, I s → ReachC c P D (fun s' => Q s' ∨ (I s' ∧ μ s' < μ s)) s) :
    ∀ s, I s → ReachC c P D Q s := by
  intro s hs
  induction hm : μ s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    refine trans (body s hs) ?_
    rintro s' (hq | ⟨hi, hlt⟩)
    · exact .done hq
    · exact ih _ (hm ▸ hlt) s' hi rfl

theorem cutpoints {Q : State → Prop} (inv : Word → State → Prop) (μ : Word → State → Nat)
    {s : State}
    (start : ∀ R : State → Prop, R = (fun s' => Q s' ∨ inv s'.pc s') → ReachC c P D R s)
    (body : ∀ u, inv u.pc u → ∀ R : State → Prop,
      R = (fun s' => Q s' ∨ (inv s'.pc s' ∧ μ s'.pc s' < μ u.pc u)) → ReachC c P D R u) :
    ReachC c P D Q s :=
  trans (start _ rfl) fun s' h => h.elim .done fun hi =>
    loop (fun u => inv u.pc u) (fun u => μ u.pc u) (fun u hu => body u hu _ rfl) s' hi

def opt (c : CCode) (P : Perm) (D : Dom) (Q : State → Prop) : Option State → Prop
  | none => False
  | some s => ReachC c P D Q s

@[simp, nocompiler_state] theorem opt_some {Q s} : opt c P D Q (some s) = ReachC c P D Q s := rfl
@[simp, nocompiler_state] theorem opt_none {Q} : opt c P D Q none = False := rfl
attribute [irreducible] opt

theorem opt_aligned {Q : State → Prop} {a : Word} {w : Nat} {s : State} (h : aligned a w) :
    opt c P D Q (if aligned a w then some s else none) = ReachC c P D Q s := by
  simp [h]

theorem exec_ecallC (n : Nat) (s : State) : execC n .ecall s = none := by
  unfold execC; simp [exec_ecall]

theorem exec_step {Q : State → Prop} {s : State} {i : Instr} {n : Nat}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some (i, n)) (hok : InstrOk P i s)
    (h : opt c P D Q (execC n i s)) : ReachC c P D Q s := by
  cases hxs : execC n i s with
  | none => rw [hxs, opt_none] at h; exact h.elim
  | some s₁ =>
    rw [hxs, opt_some] at h
    refine .step hd ⟨s₁, .exec hx hi hok hxs⟩ (fun s' h' => ?_)
    cases h' with
    | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; rw [hxs] at hx'; cases hx'; exact h
    | sys _ hi' _ _ =>
      rw [hi] at hi'; cases hi'; exact absurd hxs (by simp [exec_ecallC])

end ReachC

/-! ## Calls, syscalls and the frame property, for compressed code

The rules `nocompiler_auto_c` needs for functions with calls and syscalls,
as `NoCompiler/Lemmas.lean` and `NoCompiler/Spec.lean` give them for `Reach`: the
frame property of a step, `ReachC.bind`, `VerifiedC.frame`, `VerifiedC.call`
and the syscall step. -/

theorem execC_frame {n : Nat} {i : Instr} {s s' : State} (h : execC n i s = some s') :
    s'.mem = s.mem ∨ ∃ op rs1 rs2 off, i = .store op rs1 rs2 off ∧
      s'.mem = writeLE s.mem (ea s rs1 off) (s.reg rs2).toNat op.width := by
  unfold execC at h
  cases i with
  | jal rd off => simp only [jumpToC] at h; split at h <;> cases h; left; simp
  | jalr rd rs1 off => simp only [jumpToC] at h; split at h <;> cases h; left; simp
  | branch op rs1 rs2 off =>
    simp only [jumpToC] at h
    split at h
    · split at h <;> cases h; left; simp
    · cases h; left; simp
  | _ =>
    obtain ⟨s1, h1, rfl⟩ := Option.map_eq_some_iff.1 h
    rcases exec_frame h1 with e | ⟨op, rs1, rs2, off, hi, e⟩
    · left; simpa using e
    · right; exact ⟨op, rs1, rs2, off, hi, by simpa using e⟩

theorem StepC.frame {c : CCode} {P : Perm} {s s' : State} (h : StepC c P s s') (x : Word)
    (hx : ¬ P.writable x) : s'.mem x = s.mem x := by
  cases h with
  | exec _ _ hok hxs =>
    rcases execC_frame hxs with e | ⟨op, rs1, rs2, off, rfl, e⟩
    · rw [e]
    · rw [e]
      apply writeLE_other
      rcases hok with h0 | ⟨r, hr, hc⟩
      · exact absurd h0 (Nat.ne_of_gt (StOp.width_pos op))
      · exact Nat.le_of_not_lt fun hlt => hx ⟨r, hr, Region.covers_mem hc hlt⟩
  | sys _ _ hok hy =>
    cases hy with
    | writeOk => simp
    | writeErr => simp
    | exit => simp
    | readErr => simp
    | readOk ds hn hlen hmax =>
      simp only [State.emit_mem, State.setMem_mem]
      apply writeBytes_other
      rcases hok.2 hn with h0 | ⟨r, hr, hc⟩
      · omega
      · exact Nat.le_of_not_lt fun hlt =>
          hx ⟨r, hr, Region.covers_mem (n := ds.length) (by unfold Region.covers at *; omega) hlt⟩

theorem StepC.instrOk {c P s s'} (h : StepC c P s s') :
    ∃ i n, c.instr s.pc = some (i, n) ∧ InstrOk P i s ∧ s.exit = none := by
  cases h with
  | exec he hi hok _ => exact ⟨_, _, hi, hok, he⟩
  | sys he hi hok _ => exact ⟨_, _, hi, hok, he⟩

theorem StepC.restrict {c P Q s s₁ s'} (h : StepC c P s s₁) (h' : StepC c Q s s') : StepC c P s s' := by
  obtain ⟨i, n, hi, hok, _⟩ := h.instrOk
  cases h' with
  | exec he hi' _ hx => rw [hi] at hi'; cases hi'; exact .exec he hi hok hx
  | sys he hi' _ hy => rw [hi] at hi'; cases hi'; exact .sys he hi hok hy

theorem StepC.mono {c P Q s s'} (hle : P.le Q) (h : StepC c P s s') : StepC c Q s s' := by
  cases h with
  | exec he hi hok hx => exact .exec he hi (InstrOk.mono hle hok) hx
  | sys he hi hok hy => exact .sys he hi (InstrOk.mono (i := .ecall) hle hok) hy

namespace ReachC
variable {c : CCode} {P : Perm} {D : Dom}

theorem mono {Q Q' : State → Prop} (hq : ∀ s, Q s → Q' s) {s} (h : ReachC c P D Q s) :
    ReachC c P D Q' s := by
  induction h with
  | done hq' => exact .done (hq _ hq')
  | step hd hex _ ih => exact .step hd hex ih

theorem bind {P₁ P₂ : Perm} {D₁ D₂ : Dom} {Q₁ Q₂ : State → Prop} {s}
    (h : ReachC c P₁ D₁ Q₁ s) (hP : P₁.le P₂) (hD : D₁.sub D₂)
    (k : ∀ s', Q₁ s' → ReachC c P₂ D₂ Q₂ s') : ReachC c P₂ D₂ Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hd hex _ ih =>
    obtain ⟨s₁, h₁⟩ := hex
    exact .step (hD _ hd) ⟨s₁, h₁.mono hP⟩ (fun s' h' => ih s' (h₁.restrict h'))

theorem inv {Q I : State → Prop} (hI : ∀ u u', I u → StepC c P u u' → I u') {s}
    (h : ReachC c P D Q s) (hs : I s) : ReachC c P D (fun u => Q u ∧ I u) s := by
  induction h with
  | done hq => exact .done ⟨hq, hs⟩
  | step hd hex _ ih => exact .step hd hex (fun s' h' => ih s' h' (hI _ _ hs h'))

theorem frame {Q : State → Prop} {s : State} (h : ReachC c P D Q s) :
    ReachC c P D (fun u => Q u ∧ ∀ x, ¬ P.writable x → u.mem x = s.mem x) s :=
  ReachC.inv (I := fun u => ∀ x, ¬ P.writable x → u.mem x = s.mem x)
    (fun _ _ hu hs x hx => (hs.frame x hx).trans (hu x hx)) h (fun _ _ => rfl)

/-- Step over an ECALL: every outcome the environment allows has to reach `Q`. -/
theorem sys_step {Q : State → Prop} {s : State}
    (hd : D.mem s.pc) (hx : s.exit = none) (hi : c.instr s.pc = some (.ecall, 4)) (hok : SysOk P s)
    (hex : ∃ s', Sys s s') (h : ∀ s', Sys s s' → ReachC c P D Q s') : ReachC c P D Q s := by
  obtain ⟨s₁, h₁⟩ := hex
  refine .step hd ⟨s₁, .sys hx hi hok h₁⟩ (fun s' h' => ?_)
  cases h' with
  | exec _ hi' _ hx' => rw [hi] at hi'; cases hi'; simp [exec_ecallC] at hx'
  | sys _ _ _ hy => exact h _ hy
end ReachC

variable {c : CCode} {α : Type}

theorem VerifiedC.frame {D : Dom} {entry : Word} {sp : Spec α} (h : VerifiedC c D entry sp)
    (a : α) (s : State) (he : EntryC D entry s) (hpre : sp.pre a s) :
    ExecC c (sp.perm a s) D
      (fun s' => sp.Done a s s' ∧ ∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) s :=
  ReachC.mono (fun _ ⟨⟨hf, hd⟩, hm⟩ => ⟨hf, hd, hm⟩) (ReachC.frame (h a s he hpre))

/-- The call rule, for compressed code. -/
theorem VerifiedC.call {Dg D : Dom} {entry : Word} {sp : Spec α} {P : Perm}
    {Q : State → Prop} {s : State} (hg : VerifiedC c Dg entry sp) (a : α)
    (he : EntryC Dg entry s) (hpre : sp.pre a s) (hD : Dg.sub D) (hP : (sp.perm a s).le P)
    (k : ∀ s', sp.Done a s s' → (∀ x, ¬ (sp.perm a s).writable x → s'.mem x = s.mem x) →
      ReachC c P D Q s') : ReachC c P D Q s :=
  ReachC.bind (hg.frame a s he hpre) hP hD (fun s' ⟨_, hd, hm⟩ => k s' hd hm)

/-! ## The registers a function writes, and its instruction addresses -/

namespace Auto
/-- The registers the instructions in `[entry, entry + bytes)` write, walking
    instruction by instruction. -/
def writesC (c : CCode) (entry : Word) (bytes : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, off =>
      if off ≥ bytes then [] else
      match c.instr (entry + BitVec.ofNat 64 off) with
      | some (i, n) => (rd? i).toList ++ go fuel (off + n)
      | none => go fuel (off + 2)
  ((go bytes 0).eraseDups).filter (· ≠ 0)

/-- The addresses of the ECALLs in `[entry, entry + bytes)`. -/
def ecallsC (c : CCode) (entry : Word) (bytes : Nat) : List Nat :=
  let rec go : Nat → Nat → List Nat
    | 0, _ => []
    | fuel + 1, off =>
      if off ≥ bytes then [] else
      match c.instr (entry + BitVec.ofNat 64 off) with
      | some (.ecall, n) => (entry + BitVec.ofNat 64 off).toNat :: go fuel (off + n)
      | some (_, n) => go fuel (off + n)
      | none => go fuel (off + 2)
  go bytes 0

/-- The prologue at `entry`, as `frameOf` gives it for 32-bit code:
    `addi sp, sp, -N` (or `c.addi16sp`) and the `sd`/`c.sdsp` after it. -/
def frameOfC (c : CCode) (entry : Word) : List Nat :=
  match c.instr entry with
  | some (.iop .addi 2 2 imm, n0) =>
    if 2048 ≤ imm.toNat then
      let rec go : Nat → Word → List Nat
        | 0, _ => []
        | fuel + 1, pc =>
          match c.instr pc with
          | some (.store .sd 2 r off, n) => off.toNat :: r.val :: go fuel (pc + BitVec.ofNat 64 n)
          | _ => []
      (4096 - imm.toNat) :: go 32 (entry + BitVec.ofNat 64 n0)
    else []
  | _ => []
end Auto

end NoCompiler

/-! ## `nocompiler_auto_c`: the symbolic run on compressed code

The same driver as `nocompiler_auto` (NoCompiler/Auto.lean) over `ReachC`. There is no
block/loop tree here, so the cut points are the caller's: an invariant at a
set of addresses that every cycle of the function's control flow passes
through. Nothing checks that the set is enough before the run; if it is not,
a run goes around a loop until its step bound and fails. -/
namespace NoCompiler.Auto
open Lean Elab Tactic Meta

def cFlavor : Flavor :=
  { reach := ``ReachC, opt := ``ReachC.opt, instr := ``CCode.instr, exec := ``ExecC,
    execStep := ``ReachC.exec_step, done := ``ReachC.done, optSome := ``ReachC.opt_some,
    optAligned := ``ReachC.opt_aligned, cutpoints := ``ReachC.cutpoints,
    verified := ``VerifiedC, callRule := ``VerifiedC.call, sysStep := ``ReachC.sys_step,
    entry := ``EntryC, retMask := ``ret_mask2, retTwo := ``id }

/-- `nocompiler_auto_c entry size s he [facts] (loop_inv pc inv measure μ)*`: as
    `nocompiler_auto`, for the function of `size` bytes at `entry` of a `CCode`. -/
syntax (name := nocompilerAutoC) "nocompiler_auto_c " term:max term:max ident ident
  (" [" Lean.Parser.Tactic.simpArg,* "]")? (" calls " "[" term,* "]")? (ppLine nocompilerCut)* : tactic

@[tactic nocompilerAutoC] def evalNoCompilerAutoC : Tactic := fun stx => do
  let call ← parseCall cFlavor stx[3] stx[4] stx[5] stx[7].getArgs
  let callees ← parseCallees cFlavor stx[6]
  let entryE ← Term.elabTerm stx[1] (some (mkConst ``Word))
  let sizeE ← Term.elabTerm stx[2] (some (mkConst ``Nat))
  let entryN ← evalNat (← mkAppM ``BitVec.toNat #[entryE])
  let rsList ← evalNatList (mkApp3 (mkConst ``writesC) call.code entryE sizeE)
  let rsList := if callees.isEmpty then rsList else
    (rsList ++ nonPreserved.filter (fun r => r != 1 || rsList.contains 1)).eraseDups
  let ecallList ← evalNatList (mkApp3 (mkConst ``ecallsC) call.code entryE sizeE)
  let frameList ← evalNatList (mkApp2 (mkConst ``frameOfC) call.code entryE)
  autoCore cFlavor call (call.cuts.toList.map (·.1)) rsList entryN callees ecallList frameList

end NoCompiler.Auto
