import Projects.thermostat.HeadFieldsRegs
namespace E5R.Thermostat.HeadFieldsConstants
open E5R E5R.Thermostat HttpRequestSpec

/-- The stable constants only. In particular, this does not assume the TE
    register already reflects a newly stored TE flag before its real reload. -/
structure At (c : Core) (sp : Word) (length minor : Nat) : Prop where
  stack : c.get 2=sp
  lf : c.get 16=10#32
  cr : c.get 17=13#32
  tcharMin : c.get 5=33#32
  digitMin : c.get 6=48#32
  maskWidth : c.get 7=14#32
  colon : c.get 28=58#32
  upperEnd : c.get 27=91#32
  version : c.get 8=BitVec.ofNat 32 minor
  inverse : c.get 18=BitVec.ofNat 32 (1-minor)
  negLength : c.get 22=0#32-BitVec.ofNat 32 length

def protectedRegs : List Reg := [2,16,17,5,6,7,28,27,8,18,22]

theorem of_regs {c sp i length minor f} (h : HeadFieldsRegs.At c sp i length minor f) : At c sp length minor :=
  ⟨h.stack,h.lf,h.cr,h.tcharMin,h.digitMin,h.maskWidth,h.colon,h.upperEnd,h.version,h.inverse,h.negLength⟩

theorem preserve {c d sp length minor} (h : At c sp length minor)
    (frame : ∀ r : Reg, r∈protectedRegs → d.get r=c.get r) : At d sp length minor := by
  exact ⟨(frame 2 (by decide)).trans h.stack,
    (frame 16 (by decide)).trans h.lf,
    (frame 17 (by decide)).trans h.cr,
    (frame 5 (by decide)).trans h.tcharMin,
    (frame 6 (by decide)).trans h.digitMin,
    (frame 7 (by decide)).trans h.maskWidth,
    (frame 28 (by decide)).trans h.colon,
    (frame 27 (by decide)).trans h.upperEnd,
    (frame 8 (by decide)).trans h.version,
    (frame 18 (by decide)).trans h.inverse,
    (frame 22 (by decide)).trans h.negLength⟩

theorem commit_regs : ∀ r : Reg, r∈protectedRegs → r≠9 ∧ r≠10 ∧ r≠23 ∧ r≠11 ∧ r≠21 ∧ r≠24 := by decide +kernel

theorem loop {c sp i length minor f} (h : At c sp length minor)
    (hp : c.pc=0x80002f58#32) (position : c.get 24=BitVec.ofNat 32 i)
    (count : c.get 9=BitVec.ofNat 32 f.headers.length) (te : c.get 23=(if f.te then 1#32 else 0#32)) :
    HeadFieldsRegs.At c sp i length minor f :=
  ⟨hp,h.stack,position,h.lf,h.cr,h.tcharMin,h.digitMin,h.maskWidth,h.colon,h.upperEnd,h.version,h.inverse,count,te,h.negLength⟩
end E5R.Thermostat.HeadFieldsConstants
