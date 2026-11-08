import Projects.thermostat.HeadVersionMemory
namespace E5R.Thermostat.HeadVersionStorage
open E5R E5R.Thermostat

/-- Actual parser scratch storage, capturing the pre-store register values. -/
def memory (ram : Word → BitVec 8) (sp : Word) (c : Core) :=
  HeadVersionSave.memory ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (hp : c.pc=0x80002e2c#32) (h2 : c.get 2=sp) (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,memory ram sp c⟩ ∧ d.pc=0x80002e3e#32 ∧
      (∀ r : Reg, d.get r=c.get r) ∧ d.sameCsr c := by
  exact HeadVersionSave.contract B c ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17) h2 rfl rfl rfl rfl rfl rfl rfl rfl rfl hm ha hp

theorem region (ram : Word → BitVec 8) (sp : Word) (c : Core) (off len : Nat)
    (hb : off+len≤4294967296) (hs : off+len≤20 ∨ 56≤off) :
    ViewFrame.Region ram (memory ram sp c) (sp+BitVec.ofNat 32 off) len :=
  HeadVersionMemory.region ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17) off len hb hs

theorem saved (ram : Word → BitVec 8) (sp : Word) (c : Core) (values : Reg → Word)
    (h : HeadSaved.At ram sp values) : HeadSaved.At (memory ram sp c) sp values :=
  HeadVersionMemory.saved ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17) values h

theorem buf_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+44#32) .w=c.get 11 :=
  HeadVersionMemory.buf_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem length_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+48#32) .w=c.get 12 :=
  HeadVersionMemory.length_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem dst_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+52#32) .w=c.get 10 :=
  HeadVersionMemory.dst_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem congr_core (ram : Word → BitVec 8) (sp : Word) (c d : Core)
    (frame : ∀ r : Reg, r≠28 → r≠31 → d.get r=c.get r) : memory ram sp d=memory ram sp c := by
  unfold memory
  rw [frame 18 (by decide) (by decide),frame 29 (by decide) (by decide),frame 5 (by decide) (by decide),frame 14 (by decide) (by decide),frame 16 (by decide) (by decide),frame 11 (by decide) (by decide),frame 10 (by decide) (by decide),frame 12 (by decide) (by decide),frame 17 (by decide) (by decide)]

theorem app (ram : Word → BitVec 8) (c : Core) (state : Spec.Snapshot) (h : AppState.At ram state) :
    AppState.At (memory ram 0x80ffea10#32 c) state :=
  HeadVersionMemory.app ram (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17) state h

theorem targetEnd_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+28#32) .w=c.get 18 :=
  HeadVersionMemory.targetEnd_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem targetStart_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+24#32) .w=c.get 29 :=
  HeadVersionMemory.targetStart_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem mask_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+32#32) .w=c.get 5 :=
  HeadVersionMemory.mask_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem n_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+40#32) .w=c.get 14 :=
  HeadVersionMemory.n_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem maxHead_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+36#32) .w=c.get 16 :=
  HeadVersionMemory.maxHead_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)

theorem methodEnd_word (ram : Word → BitVec 8) (sp : Word) (c : Core) :
    ramRead (memory ram sp c) (sp+20#32) .w=c.get 17 :=
  HeadVersionMemory.methodEnd_word ram sp (c.get 18) (c.get 29) (c.get 5) (c.get 14) (c.get 16) (c.get 11) (c.get 10) (c.get 12) (c.get 17)
end E5R.Thermostat.HeadVersionStorage
