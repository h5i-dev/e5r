import Projects.thermostat.HeadClScratch
import Projects.thermostat.HeadTeRuleMath
import Projects.thermostat.HeadFieldsMeta
import Projects.thermostat.HeadSavedTail
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadHeaderScratch
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def memory (ram : Word → BitVec 8) (sp : Word) (ve le : Nat) :=
  ramWrite ram (sp+0#32) (BitVec.ofNat 32 le-BitVec.ofNat 32 ve) .w

theorem region (ram : Word → BitVec 8) (sp : Word) (ve le off len : Nat)
    (bound : off+len≤4294967296) (outside : 4≤off) :
    ViewFrame.Region ram (memory ram sp ve le) (sp+BitVec.ofNat 32 off) len := by
  intro i
  unfold memory
  exact StoreBytes.frame _ _ _ _ .w (fun j => FrameOffsets.ne sp off 0 i.val j.val
    (by have hi := i.isLt;omega) (by have hj : j.val<4 := j.isLt;omega)
    (by have hi := i.isLt;have hj : j.val<4 := j.isLt;omega))

theorem word_frame (ram : Word → BitVec 8) (sp : Word) (ve le off : Nat)
    (bound : off+4≤4294967296) (outside : 4≤off) :
    ramRead (memory ram sp ve le) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
  simpa only [BitVec.add_zero] using ViewFrame.word (region ram sp ve le off 4 bound outside) 0 (by decide)

theorem scratch_word (ram : Word → BitVec 8) (sp : Word) (ve le : Nat) :
    ramRead (memory ram sp ve le) (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve := ramRead_ramWrite_w _ _ _

theorem fields {ram : Word → BitVec 8} {sp : Word} {f : Fields} (ve le : Nat) (h : HeadFieldsView.At ram sp f) :
    HeadFieldsView.At (memory ram sp ve le) sp f :=
  HeadFieldsView.preserve h (region ram sp ve le 56 271 (by decide) (by decide))

theorem rx (ram : Word → BitVec 8) (sp : Word) (ve le : Nat) (i : Nat) (hi : i<2048) :
    bytes (memory ram sp ve le) (sp+516#32) i=bytes ram (sp+516#32) i :=
  congrArg BitVec.toNat (region ram sp ve le 516 2048 (by decide) (by decide) ⟨i,hi⟩)

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (ns ve le : Nat)
    (hp : c.pc=0x80003192#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (h25 : c.get 25=BitVec.ofNat 32 ve) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (name : ns≤le) (value : ve≤le) (bound : le≤2048) (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 3 ⟨c,ram⟩ ⟨d,memory ram sp ve le⟩ ∧ d.pc=0x8000319a#32 ∧
      d.get 10=BitVec.ofNat 32 le-BitVec.ofNat 32 ve ∧ (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  have arithmetic : (BitVec.ofNat 32 ns-BitVec.ofNat 32 ve)+BitVec.ofNat 32 (le-ns)=BitVec.ofNat 32 le-BitVec.ofNat 32 ve := by
    rw [HeadTeRuleMath.span ns ve le name value bound,BitVec.ofNat_sub_ofNat_of_le le ve (by omega) value]
  obtain ⟨d,trace,pc,v10,frame,csr⟩ := HeadClScratch.contract B c ram sp _ _ _ h2 h24 h25 h21 stack aligned hp
  have after : HeadClScratch.memory ram sp (BitVec.ofNat 32 ns) (BitVec.ofNat 32 ve) (BitVec.ofNat 32 (le-ns))=memory ram sp ve le := by
    unfold HeadClScratch.memory memory
    rw [arithmetic]
  rw [after] at trace
  exact ⟨d,trace,pc,v10.trans arithmetic,frame,csr⟩
end E5R.Thermostat.HeadHeaderScratch
