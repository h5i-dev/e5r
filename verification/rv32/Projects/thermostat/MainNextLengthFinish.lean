import Projects.thermostat.MainNextLengthTailMemory
import Projects.thermostat.MainNextArrayFrame
namespace E5R.Thermostat.MainNextLengthFinish
open E5R E5R.Thermostat HttpRequestSpec

def pad (ram : Word → BitVec 8) (sp : Word) (k : Nat) := extend .b false (ramRead ram (sp+BitVec.ofNat 32 (3617+k)) .b)

def memory (ram : Word → BitVec 8) (sp : Word) (head : Head) (used : Word) :=
  MainNextLengthTail.memory ram sp (BitVec.ofNat 32 head.len) used (BitVec.ofNat 32 head.minor)
    (pad ram sp 0) (pad ram sp 1) (pad ram sp 2) (pad ram sp 3) (pad ram sp 4) (pad ram sp 5) (pad ram sp 6)

def Frame (before after : Word → BitVec 8) (sp : Word) : Prop := ∀ off size : Nat,
  off+size≤5232 → (off+size≤40 ∨ 44≤off) → (off+size≤4896 ∨ 4903≤off) → ViewFrame.Region before after (sp+BitVec.ofNat 32 off) size

/-- Real padding reads and packing preserve all semantic header fields.
    Every padding value is the actual RAM value, with no zero assumption. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (head : Head) (used : Word)
    (hp : c.pc=0x80000cf6#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32) (h25 : c.get 25=used)
    (view : HeadCompletedView.At ram (sp+3320#32) head) (version : head.minor≤1)
    (consumed : ramRead ram (sp+3648#32) .w=BitVec.ofNat 32 head.len)
    (array : MainNextArrayView.At ram (sp+4904#32) head)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 25 ⟨c,ram⟩ ⟨d,memory ram sp head used⟩ ∧ d.pc=0x80000a9a#32 ∧
      d.get 20=BitVec.ofNat 32 head.len ∧ d.get 24=used ∧
      (∀ r : Reg, r∈[2,8,9,18,19,21,22,23,25,26,27] → d.get r=c.get r) ∧
      HeadCompletedView.At (memory ram sp head used) (sp+3320#32) head ∧
      MainNextArrayView.At (memory ram sp head used) (sp+4904#32) head ∧ Frame ram (memory ram sp head used) sp ∧ d.sameCsr c := by
  have minorByte : ram (sp+3616#32)=BitVec.ofNat 8 head.minor := by
    simpa only [BitVec.add_assoc,show 3320#32+296#32=3616#32 by decide +kernel] using view.version
  have minor : extend .b false (ramRead ram (sp+3616#32) .b)=BitVec.ofNat 32 head.minor := by
    rw [Memory.load_byte,minorByte,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show head.minor<2^8 by omega)]
  obtain ⟨d,steps,pc,_,_,_,_,_,_,_,len,usedReg,dr,dc⟩ := MainNextLengthTail.contract B c ram sp (BitVec.ofNat 32 head.len) used (BitVec.ofNat 32 head.minor)
    (pad ram sp 0) (pad ram sp 1) (pad ram sp 2) (pad ram sp 3) (pad ram sp 4) (pad ram sp 5) (pad ram sp 6)
    h2 h8 h25 stack aligned minor consumed rfl rfl rfl rfl rfl rfl rfl hp
  have frame : Frame ram (memory ram sp head used) sp := MainNextLengthTailMemory.region ram sp _ _ _ _ _ _ _ _ _ _
  have regs : ∀ r : Reg, r∈[2,8,9,18,19,21,22,23,25,26,27] → d.get r=c.get r := by
    intro r safe
    have ne : ∀ r : Reg, r∈[2,8,9,18,19,21,22,23,25,26,27] → r≠16 ∧ r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 ∧ r≠15 ∧ r≠20 ∧ r≠24 := by decide +kernel
    obtain ⟨a,b,c,e,f,g,h,i,j⟩ := ne r safe
    exact dr r a b c e f g h i j
  have finalHead := MainCopyView.head (frame 3320 304 (by decide) (Or.inr (by decide)) (Or.inl (by decide))) head view
  have finalArray := MainNextArrayFrame.preserve array (frame 4904 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  exact ⟨d,steps,pc,len,usedReg,regs,finalHead,finalArray,frame,dc⟩
end E5R.Thermostat.MainNextLengthFinish
