import Projects.thermostat.HeadRegionFrame
import Projects.thermostat.MainNextLengthLoads
import Projects.thermostat.MainNextLengthStoreMemory
import Projects.thermostat.MainNextLengthCall
import Projects.thermostat.MainNextArrayView
namespace E5R.Thermostat.MainNextLengthPrefix
open E5R E5R.Thermostat HttpRequestSpec

def stored (ram : Word → BitVec 8) (sp : Word) (head : Head) := MainNextLengthStores.memory ram sp
  (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2)

def memory (ram : Word → BitVec 8) (sp : Word) (head : Head) := MainNextCopy264.memory (stored ram sp head) sp 3352

def Frame (before after : Word → BitVec 8) (sp : Word) : Prop :=
  ∀ off size : Nat, 40≤off → off+size≤4904 → ViewFrame.Region before after (sp+BitVec.ofNat 32 off) size

/-- Actual fixed-length Next construction through the memcpy return: mixed
    word/half loads, span/payload stores, real call and264 RAM bytes copied. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (head : Head) (amount : Nat)
    (hp : c.pc=0x80000c98#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (view : HeadCompletedView.At ram (sp+3320#32) head) (kind : head.framing=.length amount) (bound : amount≤1024)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 382 ⟨c,ram⟩ ⟨d,memory ram sp head⟩ ∧ d.pc=0x80000cf6#32 ∧ d.get 2=sp ∧ d.get 8=sp+3204#32 ∧
      d.get 9=1#32 ∧ d.get 18=0#32 ∧ d.get 27=BitVec.ofNat 32 amount ∧
      (∀ rr : Reg, rr∈[19,20,21,22,23,24,25,26] → d.get rr=c.get rr) ∧
      MainNextArrayView.At (memory ram sp head) (sp+4904#32) head ∧
      HeadCompletedView.At (memory ram sp head) (sp+3320#32) head ∧ Frame ram (memory ram sp head) sp ∧ d.sameCsr c := by
  have words := MainNextLengthWords.contract ram sp head amount view kind bound
  obtain ⟨a,ta,apc,a12,a10,a11,a9,a18,a27,ar,ac⟩ := MainNextLengthLoads.contract B c ram sp amount h2 h8 words stack aligned hp
  have a2 := (ar 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2
  have a8 := (ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h8
  have offset (a b : Nat) : (sp+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=sp+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  obtain ⟨b,tb,bpc,b13,b11,b10,br,bc⟩ := MainNextLengthStores.contract B a ram sp _ _ _ _ a2 a8 a10 a11 a12
    (by simpa only [offset] using view.methodStart) (by simpa only [offset] using view.methodEnd)
    (by simpa only [offset] using view.targetStart) (by simpa only [offset] using view.targetEnd) stack aligned apc
  have b2 := (br 2 (by decide) (by decide) (by decide)).trans a2
  obtain ⟨z,tz,zpc,z10,z12,z11,z1,zr,zc⟩ := MainNextLengthCall.contract B b (stored ram sp head) sp b2 bpc
  have z2 := (zr 2 (by decide) (by decide) (by decide) (by decide)).trans b2
  obtain ⟨d,td,ret,_⟩ := MainNextCopy264.contract B z (stored ram sp head) sp 3352 (Or.inl rfl) zpc z2 z10 z11 z12 stack aligned
  have pc : d.pc=0x80000cf6#32 := by rw [ret.pc,z1];decide +kernel
  have regs (rr : Reg) (safe : rr≠12 ∧ rr≠10 ∧ rr≠11 ∧ rr≠9 ∧ rr≠18 ∧ rr≠27 ∧ rr≠13 ∧ rr≠1)
      (saved : d.get rr=z.get rr) : d.get rr=c.get rr := by
    obtain ⟨h12,h10,h11,h9,h18,h27,h13,h1⟩ := safe
    exact saved.trans ((zr rr h10 h12 h11 h1).trans ((br rr h13 h11 h10).trans (ar rr h12 h10 h11 h9 h18 h27)))
  have kept : ∀ rr : Reg, rr∈[19,20,21,22,23,24,25,26] → d.get rr=c.get rr := by
    intro rr member
    have casesReg : rr=19 ∨ rr=20 ∨ rr=21 ∨ rr=22 ∨ rr=23 ∨ rr=24 ∨ rr=25 ∨ rr=26 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
    rcases casesReg with h|h|h|h|h|h|h|h <;> subst rr
    · exact regs 19 (by decide) ret.x19
    · exact regs 20 (by decide) ret.x20
    · exact regs 21 (by decide) ret.x21
    · exact regs 22 (by decide) ret.x22
    · exact regs 23 (by decide) ret.x23
    · exact regs 24 (by decide) ret.x24
    · exact regs 25 (by decide) ret.x25
    · exact regs 26 (by decide) ret.x26
  have frame : Frame ram (memory ram sp head) sp := by
    intro off size lo hi
    apply HeadRegionFrame.trans (MainNextLengthStoreMemory.region ram sp _ _ _ _ off size lo (by omega))
    exact MainNextCopy264.frame (stored ram sp head) sp 3352 off size (by omega) (Or.inl hi)
  have source : HeadCompletedView.At (stored ram sp head) (sp+3320#32) head := MainNextLengthStoreMemory.head ram sp _ _ _ _ head view
  have finalHead := MainCopyView.head (frame 3320 304 (by decide) (by decide)) head view
  refine ⟨d,((ta.trans tb).trans tz).trans td,pc,ret.sp.trans z2,?_,?_,?_,?_,kept,MainNextArrayView.fixed (stored ram sp head) sp head stack source,finalHead,frame,((ret.csr.trans zc).trans bc).trans ac⟩
  · exact ret.x8.trans ((zr 8 (by decide) (by decide) (by decide) (by decide)).trans ((br 8 (by decide) (by decide) (by decide)).trans a8))
  · exact ret.x9.trans ((zr 9 (by decide) (by decide) (by decide) (by decide)).trans ((br 9 (by decide) (by decide) (by decide)).trans a9))
  · exact ret.x18.trans ((zr 18 (by decide) (by decide) (by decide) (by decide)).trans ((br 18 (by decide) (by decide) (by decide)).trans a18))
  · exact ret.x27.trans ((zr 27 (by decide) (by decide) (by decide) (by decide)).trans ((br 27 (by decide) (by decide) (by decide)).trans a27))
end E5R.Thermostat.MainNextLengthPrefix
