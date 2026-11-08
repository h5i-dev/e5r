import Projects.thermostat.MainBodyHeadLoad
import Projects.thermostat.MainBodyChunkBranch
import Projects.thermostat.MainBodyLengthBranch
import Projects.thermostat.HeadCompletedView
namespace E5R.Thermostat.MainBodyHeadDispatch
open E5R E5R.Thermostat HttpRequestSpec

def At (c : Core) : Framing → Prop
  | .empty => c.pc=0x80000fc0#32
  | .length _ => c.pc=0x80000c26#32
  | .chunked => c.pc=0x80000e54#32

/-- Actual loads from the copied Head, persisted consumed-head length, and
    both framing tests. The constants two and one are execution premises;
    reset-to-header preservation is proved separately. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (fp : Word) (head : Head)
    (hp : c.pc=0x80000c14#32) (h8 : c.get 8=fp) (h18 : c.get 18=2#32) (h22 : c.get 22=1#32)
    (view : HeadCompletedView.At ram (fp+116#32) head) (object : Memory.Block B fp 448) (aligned : fp.toNat%4=0) :
    ∃ n d, 4≤n ∧ n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩
      ⟨d,MainBodyHeadLoad.memory ram fp (BitVec.ofNat 32 head.len) (HeadCompletedView.framingTag head.framing)⟩ ∧
      At d head.framing ∧ d.get 20=BitVec.ofNat 32 head.len ∧ d.get 9=HeadCompletedView.framingTag head.framing ∧
      (∀ r : Reg, r≠20 → r≠9 → d.get r=c.get r) ∧ d.sameCsr c := by
  have len : ramRead ram (fp+408#32) .w=BitVec.ofNat 32 head.len := by
    simpa only [BitVec.add_assoc,show 116#32+292#32=408#32 by decide +kernel] using view.length
  obtain ⟨a,ta,apc,a20,a9,ar,ac⟩ := MainBodyHeadLoad.contract B c ram fp _ _ h8 len view.tag object aligned hp
  have a18 : a.get 18=2#32 := (ar 18 (by decide) (by decide)).trans h18
  have a22 : a.get 22=1#32 := (ar 22 (by decide) (by decide)).trans h22
  cases kind : head.framing with
  | chunked =>
    have tag : a.get 9=2#32 := by simpa only [kind,HeadCompletedView.framingTag] using a9
    obtain ⟨d,td,dpc,dr,dc⟩ := MainBodyChunkBranch.contract B a _ 2#32 2#32 true apc tag a18 (by decide +kernel)
    refine ⟨4,d,by decide,by decide,ta.trans td,?_,(dr 20).trans a20,(dr 9).trans tag,?_,dc.trans ac⟩
    · simpa only [ite_true,At] using dpc
    · intro r h20 h9;exact (dr r).trans (ar r h20 h9)
  | empty =>
    have tag : a.get 9=0#32 := by simpa only [kind,HeadCompletedView.framingTag] using a9
    obtain ⟨b,tb,bpc,br,bc⟩ := MainBodyChunkBranch.contract B a _ 0#32 2#32 false apc tag a18 (by decide +kernel)
    have pc : b.pc=0x80000c22#32 := by simpa only [Bool.false_eq_true,ite_false] using bpc
    obtain ⟨d,td,dpc,dr,dc⟩ := MainBodyLengthBranch.contract B b _ 0#32 1#32 true pc ((br 9).trans tag) ((br 22).trans a22) (by decide +kernel)
    refine ⟨5,d,by decide,by decide,(ta.trans tb).trans td,?_,(dr 20).trans ((br 20).trans a20),(dr 9).trans ((br 9).trans tag),?_,(dc.trans bc).trans ac⟩
    · simpa only [ite_true,At] using dpc
    · intro r h20 h9;exact (dr r).trans ((br r).trans (ar r h20 h9))
  | length count =>
    have tag : a.get 9=1#32 := by simpa only [kind,HeadCompletedView.framingTag] using a9
    obtain ⟨b,tb,bpc,br,bc⟩ := MainBodyChunkBranch.contract B a _ 1#32 2#32 false apc tag a18 (by decide +kernel)
    have pc : b.pc=0x80000c22#32 := by simpa only [Bool.false_eq_true,ite_false] using bpc
    obtain ⟨d,td,dpc,dr,dc⟩ := MainBodyLengthBranch.contract B b _ 1#32 1#32 false pc ((br 9).trans tag) ((br 22).trans a22) (by decide +kernel)
    refine ⟨5,d,by decide,by decide,(ta.trans tb).trans td,?_,(dr 20).trans ((br 20).trans a20),(dr 9).trans ((br 9).trans tag),?_,(dc.trans bc).trans ac⟩
    · simpa only [Bool.false_eq_true,ite_false,At] using dpc
    · intro r h20 h9;exact (dr r).trans ((br r).trans (ar r h20 h9))
end E5R.Thermostat.MainBodyHeadDispatch
