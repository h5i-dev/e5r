import Projects.thermostat.MainRequestPaddingLoads
import Projects.thermostat.MainRequestMinorRawStores
import Projects.thermostat.MainRequestStoreFrames
import Projects.thermostat.MainRequestZero
import Projects.thermostat.MainRequestSaved
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainRequestTailCore
open E5R E5R.Thermostat

def padding (ram : Word → BitVec 8) (sp : Word) := MainRequestPaddingStores.memory ram sp
  (extend .b false (ramRead ram (sp+4240#32) .b)) (extend .b false (ramRead ram (sp+4241#32) .b))
  (extend .b false (ramRead ram (sp+4242#32) .b)) (extend .b false (ramRead ram (sp+4243#32) .b))
  (extend .b false (ramRead ram (sp+4244#32) .b)) (extend .b false (ramRead ram (sp+4245#32) .b))
  (extend .b false (ramRead ram (sp+4246#32) .b))

def minorRaw (ram : Word → BitVec 8) (sp minor rx used : Word) :=
  MainRequestMinorRawStores.memory (padding ram sp) sp minor rx used

def memory (ram : Word → BitVec 8) (sp minor rx used : Word) := MainRequestZero.memory (minorRaw ram sp minor rx used) sp

/-- Actual arbitrary padding relocation, minor/raw field stores and complete
    parameter-array initialization, through the real memset return. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp minor rx used : Word)
    (hp : c.pc=0x800011e2#32) (h2 : c.get 2=sp) (h8 : c.get 8=sp+3204#32)
    (h21 : c.get 21=rx) (h24 : c.get 24=used) (hminor : ramRead ram (sp+40#32) .w=minor)
    (stack : Memory.Block B sp 5232) (aligned : sp.toNat%4=0) :
    ∃ d, Quiet.Steps B img 72 ⟨c,ram⟩ ⟨d,memory ram sp minor rx used⟩ ∧ d.pc=0x80001246#32 ∧
      d.get 9=minor ∧ MainRequestSaved.Frame c d ∧ d.sameCsr c := by
  obtain ⟨a,loads,pa,a10,a11,a12,a13,a14,a15,a16,ar,ac⟩ := MainRequestPaddingLoads.contract B c ram sp _ _ _ _ _ _ _ h8 stack aligned rfl rfl rfl rfl rfl rfl rfl hp
  have fa := MainRequestSaved.temps7 ar
  have a8 : a.get 8=sp+3204#32 := (fa 8 (by decide)).trans h8
  have a2 : a.get 2=sp := (fa 2 (by decide)).trans h2
  obtain ⟨b,stores,pb,b17,br,bc⟩ := MainRequestPaddingStores.contract B a ram sp _ _ _ _ _ _ _ a8 stack aligned a2 a10 a11 a12 a13 a14 a15 a16 pa
  have fb := MainRequestSaved.temp17 br
  have cab := MainRequestSaved.trans fa fb
  let r1 := padding ram sp
  have minorWord : ramRead r1 (sp+40#32) .w=minor := by
    have region := MainRequestStoreFrames.padding ram sp
      (extend .b false (ramRead ram (sp+4240#32) .b)) (extend .b false (ramRead ram (sp+4241#32) .b))
      (extend .b false (ramRead ram (sp+4242#32) .b)) (extend .b false (ramRead ram (sp+4243#32) .b))
      (extend .b false (ramRead ram (sp+4244#32) .b)) (extend .b false (ramRead ram (sp+4245#32) .b))
      (extend .b false (ramRead ram (sp+4246#32) .b)) 40 4 (by decide) (Or.inl (by decide))
    have word := ViewFrame.word region 0 (by decide)
    simp only [BitVec.add_zero] at word
    exact word.trans hminor
  obtain ⟨e,minorStores,pe,e9,er,ec⟩ := MainRequestMinorRawStores.contract B b r1 sp minor rx used
    ((cab 8 (by decide)).trans h8) stack aligned ((cab 2 (by decide)).trans h2)
    ((cab 21 (by decide)).trans h21) ((cab 24 (by decide)).trans h24) minorWord pb
  have fe := MainRequestSaved.minor er
  have cae := MainRequestSaved.trans cab fe
  obtain ⟨d,clear,pd,dr,dc⟩ := MainRequestZero.contract B e _ sp pe ((cae 2 (by decide)).trans h2) stack aligned
  have fd := MainRequestSaved.zero dr
  exact ⟨d,((loads.trans stores).trans minorStores).trans clear,pd,
    (dr 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans e9,
    MainRequestSaved.trans cae fd,dc.trans (ec.trans (bc.trans ac))⟩
end E5R.Thermostat.MainRequestTailCore
