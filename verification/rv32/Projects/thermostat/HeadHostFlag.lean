import Projects.thermostat.HeadHostFlagLoad
import Projects.thermostat.HeadHostFlagBranch
import Projects.thermostat.HeadHostFlagStore
import Projects.thermostat.HeadFieldsView
namespace E5R.Thermostat.HeadHostFlag
open E5R E5R.Thermostat

def memory (ram : Word → BitVec 8) (sp : Word) (host : Bool) :=
  if host then ram else HeadHostFlagStore.memory ram sp

theorem test : ∀ host : Bool,
    taken .ne (BitVec.ofNat 32 (HeadFieldsView.flag host).toNat) (0 : Word)=host := by decide +kernel

/-- Actual Host duplicate refusal or one-byte host flag store. The previous
    flag is loaded from RAM; no permission to accept a duplicate is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (host : Bool)
    (hp : c.pc=0x80003182#32) (h2 : c.get 2=sp) (hhost : ram (sp+324#32)=HeadFieldsView.flag host)
    (hm : Memory.Block B sp 327) :
    ∃ n d, 2≤n ∧ n≤5 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,memory ram sp host⟩ ∧
      d.pc=(if host then 0x8000342c#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → d.get r=c.get r) ∧ d.sameCsr c := by
  have access : B.inRam (sp+324#32) 1=true := Memory.block_access hm (off := 324) (by decide) (by decide)
  obtain ⟨a,load,pc,value,frame,csr⟩ := HeadHostFlagLoad.contract B c ram sp (HeadFieldsView.flag host) h2 access hhost hp
  obtain ⟨b,branch,pc2,frame2,csr2⟩ := HeadHostFlagBranch.contract B a ram (BitVec.ofNat 32 (HeadFieldsView.flag host).toNat) host pc value (test host)
  have source (r : Reg) (h10 : r≠10) : b.get r=c.get r := (frame2 r).trans (frame r h10)
  cases host with
  | true => exact ⟨2,b,by decide,by decide,load.trans branch,pc2,source,csr2.trans csr⟩
  | false =>
    obtain ⟨d,store,pc3,one,frame3,csr3⟩ := HeadHostFlagStore.contract B b ram sp ((source 2 (by decide)).trans h2) access pc2
    exact ⟨5,d,by decide,by decide,(load.trans branch).trans store,pc3,
      fun r h10 => (frame3 r h10).trans (source r h10),csr3.trans (csr2.trans csr)⟩
end E5R.Thermostat.HeadHostFlag
