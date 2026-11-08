import Projects.thermostat.HeadHostBuffer
import Projects.thermostat.HeadHostCompare
import Projects.thermostat.HeadHostFlagMemory
namespace E5R.Thermostat.HeadHost
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def updated (g : Nat → Nat) (start : Nat) (f : Fields) : Fields :=
  if classify g start (start+4)=1 ∧ f.host=false then {f with host := true} else f

/-- Actual width-four name classification and Host duplicate check/store.
    This ends before the common header-array commit; no appended field is assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat) (f : Fields)
    (hp : c.pc=0x80003106#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (fields : HeadFieldsView.At ram sp f) (width : start+4≤length) (hlen : length≤2048) (mem : Memory.Block B buf length)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d after, 9≤n ∧ n≤43 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if classify g start (start+4)=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32) ∧
      HeadFieldsView.At after sp (updated g start f) ∧ (after=ram ∨ after=HeadHostFlagStore.memory ram sp) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have stack : Memory.Block B sp 56 := by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 56) (by decide) (by decide)
  have hostStack : Memory.Block B sp 327 := by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 327) (by decide) (by decide)
  obtain ⟨a,setup,pc,pointer,frame,csr⟩ := HeadHostBuffer.contract B c ram sp buf (BitVec.ofNat 32 start) h2 h24 hbuf stack ha hp
  obtain ⟨n,b,nlo,nhi,compare,pc2,frame2,csr2⟩ := HeadHostCompare.contract B a ram sp buf start length pc
    ((frame 2 (by decide)).trans h2) ((frame 24 (by decide)).trans h24) pointer hraw width hlen mem stack ha
  have source (r : Reg) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : b.get r=c.get r :=
    (frame2 r h10 h11 h12 h13 h14).trans (frame r h10)
  change b.pc=(if HeadHostSpec.Prefix g start then 0x80003182#32 else 0x800033b6#32) at pc2
  by_cases prefixOK : HeadHostSpec.Prefix g start
  · have atHost : b.pc=0x80003182#32 := by simpa only [prefixOK,ite_true] using pc2
    obtain ⟨m,d,mlo,mhi,flag,pc3,frame3,csr3⟩ := HeadHostFlag.contract B b ram sp f.host atHost
      ((source 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) fields.host hostStack
    refine ⟨2+n+m,d,HeadHostFlag.memory ram sp f.host,by omega,by omega,(setup.trans compare).trans flag,?_,?_,?_,
      fun r h10 h11 h12 h13 h14 => (frame3 r h10).trans (source r h10 h11 h12 h13 h14),csr3.trans (csr2.trans csr)⟩
    · change d.pc=(if classify g start (start+4)=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32)
      simpa [HeadHostSpec.classify_width4,prefixOK] using pc3
    · change HeadFieldsView.At (HeadHostFlag.memory ram sp f.host) sp (updated g start f)
      cases host : f.host with
      | true => simpa [HeadHostFlag.memory,updated,HeadHostSpec.classify_width4,prefixOK,host] using fields
      | false => simpa [HeadHostFlag.memory,updated,HeadHostSpec.classify_width4,prefixOK,host] using HeadHostFlagMemory.fields fields
    · unfold HeadHostFlag.memory
      split
      · exact Or.inl rfl
      · exact Or.inr rfl
  · refine ⟨2+n,b,ram,by omega,by omega,setup.trans compare,?_,?_,Or.inl rfl,source,csr2.trans csr⟩
    · change b.pc=(if classify g start (start+4)=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32)
      simpa [HeadHostSpec.classify_width4,prefixOK] using pc2
    · change HeadFieldsView.At ram sp (updated g start f)
      simpa [updated,HeadHostSpec.classify_width4,prefixOK] using fields
end E5R.Thermostat.HeadHost
