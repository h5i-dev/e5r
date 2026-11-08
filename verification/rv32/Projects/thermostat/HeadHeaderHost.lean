import Projects.thermostat.HeadActionSpec
import Projects.thermostat.HeadHost
import Projects.thermostat.HeadHeaderActionView
import Projects.thermostat.HeadRegisterFrame
namespace E5R.Thermostat.HeadHeaderHost
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem action (g : Nat → Nat) (f : Fields) (ns vs ve le minor : Nat) :
    HeadActionSpec.action g f ns (ns+4) vs ve le minor 1024=
      (if classify g ns (ns+4)=1 ∧ f.host then .bad 400 else .ok (HeadHost.updated g ns f)) := by
  have kind := HeadHostSpec.classify_width4 g ns
  unfold HeadActionSpec.action HeadHost.updated
  rw [kind]
  by_cases prefixOK : HeadHostSpec.Prefix g ns <;> cases f.host <;> simp only [prefixOK,ite_true,ite_false,Bool.false_eq_true,not_false_eq_true,false_and,and_false,and_true,true_and,show ¬(0=1) by decide,show ¬(0=2) by decide,show ¬(0=3) by decide]

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (ns vs ve le length minor : Nat) (f : Fields)
    (hp : c.pc=0x80003106#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (fields : HeadFieldsView.At ram sp f) (width : ns+4≤length) (bound : length≤2048)
    (mem : Memory.Block B buf length) (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) :
    let result := HeadActionSpec.action (bytes ram buf) f ns (ns+4) vs ve le minor 1024
    ∃ n d after, 9≤n ∧ n≤43 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderActionView.At d result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      (after=ram ∨ after=HeadHostFlagStore.memory ram sp) ∧ HeadRegisterFrame.At c d [10,11,12,13,14] ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨n,d,after,lo,hi,trace,pc,view,effect,frame,csr⟩ := HeadHost.contract B c ram sp buf ns length f hp h2 h24 hraw hbuf fields width bound mem stack aligned
  change d.pc=(if classify g ns (ns+4)=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32) at pc
  change HeadFieldsView.At after sp (HeadHost.updated g ns f) at view
  have actualFrame : HeadRegisterFrame.At c d [10,11,12,13,14] := by
    intro r safe
    have facts : ∀ r : Reg, r∉[10,11,12,13,14] → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠13 ∧ r≠14 := by decide +kernel
    obtain ⟨a,b,c,d,e⟩ := facts r safe
    exact frame r a b c d e
  have spec := action g f ns vs ve le minor
  change ∃ n d after, _
  rw [show HeadActionSpec.action (bytes ram buf) f ns (ns+4) vs ve le minor 1024=
    (if classify g ns (ns+4)=1 ∧ f.host then .bad 400 else .ok (HeadHost.updated g ns f)) from spec]
  by_cases duplicate : classify g ns (ns+4)=1 ∧ f.host
  · rw [ite_eq_left duplicate]
    have unchanged : HeadHost.updated g ns f=f := by
      simp [HeadHost.updated,duplicate.1,duplicate.2]
    have dpc : d.pc=0x8000342c#32 := by simpa [duplicate] using pc
    rw [unchanged] at view
    exact ⟨n,d,after,lo,hi,trace,⟨dpc,(actualFrame 1 (by decide)).trans h1⟩,view,effect,actualFrame,csr⟩
  · rw [ite_eq_right duplicate]
    have dpc : d.pc=0x800033b6#32 := by simpa [duplicate] using pc
    exact ⟨n,d,after,lo,hi,trace,dpc,view,effect,actualFrame,csr⟩
end E5R.Thermostat.HeadHeaderHost
