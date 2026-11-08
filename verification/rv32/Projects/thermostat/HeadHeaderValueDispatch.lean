import Projects.thermostat.HeadNameClassify
import Projects.thermostat.HeadHeaderActionView
namespace E5R.Thermostat.HeadHeaderValueDispatch
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual value-parser entries selected by real name dispatch refine the
    independent addHeader action before the common array append. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word)
    (f : Fields) (ns ne vs ve le length minor : Nat)
    (hp : c.pc=HeadNameClassify.endpoint (classify (bytes ram buf) ns ne))
    (kinds : classify (bytes ram buf) ns ne=0 ∨ classify (bytes ram buf) ns ne=2 ∨ classify (bytes ram buf) ns ne=3)
    (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (h15 : c.get 15=BitVec.ofNat 32 vs) (h26 : c.get 26=BitVec.ofNat 32 le)
    (h11 : classify (bytes ram buf) ns ne=2 → c.get 11=BitVec.ofNat 32 le)
    (h16 : c.get 16=10#32) (h18 : c.get 18=BitVec.ofNat 32 (1-minor))
    (h24 : c.get 24=BitVec.ofNat 32 ns) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (fields : HeadFieldsView.At ram sp f)
    (ordered : ns≤vs ∧ vs≤ve ∧ ve≤le ∧ le≤length) (bound : length≤2048) (version : minor≤1)
    (memory : Memory.Block B buf length) (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) :
    let result := HeadActionSpec.action (bytes ram buf) f ns ne vs ve le minor 1024
    ∃ n d after, n≤101+30*(ve-vs) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderActionView.At d result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      HeadHeaderActionView.Effect ram after sp ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  rcases kinds with ordinary | cl | te
  · have pc : c.pc=0x800033b6#32 := by simpa only [HeadNameClassify.endpoint,ordinary,show ¬(0=2) by decide,show ¬(0=3) by decide,ite_false] using hp
    have action : HeadActionSpec.action g f ns ne vs ve le minor 1024=.ok f := HeadClassSpec.ordinary_action g f ns ne vs ve le minor ordinary
    change ∃ n d after, _
    rw [show HeadActionSpec.action (bytes ram buf) f ns ne vs ve le minor 1024=.ok f from action]
    exact ⟨0,c,ram,by omega,.refl _,pc,fields,Or.inl rfl,fun _ _ _ _ _ _ _ _ _ _ => rfl,by rfl⟩
  · have pc : c.pc=0x800031dc#32 := by simpa only [HeadNameClassify.endpoint,cl,ite_true] using hp
    obtain ⟨n,d,after,lo,hi,trace,post,view,frame,csr⟩ := HeadClValue.contract B c ram sp buf vs ve le length f pc h1 h2 h23 h15 h26 (h11 cl) h16 scratch hbuf hraw hlimit fields
      ⟨ordered.2.1,ordered.2.2.1,ordered.2.2.2⟩ bound memory stack aligned
    obtain ⟨actionAt,view',effect⟩ := HeadHeaderActionView.from_cl post view
    have action := HeadClassSpec.cl_action g f ns ne vs ve le minor cl
    change ∃ n d after, _
    rw [show HeadActionSpec.action (bytes ram buf) f ns ne vs ve le minor 1024=HeadClassSpec.ofCl f (HeadClValue.outcome (bytes ram buf) f vs ve le) from action]
    exact ⟨n,d,after,by omega,trace,actionAt,view',effect,frame,csr⟩
  · have pc : c.pc=0x800032ae#32 := by simpa only [HeadNameClassify.endpoint,te,show ¬(3=2) by decide,ite_false,ite_true] using hp
    obtain ⟨n,d,after,lo,hi,trace,post,view,frame,csr⟩ := HeadTeValue.contract B c ram sp buf f ns vs ve le length minor pc h1 h2 h18 h23 h24 h15 h26 h21 scratch hbuf hraw fields ordered bound version memory stack aligned
    obtain ⟨actionAt,view',effect⟩ := HeadHeaderActionView.from_te post view
    have action := HeadClassSpec.te_action g f ns ne vs ve le minor te
    change ∃ n d after, _
    rw [show HeadActionSpec.action (bytes ram buf) f ns ne vs ve le minor 1024=HeadClassSpec.ofTe f (HeadTeValue.outcome (bytes ram buf) f vs ve le minor) from action]
    refine ⟨n,d,after,by omega,trace,actionAt,view',effect,?_,csr⟩
    intro r h1 h30 h12 h29 h14 h13 h11 h10 h31
    exact frame r h1 h10 h11 h12 h13 h14
end E5R.Thermostat.HeadHeaderValueDispatch
