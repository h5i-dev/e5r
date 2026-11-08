import Projects.thermostat.HeadHeaderCapacity
import Projects.thermostat.HeadHeaderWidth
import Projects.thermostat.HeadHeaderTooMany
import Projects.thermostat.HeadHost
namespace E5R.Thermostat.HeadHeaderClass4
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (g : Nat → Nat) (start ne : Nat) (f : Fields) : Word :=
  if 16≤f.headers.length then 0x8000342c#32 else if ne-start≠4 then 0x80003192#32
  else if classify g start ne=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32

def updated (g : Nat → Nat) (start ne : Nat) (f : Fields) : Fields :=
  if 16≤f.headers.length ∨ ne-start≠4 then f else HeadHost.updated g start f

/-- Real add_header capacity guard and width-four classification/Host path.
    Other widths reach the actual CL/TE classifier entry with their live
    name length and line-end register preserved. Array commit follows later. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start ne length : Nat) (f : Fields)
    (hp : c.pc=0x800030fa#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h14 : c.get 14=BitVec.ofNat 32 (ne-start))
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (fields : HeadFieldsView.At ram sp f) (lower : start≤ne) (upper : ne≤length) (hlen : length≤2048)
    (mem : Memory.Block B buf length) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d after, 4≤n ∧ n≤47 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=endpoint g start ne f ∧
      (d.pc=0x8000342c#32 → d.get 1=(if 16≤f.headers.length then 431#32 else 400#32)) ∧
      HeadFieldsView.At after sp (updated g start ne f) ∧ (after=ram ∨ after=HeadHostFlagStore.memory ram sp) ∧
      (ne-start≠4 → d.get 14=BitVec.ofNat 32 (ne-start) ∧ d.get 11=c.get 11) ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  obtain ⟨a,capacity,pc,countCap,frame,csr⟩ := HeadHeaderCapacity.contract B c ram f.headers.length hp h9 fields.count_bound
  by_cases full : 16≤f.headers.length
  · have atFull : a.pc=0x800034d4#32 := by simpa only [full,ite_true] using pc
    obtain ⟨d,reject,pc2,status,frame2,csr2⟩ := HeadHeaderTooMany.contract B a ram atFull
    refine ⟨4,d,ram,by decide,by decide,capacity.trans reject,?_,?_,?_,Or.inl rfl,?_,?_,csr2.trans csr⟩
    · change d.pc=endpoint g start ne f
      simpa only [endpoint,full,ite_true] using pc2
    · intro _;simpa only [full,ite_true] using status
    · change HeadFieldsView.At ram sp (updated g start ne f)
      simpa only [updated,full,true_or,ite_true] using fields
    · intro _
      exact ⟨(frame2 14 (by decide)).trans ((frame 14 (by decide)).trans h14),(frame2 11 (by decide)).trans (frame 11 (by decide))⟩
    · intro r h1 h10 _ _ _ _
      exact (frame2 r h1).trans (frame r h10)
  · have atWidth : a.pc=0x80003100#32 := by simpa only [full,ite_false] using pc
    obtain ⟨b,width,pc2,four,frame2,csr2⟩ := HeadHeaderWidth.contract B a ram (ne-start) atWidth ((frame 14 (by decide)).trans h14) (by omega)
    have source (r : Reg) (h10 : r≠10) : b.get r=c.get r := (frame2 r h10).trans (frame r h10)
    by_cases other : ne-start≠4
    · refine ⟨4,b,ram,by decide,by decide,capacity.trans width,?_,?_,?_,Or.inl rfl,?_,?_,csr2.trans csr⟩
      · change b.pc=endpoint g start ne f
        simpa [endpoint,full,other] using pc2
      · intro impossible
        have atOther : b.pc=0x80003192#32 := by simpa [other] using pc2
        exact False.elim ((by decide : 0x80003192#32≠0x8000342c#32) (atOther.symm.trans impossible))
      · change HeadFieldsView.At ram sp (updated g start ne f)
        simpa [updated,other] using fields
      · intro _;exact ⟨(source 14 (by decide)).trans h14,source 11 (by decide)⟩
      · intro r _ h10 _ _ _ _;exact source r h10
    · have atHost : b.pc=0x80003106#32 := by simpa only [other,ite_false] using pc2
      have ending : ne=start+4 := by omega
      obtain ⟨n,d,after,nlo,nhi,host,pc3,view,effect,frame3,csr3⟩ := HeadHost.contract B b ram sp buf start length f atHost
        ((source 2 (by decide)).trans h2) ((source 24 (by decide)).trans h24) hraw hbuf fields (by omega) hlen mem hm ha
      refine ⟨4+n,d,after,by omega,by omega,(capacity.trans width).trans host,?_,?_,?_,effect,?_,?_,csr3.trans (csr2.trans csr)⟩
      · change d.pc=endpoint g start ne f
        rw [endpoint,ite_eq_right full,ite_eq_right other,ending]
        exact pc3
      · intro _
        have value : d.get 1=400#32 := (frame3 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((source 1 (by decide)).trans h1)
        simpa only [full,ite_false] using value
      · change HeadFieldsView.At after sp (updated g start ne f)
        simpa only [updated,full,other,false_or,ite_false] using view
      · intro contradiction;exact False.elim (contradiction (by omega))
      · intro r _ h10 h11 h12 h13 h14
        exact (frame3 r h10 h11 h12 h13 h14).trans (source r h10)
end E5R.Thermostat.HeadHeaderClass4
