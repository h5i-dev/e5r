import Projects.thermostat.HeadTePreflight
import Projects.thermostat.HeadTeValueWidth
import Projects.thermostat.HeadTeBuffer
import Projects.thermostat.HeadChunkedCompare
import Projects.thermostat.HeadTeFlagMemory
namespace E5R.Thermostat.HeadTeValue
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The independent TE value rule, before the common header-array append. -/
def outcome (g : Nat → Nat) (f : Fields) (vs ve le minor : Nat) : Option Nat :=
  if HeadTePreflight.Bad f ve le minor then some 400
  else if eqCi g vs ve litChunked then none else some 501

def Post (ram after : Word → BitVec 8) (sp : Word) (d : Core) (result : Option Nat) : Prop :=
  match result with
  | some status => d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status ∧ after=ram
  | none => d.pc=0x800033b6#32 ∧ after=HeadTeFlagStore.memory ram sp

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word)
    (f : Fields) (ns vs ve le length minor : Nat)
    (hp : c.pc=0x800032ae#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h18 : c.get 18=BitVec.ofNat 32 (1-minor)) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (h24 : c.get 24=BitVec.ofNat 32 ns) (h15 : c.get 15=BitVec.ofNat 32 vs)
    (h26 : c.get 26=BitVec.ofNat 32 le) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (fields : HeadFieldsView.At ram sp f) (ordered : ns≤vs ∧ vs≤ve ∧ ve≤le ∧ le≤length)
    (bound : length≤2048) (version : minor≤1) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) :
    let result := outcome (bytes ram buf) f vs ve le minor
    ∃ n d after, 2≤n ∧ n≤81 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ Post ram after sp d result ∧
      HeadFieldsView.At after sp (if result=none then {f with te := true} else f) ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have stack327 : Memory.Block B sp 327 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 327) (by decide) (by decide))
  have stack56 : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 56) (by decide) (by decide))
  obtain ⟨n,a,lo,hi,preflight,pc,frame,csr⟩ := HeadTePreflight.contract B c ram sp f ve le minor hp h2 h18 h23 scratch fields ordered.2.2.1 (by omega) version stack327 aligned
  by_cases bad : HeadTePreflight.Bad f ve le minor
  · have result : outcome g f vs ve le minor=some 400 := by simp only [outcome,bad,ite_true]
    have endPC : a.pc=0x8000342c#32 := by simpa only [bad,ite_true] using pc
    change ∃ n d after, _
    rw [show outcome (bytes ram buf) f vs ve le minor=some 400 from result]
    exact ⟨n,a,ram,lo,by omega,preflight,⟨endPC,(frame 1 (by decide)).trans h1,rfl⟩,fields,
      fun r _ h10 _ _ _ _ => frame r h10,csr⟩
  · have veEq : ve=le := by
      by_cases neq : ve≠le
      · exact False.elim (bad (Or.inr (Or.inr (Or.inr neq))))
      · omega
    have atWidth : a.pc=0x800032c8#32 := by simpa only [bad,ite_false] using pc
    obtain ⟨d,width,pc2,status,frame2,csr2⟩ := HeadTeValueWidth.contract B a ram ns vs le atWidth
      ((frame 24 (by decide)).trans h24) ((frame 15 (by decide)).trans h15)
      ((frame 26 (by decide)).trans h26) ((frame 21 (by decide)).trans h21) (by omega) (by omega) (by omega)
    have source (r : Reg) (h1 : r≠1) (h10 : r≠10) : d.get r=c.get r := (frame2 r h1 h10).trans (frame r h10)
    by_cases seven : le-vs=7
    · have widthPC : d.pc=0x800032dc#32 := by simpa only [seven,ite_true] using pc2
      have veWidth : ve=vs+7 := by omega
      obtain ⟨e,buffer,pc3,pointer,frame3,csr3⟩ := HeadTeBuffer.contract B d ram sp buf (BitVec.ofNat 32 vs)
        ((source 2 (by decide) (by decide)).trans h2) ((source 15 (by decide) (by decide)).trans h15) hbuf stack56 aligned widthPC
      have source3 (r : Reg) (h1 : r≠1) (h10 : r≠10) : e.get r=c.get r := (frame3 r h10).trans (source r h1 h10)
      obtain ⟨k,z,klo,khi,compare,pc4,frame4,csr4⟩ := HeadChunkedCompare.contract B e ram sp buf vs length pc3
        ((source3 2 (by decide) (by decide)).trans h2) ((source3 15 (by decide) (by decide)).trans h15) pointer hraw (by omega) bound mem stack56 aligned
      change z.pc=(if HeadChunkedSpec.Prefix g vs then 0x800033b0#32 else 0x8000342c#32) at pc4
      have chunked : eqCi g vs ve litChunked=decide (HeadChunkedSpec.Prefix g vs) := by
        rw [veWidth,HeadChunkedSpec.eqCi_chunked]
      have frameAll (r : Reg) (h1 : r≠1) (h10 : r≠10) (h11 : r≠11) (h12 : r≠12) (h13 : r≠13) (h14 : r≠14) : z.get r=c.get r :=
        (frame4 r h10 h11 h12 h13 h14).trans (source3 r h1 h10)
      have z1 : z.get 1=501#32 := (frame4 1 (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((frame3 1 (by decide)).trans status)
      by_cases accepted : HeadChunkedSpec.Prefix g vs
      · have result : outcome g f vs ve le minor=none := by simp only [outcome,bad,ite_false,chunked,accepted,decide_true,ite_true]
        have zpc : z.pc=0x800033b0#32 := by simpa only [accepted,ite_true] using pc4
        obtain ⟨endCore,store,endPC,one,storeFrame,storeCsr⟩ := HeadTeFlagStore.contract B z ram sp
          ((frameAll 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
          (Memory.block_access stack (off := 326) (by decide) (by decide)) zpc
        change ∃ n d after, _
        rw [show outcome (bytes ram buf) f vs ve le minor=none from result]
        refine ⟨n+6+2+k+2,endCore,HeadTeFlagStore.memory ram sp,by omega,by omega,
          (((preflight.trans width).trans buffer).trans compare).trans store,⟨endPC,rfl⟩,HeadTeFlagMemory.fields fields,?_,storeCsr.trans (csr4.trans (csr3.trans (csr2.trans csr)))⟩
        intro r h1 h10 h11 h12 h13 h14
        exact (storeFrame r h10).trans (frameAll r h1 h10 h11 h12 h13 h14)
      · have result : outcome g f vs ve le minor=some 501 := by simp only [outcome,bad,ite_false,chunked,accepted,decide_false,Bool.false_eq_true,ite_false]
        have zpc : z.pc=0x8000342c#32 := by simpa only [accepted,ite_false] using pc4
        change ∃ n d after, _
        rw [show outcome (bytes ram buf) f vs ve le minor=some 501 from result]
        exact ⟨n+6+2+k,z,ram,by omega,by omega,((preflight.trans width).trans buffer).trans compare,⟨zpc,z1,rfl⟩,fields,frameAll,csr4.trans (csr3.trans (csr2.trans csr))⟩
    · have noChunked : eqCi g vs ve litChunked=false := by
        rw [eqCi,ite_eq_left (by change ve<vs ∨ ve-vs≠7;omega)]
      have result : outcome g f vs ve le minor=some 501 := by simp only [outcome,bad,ite_false,noChunked,Bool.false_eq_true,ite_false]
      have endPC : d.pc=0x8000342c#32 := by simpa only [seven,ite_false] using pc2
      change ∃ n d after, _
      rw [show outcome (bytes ram buf) f vs ve le minor=some 501 from result]
      exact ⟨n+6,d,ram,by omega,by omega,preflight.trans width,⟨endPC,status,rfl⟩,fields,
        fun r h1 h10 _ _ _ _ => source r h1 h10,csr2.trans csr⟩
end E5R.Thermostat.HeadTeValue
