import Projects.thermostat.HeadFieldsCRGuard
import Projects.thermostat.HeadFieldsCRRead
import Projects.thermostat.HeadFieldsEmpty
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadFieldsTerm
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (g : Nat → Nat) (i t cap : Nat) : Word :=
  if lineTerm g (i+t) cap=1 then 0x800033ea#32
  else if lineTerm g (i+t) cap=2 then 0x8000342c#32
  else if t=0 then 0x80003456#32 else 0x80002fbc#32

/-- Actual CRLF/short/bad-terminator and empty-header-line tests. The next
    byte is loaded only after the actual capacity branch establishes its bound. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i t cap length : Nat)
    (hp : c.pc=0x80002f9a#32) (h24 : c.get 24=BitVec.ofNat 32 i) (h21 : c.get 21=BitVec.ofNat 32 t) (h2 : c.get 2=sp)
    (h15 : c.get 15=buf+BitVec.ofNat 32 (i+t)) (h16 : c.get 16=10#32)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hi : i+t<cap) (hn : cap≤length) (hlen : length≤2048)
    (cr : bytes ram buf (i+t)=13) (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    ∃ n d, 4≤n ∧ n≤9 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint g i t cap ∧
      d.get 26=BitVec.ofNat 32 (i+t) ∧ (¬cap≤i+t+1 → d.get 1=400#32) ∧
      (∀ r : Reg, r≠26 → r≠13 → r≠10 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  have term : lineTerm g (i+t) cap=(if cap≤i+t+1 then 1 else if g (i+t+1)=10 then 0 else 2) := by
    have cr' : g (i+t)=13 := cr
    unfold lineTerm
    simp only [show ¬cap≤i+t by omega,cr',show ¬(13=10) by decide,ite_false]
    by_cases short : cap≤i+t+1 <;> by_cases lf : g (i+t+1)=10 <;> simp [short,lf]
  obtain ⟨a,guard,pc,endIndex,nextIndex,capWord,frame,csr⟩ := HeadFieldsCRGuard.contract B c ram sp i t cap hp h24 h21 h2 hcap hi (by omega) stack ha
  by_cases short : cap≤i+t+1
  · refine ⟨4,a,by decide,by decide,guard,?_,endIndex,fun full => False.elim (full short),?_,csr⟩
    · change a.pc=endpoint g i t cap
      simpa [endpoint,term,short] using pc
    · intro r h26 h13 h10 _;exact frame r h26 h13 h10
  · have atRead : a.pc=0x80002fa8#32 := by simpa only [short,ite_false] using pc
    let p := buf+BitVec.ofNat 32 (i+t)
    let byte := ram (p+1#32)
    have address : p+1#32=buf+BitVec.ofNat 32 (i+t+1) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
    have byteNat : byte.toNat=g (i+t+1) := by change (ram (p+1#32)).toNat=_;rw [address];rfl
    have access : B.inRam (p+1#32) 1=true := by
      rw [address]
      exact Memory.block_access hm (off := i+t+1) (by decide) (by change i+t+1+1≤length;omega)
    obtain ⟨b,read,pc2,value,status,frame2,csr2⟩ := HeadFieldsCRRead.contract B a ram p byte atRead
      ((frame 15 (by decide) (by decide) (by decide)).trans h15) ((frame 16 (by decide) (by decide) (by decide)).trans h16) access rfl
    change b.pc=(if byte.toNat=10 then _ else _) at pc2
    rw [byteNat] at pc2
    have source (r : Reg) (h26 : r≠26) (h13 : r≠13) (h10 : r≠10) (h1 : r≠1) : b.get r=c.get r :=
      (frame2 r h10 h1).trans (frame r h26 h13 h10)
    by_cases lf : g (i+t+1)=10
    · have atEmpty : b.pc=0x80002fb4#32 := by simpa only [lf,ite_true] using pc2
      obtain ⟨n,d,nlo,nhi,empty,endPC,frame3,csr3⟩ := HeadFieldsEmpty.contract B b ram i t atEmpty
        ((source 21 (by decide) (by decide) (by decide) (by decide)).trans h21) ((source 24 (by decide) (by decide) (by decide) (by decide)).trans h24) ((frame2 26 (by decide) (by decide)).trans endIndex) (by omega)
      refine ⟨4+3+n,d,by omega,by omega,(guard.trans read).trans empty,?_,
        (frame3 26).trans ((frame2 26 (by decide) (by decide)).trans endIndex),fun _ => (frame3 1).trans status,?_,csr3.trans (csr2.trans csr)⟩
      · change d.pc=endpoint g i t cap
        simpa [endpoint,term,short,lf] using endPC
      · intro r h26 h13 h10 h1
        exact (frame3 r).trans (source r h26 h13 h10 h1)
    · refine ⟨7,b,by decide,by decide,guard.trans read,?_,
        (frame2 26 (by decide) (by decide)).trans endIndex,fun _ => status,source,csr2.trans csr⟩
      change b.pc=endpoint g i t cap
      simpa [endpoint,term,short,lf] using pc2
end E5R.Thermostat.HeadFieldsTerm
