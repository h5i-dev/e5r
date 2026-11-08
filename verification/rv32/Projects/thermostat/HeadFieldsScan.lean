import Projects.thermostat.QuietPrefix
import Projects.thermostat.HeadFieldsScanStep
import Projects.thermostat.HeadFieldsScanAdvance
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadFieldsScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (g : Nat → Nat) (k cap : Nat) : Word :=
  if k<cap then if g k=10 then 0x80003428#32 else 0x80002f9a#32 else 0x800033ea#32

/-- Whole actual bounded header-line scan. Its end index is independent
    lineEnd; real panic guards are excluded by current<cap≤raw length. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i t cap length : Nat)
    (hp : c.pc=0x80002f6e#32) (h13 : c.get 13=BitVec.ofNat 32 i-BitVec.ofNat 32 length)
    (h21 : c.get 21=BitVec.ofNat 32 t) (h14 : c.get 14=buf+BitVec.ofNat 32 t) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32) (h25 : c.get 25=BitVec.ofNat 32 t+0xffffffff#32)
    (h11 : c.get 11=BitVec.ofNat 32 (i+t)) (h2 : c.get 2=sp)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hi : i+t<cap) (hn : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    let k := lineEnd g (i+t) cap
    ∃ steps d, 0<steps ∧ steps≤14*(cap-(i+t)) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=endpoint g k cap ∧ d.get 21=BitVec.ofNat 32 (k-i) ∧ d.get 14=buf+BitVec.ofNat 32 (k-i) ∧
      d.get 25=BitVec.ofNat 32 (k-i)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 k ∧
      (k<cap → d.get 15=buf+BitVec.ofNat 32 k ∧ d.get 30=BitVec.ofNat 32 (g k)) ∧
      (∀ r : Reg, r≠21 → r≠30 → r≠14 → r≠25 → r≠11 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let byte := ram (buf+BitVec.ofNat 32 (i+t))
  obtain ⟨n,a,nlo,nhi,read,pc,ptr,value,frame,csr⟩ := HeadFieldsScanStep.contract B c ram buf i t length hp h13 h21 h14 h24 h16 h17 (by omega) hlen hm
  change a.pc=(if g (i+t)=10 then 0x80003428#32 else if g (i+t)=13 then 0x80002f9a#32 else 0x80002f86#32) at pc
  by_cases lf : g (i+t)=10
  · have stop : lineEnd g (i+t) cap=i+t := HeadLineScanSpec.stop g (i+t) cap hi (Or.inl lf)
    change ∃ steps d, _
    rw [stop]
    refine ⟨n,a,by omega,by omega,read,?_,?_,?_,?_,(frame 11 (by decide) (by decide)).trans h11,fun _ => ⟨ptr,value⟩,?_,csr⟩
    · change a.pc=endpoint g (i+t) cap
      simpa [endpoint,hi,lf] using pc
    · simpa only [show i+t-i=t by omega] using (frame 21 (by decide) (by decide)).trans h21
    · simpa only [show i+t-i=t by omega] using (frame 14 (by decide) (by decide)).trans h14
    · simpa only [show i+t-i=t by omega] using (frame 25 (by decide) (by decide)).trans h25
    · intro r _ h30 _ _ _ h15;exact frame r h15 h30
  · by_cases cr : g (i+t)=13
    · have stop : lineEnd g (i+t) cap=i+t := HeadLineScanSpec.stop g (i+t) cap hi (Or.inr cr)
      change ∃ steps d, _
      rw [stop]
      refine ⟨n,a,by omega,by omega,read,?_,?_,?_,?_,(frame 11 (by decide) (by decide)).trans h11,fun _ => ⟨ptr,value⟩,?_,csr⟩
      · change a.pc=endpoint g (i+t) cap
        simpa [endpoint,hi,lf,cr] using pc
      · simpa only [show i+t-i=t by omega] using (frame 21 (by decide) (by decide)).trans h21
      · simpa only [show i+t-i=t by omega] using (frame 14 (by decide) (by decide)).trans h14
      · simpa only [show i+t-i=t by omega] using (frame 25 (by decide) (by decide)).trans h25
      · intro r _ h30 _ _ _ h15;exact frame r h15 h30
    · have atAdvance : a.pc=0x80002f86#32 := by simpa only [lf,cr,ite_false] using pc
      obtain ⟨b,e,blo,bhi,advance,pc2,count2,ptr2,inverse2,cursor2,frame2,csr2⟩ := HeadFieldsScanAdvance.contract B a ram sp buf i t cap atAdvance
        ((frame 21 (by decide) (by decide)).trans h21) ((frame 24 (by decide) (by decide)).trans h24) ((frame 14 (by decide) (by decide)).trans h14)
        ((frame 25 (by decide) (by decide)).trans h25) ((frame 11 (by decide) (by decide)).trans h11) ((frame 2 (by decide) (by decide)).trans h2) hcap hi (by omega) stack ha
      have source (r : Reg) (h21 : r≠21) (h30 : r≠30) (h14 : r≠14) (h25 : r≠25) (h11 : r≠11) (h15 : r≠15) : e.get r=c.get r :=
        (frame2 r h21 h30 h14 h25 h11 h15).trans (frame r h15 h30)
      have specAdvance : lineEnd g (i+t) cap=lineEnd g (i+(t+1)) cap := by
        simpa only [Nat.add_assoc] using HeadLineScanSpec.advance g (i+t) cap hi lf cr
      by_cases more : i+(t+1)<cap
      · have atLoop : e.pc=0x80002f6e#32 := by simpa only [more,ite_true] using pc2
        obtain ⟨rest,d,rlo,rhi,tail,pc3,count3,ptr3,inverse3,cursor3,cache3,frame3,csr3⟩ := contract B e ram sp buf i (t+1) cap length atLoop
          ((source 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13) count2 ptr2 ((source 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24)
          ((source 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16) ((source 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17) inverse2 cursor2
          ((source 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) hcap more hn hlen hm stack ha
        change ∃ steps d, _
        rw [specAdvance]
        refine ⟨n+b+rest,d,by omega,by omega,(read.trans advance).trans tail,pc3,count3,ptr3,inverse3,cursor3,cache3,?_,csr3.trans (csr2.trans csr)⟩
        intro r h21 h30 h14 h25 h11 h15
        exact (frame3 r h21 h30 h14 h25 h11 h15).trans (source r h21 h30 h14 h25 h11 h15)
      · have last : i+(t+1)=cap := by omega
        have stop : lineEnd g (i+t) cap=cap := by rw [specAdvance,last,HeadLineScanSpec.end_at]
        change ∃ steps d, _
        rw [stop]
        refine ⟨n+b,e,by omega,by omega,read.trans advance,?_,?_,?_,?_,?_,by intro lt;omega,source,csr2.trans csr⟩
        · simpa only [endpoint,Nat.lt_irrefl,more,ite_false] using pc2
        · simpa only [show cap-i=t+1 by omega] using count2
        · simpa only [show cap-i=t+1 by omega] using ptr2
        · simpa only [show cap-i=t+1 by omega] using inverse2
        · simpa only [last] using cursor2
termination_by cap-(i+t)
 decreasing_by omega
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i t cap length : Nat)
    (hp : c.pc=0x80002f6e#32) (h13 : c.get 13=BitVec.ofNat 32 i-BitVec.ofNat 32 length)
    (h21 : c.get 21=BitVec.ofNat 32 t) (h14 : c.get 14=buf+BitVec.ofNat 32 t) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32) (h25 : c.get 25=BitVec.ofNat 32 t+0xffffffff#32)
    (h11 : c.get 11=BitVec.ofNat 32 (i+t)) (h2 : c.get 2=sp)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hi : i+t<cap) (hn : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    let k := lineEnd g (i+t) cap
    ∃ steps d, 0<steps ∧ steps≤14*(cap-(i+t)) ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=endpoint g k cap ∧ d.get 21=BitVec.ofNat 32 (k-i) ∧ d.get 14=buf+BitVec.ofNat 32 (k-i) ∧
      d.get 25=BitVec.ofNat 32 (k-i)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 k ∧
      (k<cap → d.get 15=buf+BitVec.ofNat 32 k ∧ d.get 30=BitVec.ofNat 32 (g k)) ∧
      (∀ r : Reg, r≠21 → r≠30 → r≠14 → r≠25 → r≠11 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,hlo,bound,trace,pc,count,ptr,inverse,cursor,cache,frame,csr⟩ := contract B c ram sp buf i t cap length
    hp h13 h21 h14 h24 h16 h17 h25 h11 h2 hcap hi hn hlen hm stack ha
  exact ⟨steps,d,hlo,bound,Interrupt.close trace.det masked,pc,count,ptr,inverse,cursor,cache,frame,csr,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsScan
