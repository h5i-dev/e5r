import Projects.thermostat.HeadFieldsScanStart
import Projects.thermostat.HeadFieldsTerm
import Projects.thermostat.HeadFieldsLFReject
namespace E5R.Thermostat.HeadFieldsLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def endpoint (g : Nat → Nat) (i k cap : Nat) : Word :=
  if lineTerm g k cap=1 then 0x800033ea#32 else if lineTerm g k cap=2 then 0x8000342c#32
  else if k=i then 0x80003456#32 else 0x80002fbc#32

/-- Actual bounded header lineEnd/lineTerm through incomplete/400/empty-line
    completion or nonempty header-name parsing. Every byte access is derived. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i cap length : Nat)
    (hp : c.pc=0x80002f58#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : i<cap) (hn : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    let k := lineEnd g i cap
    ∃ n d, 10≤n ∧ n≤18+14*(cap-i) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint g i k cap ∧
      d.get 21=BitVec.ofNat 32 (k-i) ∧ d.get 25=BitVec.ofNat 32 (k-i)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 k ∧
      (lineTerm g k cap=0 → d.get 26=BitVec.ofNat 32 k) ∧ (lineTerm g k cap≠1 → d.get 1=400#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → r≠30 → r≠15 → r≠26 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c := by
  let g := bytes ram buf
  let k := lineEnd g i cap
  have lower : i≤k := scan_ge notEol g i cap
  have upper : k≤cap := scan_le notEol g i cap (by omega)
  obtain ⟨n,a,nlo,nhi,scan,pc,count,ptr,inverse,cursor,cache,frame,csr⟩ := HeadFieldsScanStart.contract B c ram sp buf i cap length
    hp h2 h24 h16 h17 hcap hraw hbuf hi hn hlen hm stack ha
  change a.pc=HeadFieldsScan.endpoint g k cap at pc
  by_cases inside : k<cap
  · obtain ⟨loadPtr,value⟩ := cache inside
    by_cases lf : g k=10
    · have atLF : a.pc=0x80003428#32 := by simpa only [HeadFieldsScan.endpoint,inside,lf,ite_true] using pc
      have term : lineTerm g k cap=2 := by simp only [lineTerm,show ¬cap≤k by omega,lf,ite_false,ite_true]
      obtain ⟨d,reject,endPC,status,frame2,csr2⟩ := HeadFieldsLFReject.contract B a ram atLF
      refine ⟨n+1,d,by omega,by omega,scan.trans reject,?_,(frame2 21 (by decide)).trans count,
        (frame2 25 (by decide)).trans inverse,(frame2 11 (by decide)).trans cursor,?_,fun _ => status,?_,csr2.trans csr⟩
      · change d.pc=endpoint g i k cap
        simpa [endpoint,term] using endPC
      · intro zero;rw [term] at zero;contradiction
      · intro r h10 h11 h21 h13 h25 h14 h30 h15 _ h1
        exact (frame2 r h1).trans (frame r h10 h11 h21 h13 h25 h14 h30 h15)
    · have cr : g k=13 := (HeadLineScanSpec.eol g i cap inside).resolve_left lf
      have atCR : a.pc=0x80002f9a#32 := by simpa only [HeadFieldsScan.endpoint,inside,lf,ite_true,ite_false] using pc
      have sum : i+(k-i)=k := by omega
      obtain ⟨b,d,blo,bhi,termTrace,endPC,endIndex,status,frame2,csr2⟩ := HeadFieldsTerm.contract B a ram sp buf i (k-i) cap length atCR
        ((frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24) count ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2)
        (by simpa only [sum] using loadPtr) ((frame 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16) hcap (by omega) hn hlen (by simpa only [sum] using cr) hm stack ha
      refine ⟨n+b,d,by omega,by omega,scan.trans termTrace,?_,(frame2 21 (by decide) (by decide) (by decide) (by decide)).trans count,
        (frame2 25 (by decide) (by decide) (by decide) (by decide)).trans inverse,
        (frame2 11 (by decide) (by decide) (by decide) (by decide)).trans cursor,?_,?_,?_,csr2.trans csr⟩
      · change d.pc=endpoint g i k cap
        change d.pc=HeadFieldsTerm.endpoint g i (k-i) cap at endPC
        simpa only [HeadFieldsTerm.endpoint,endpoint,sum,show (k-i=0) ↔ k=i by omega] using endPC
      · intro _;simpa only [sum] using endIndex
      · intro notMore
        apply status
        intro short
        have term : lineTerm g k cap=1 := by
          have bound : cap≤k+1 := by omega
          simp [lineTerm,show ¬cap≤k by omega,cr,bound]
        exact notMore term
      · intro r h10 h11 h21 h13 h25 h14 h30 h15 h26 h1
        exact (frame2 r h26 h13 h10 h1).trans (frame r h10 h11 h21 h13 h25 h14 h30 h15)
  · have last : k=cap := by omega
    have term : lineTerm g k cap=1 := by simp only [lineTerm,last,Nat.le_refl,ite_true]
    refine ⟨n,a,nlo,by omega,scan,?_,count,inverse,cursor,?_,?_,?_,csr⟩
    · change a.pc=endpoint g i k cap
      simpa only [HeadFieldsScan.endpoint,endpoint,inside,term,ite_true,ite_false] using pc
    · intro zero;rw [term] at zero;contradiction
    · intro notMore;exact False.elim (notMore term)
    · intro r h10 h11 h21 h13 h25 h14 h30 h15 _ _
      exact frame r h10 h11 h21 h13 h25 h14 h30 h15
end E5R.Thermostat.HeadFieldsLine
