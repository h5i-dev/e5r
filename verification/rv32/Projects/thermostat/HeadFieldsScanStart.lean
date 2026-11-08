import Projects.thermostat.HeadFieldsScanInit
import Projects.thermostat.HeadFieldsScan
namespace E5R.Thermostat.HeadFieldsScanStart
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual header-line scan setup and complete scan. Its real min/slice guard
    is derived from the admitted current position and raw-length bounds. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i cap length : Nat)
    (hp : c.pc=0x80002f58#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : i<cap) (hn : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) :
    let g := bytes ram buf
    let k := lineEnd g i cap
    ∃ steps d, 10≤steps ∧ steps≤9+14*(cap-i) ∧ Quiet.Steps B img steps ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=HeadFieldsScan.endpoint g k cap ∧ d.get 21=BitVec.ofNat 32 (k-i) ∧ d.get 14=buf+BitVec.ofNat 32 (k-i) ∧
      d.get 25=BitVec.ofNat 32 (k-i)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 k ∧
      (k<cap → d.get 15=buf+BitVec.ofNat 32 k ∧ d.get 30=BitVec.ofNat 32 (g k)) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → r≠30 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  have test : taken .ltu (BitVec.ofNat 32 length) (BitVec.ofNat 32 i)=false := by
    simp only [taken,BitVec.ult,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : length<2^32),Nat.mod_eq_of_lt (by omega : i<2^32)]
    simp only [show ¬length<i by omega,decide_false]
  obtain ⟨a,setup,pc,raw,index,zero,relative,inverse,bufPtr,frame,csr⟩ := HeadFieldsScanInit.contract B c ram sp buf
    (BitVec.ofNat 32 i) (BitVec.ofNat 32 length) h2 h24 hraw hbuf test stack ha hp
  obtain ⟨n,d,nlo,nhi,scan,endPC,count,ptr,inverse2,cursor,cache,frame2,csr2⟩ := HeadFieldsScan.contract B a ram sp buf i 0 cap length
    pc relative zero (by simpa only [BitVec.add_zero] using bufPtr)
    ((frame 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h24)
    ((frame 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h16)
    ((frame 17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h17) inverse index
    ((frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h2) hcap hi hn hlen hm stack ha
  refine ⟨9+n,d,by omega,by omega,setup.trans scan,endPC,count,ptr,inverse2,cursor,cache,?_,csr2.trans csr⟩
  intro r h10 h11 h21 h13 h25 h14 h30 h15
  exact (frame2 r h21 h30 h14 h25 h11 h15).trans (frame r h10 h11 h21 h13 h25 h14)
end E5R.Thermostat.HeadFieldsScanStart
