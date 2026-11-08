import Projects.thermostat.HeadVersionBounds
import Projects.thermostat.HeadVersionDigits
import Projects.thermostat.HeadVersionInputSpec
import Projects.thermostat.HeadVersionResult
namespace E5R.Thermostat.HeadVersionDigitsRun
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual digit bounds checks, RAM loads and version classification composed.
    All three byte-read premises are derived from the available input slice. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf limits dst : Word) (te length : Nat)
    (hp : c.pc=0x80002e8c#32) (h2 : c.get 2=sp) (h7 : c.get 7=BitVec.ofNat 32 (te-1))
    (h6 : c.get 6=buf+BitVec.ofNat 32 (te-1)) (h13 : c.get 13=limits) (h15 : c.get 15=400#32)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hlenWord : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (hdst : ramRead ram (sp+52#32) .w=dst)
    (hm : Memory.Block B sp 56) (ha : sp.toNat%4=0) (mem : Memory.Block B buf length)
    (ht : 0<te) (hw : te+9≤length) (hlen : length≤2048) :
    let g := bytes ram buf
    let v := versionDigits (g (te+6)) (g (te+7)) (g (te+8))
    ∃ n d, 15≤n ∧ n≤34 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ HeadVersionResult.At d v limits dst ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → r≠15 → r≠20 → r≠8 → r≠18 → d.get r=c.get r) ∧ d.sameCsr c := by
  let pos := BitVec.ofNat 32 (te-1)
  let base := buf+pos
  have address (k : Nat) : buf+pos+BitVec.ofNat 32 (k+1)=buf+BitVec.ofNat 32 (te+k) :=
    HeadVersionInputSpec.address buf te k ht
  have access (k : Nat) (hk : 6≤k ∧ k≤8) : B.inRam (buf+pos+BitVec.ofNat 32 (k+1)) 1=true := by
    rw [address k]
    exact Memory.block_access mem (off := te+k) (by decide) (by change te+k+1≤length;omega)
  obtain ⟨a,bounds,pc,last,len,frame,csr⟩ := HeadVersionBounds.contract B c ram sp te length hp h7 h2 hlenWord hm ha ht hw hlen
  obtain ⟨n,d,nlo,nhi,trace,result,frame2,csr2⟩ := HeadVersionDigits.contract B a ram sp pos base limits buf dst
    (ram (buf+pos+7#32)) (ram (base+8#32)) (ram (base+9#32)) pc
    ((frame 2 (by decide) (by decide)).trans h2) ((frame 7 (by decide) (by decide)).trans h7)
    ((frame 6 (by decide) (by decide)).trans h6) ((frame 13 (by decide) (by decide)).trans h13)
    ((frame 15 (by decide) (by decide)).trans h15) hm ha hbuf hdst (access 6 (by decide)) rfl (access 7 (by decide)) rfl (access 8 (by decide)) rfl
  refine ⟨9+n,d,by omega,by omega,bounds.trans trace,?_,?_,csr2.trans csr⟩
  · change HeadVersionResult.At d
      (versionDigits (ram (buf+pos+7#32)).toNat (ram (base+8#32)).toNat (ram (base+9#32)).toNat) limits dst at result
    simpa only [base,address 6,address 7,address 8,bytes] using result
  · intro r h10 h11 h12 h13 h14 h15 h20 h8 h18
    exact (frame2 r h10 h11 h12 h13 h14 h15 h20 h8 h18).trans (frame r h10 h11)
end E5R.Thermostat.HeadVersionDigitsRun
