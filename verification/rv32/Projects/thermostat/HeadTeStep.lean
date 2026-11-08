import Projects.thermostat.HeadTeMath
import Projects.thermostat.HeadTeGuardAdd
import Projects.thermostat.HeadTeGuard
import Projects.thermostat.HeadTeFoldRaw
import Projects.thermostat.HeadTeCompareBranch
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadTeStep
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start length k : Nat)
    (hp : c.pc=0x80003284#32)
    (h11 : c.get 11=BitVec.ofNat 32 length-BitVec.ofNat 32 start)
    (h10 : c.get 10=BitVec.ofNat 32 (17-k))
    (h20 : c.get 20=buf+BitVec.ofNat 32 (start+k))
    (h13 : c.get 13=BitVec.ofNat 32 (0x80005dee+k))
    (width : start+17≤length) (bound : length≤2048) (hk : k<17)
    (mem : Memory.Block B buf length)
    (outside : B.inRam (BitVec.ofNat 32 (0x80005dee+k)) 1=false) :
    ∃ d, Quiet.Steps B img 10 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if lower (bytes ram buf (start+k))=litTransferEncoding[k] then 0x800032a6#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠12 → r≠14 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let actual := ram (buf+BitVec.ofNat 32 (start+k))
  let expected : BitVec 8 := BitVec.ofNat 8 litTransferEncoding[k]
  obtain ⟨a,t0,p0,v12,v14,f0,s0⟩ := HeadTeGuardAdd.contract B c ram _ _ h11 h10 hp
  obtain ⟨b,t1,p1,f1,s1⟩ := HeadTeGuard.contract B a ram _ 17#32 false p0 v12 v14
    (HeadTeMath.guard start length k width bound hk)
  have p1' : b.pc=0x8000328e#32 := by simpa using p1
  have b20 : b.get 20=buf+BitVec.ofNat 32 (start+k) := (f1 20).trans ((f0 20 (by decide) (by decide)).trans h20)
  have b13 : b.get 13=BitVec.ofNat 32 (0x80005dee+k) := (f1 13).trans ((f0 13 (by decide) (by decide)).trans h13)
  obtain ⟨e,t2,p2,folded,shifted,literal,f2,s2⟩ := HeadTeFoldRaw.contract B b ram _ _ actual expected b20 b13
    (.ram (Memory.block_access mem (by decide) (by omega)) rfl)
    (HeadTeMath.literal_byte B ram ⟨k,hk⟩ outside) p1'
  have test : taken .ne (HeadFoldMath.word actual) (BitVec.ofNat 32 expected.toNat)=
      decide (lower (bytes ram buf (start+k))≠litTransferEncoding[k]) := by
    rw [HeadFoldMath.comparison]
    have eb : expected.toNat=litTransferEncoding[k] := by
      change litTransferEncoding[k]%256=litTransferEncoding[k]
      exact Nat.mod_eq_of_lt (HeadTeMath.literal_bound ⟨k,hk⟩)
    rw [eb];rfl
  obtain ⟨d,t3,p3,f3,s3⟩ := HeadTeCompareBranch.contract B e ram _ _ _ p2 folded literal test
  refine ⟨d,by simpa using (t0.trans (t1.trans (t2.trans t3))),?_,?_,s3.trans (s2.trans (s1.trans s0))⟩
  · by_cases same : lower (bytes ram buf (start+k))=litTransferEncoding[k] <;> simpa [same] using p3
  · intro r h12 h14 h29
    exact (f3 r).trans ((f2 r h12 h14 h29).trans ((f1 r).trans (f0 r h12 h14)))
end E5R.Thermostat.HeadTeStep
