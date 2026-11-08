import Projects.thermostat.HeadClMath
import Projects.thermostat.HeadClGuardAdd
import Projects.thermostat.HeadClGuard
import Projects.thermostat.HeadClFoldRaw
import Projects.thermostat.HeadClCompareBranch
import Projects.thermostat.HeadLineScanSpec
namespace E5R.Thermostat.HeadClStep
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- The real capacity check, input and ROM loads, ASCII folding, and comparison
    for one byte of the fourteen-byte Content-Length name. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (start length k : Nat)
    (hp : c.pc=0x800031b2#32) (h7 : c.get 7=14#32)
    (h13 : c.get 13=BitVec.ofNat 32 length-BitVec.ofNat 32 start)
    (h10 : c.get 10=BitVec.ofNat 32 (14-k))
    (h31 : c.get 31=buf+BitVec.ofNat 32 (start+k))
    (h30 : c.get 30=BitVec.ofNat 32 (0x80005de0+k))
    (width : start+14≤length) (bound : length≤2048) (hk : k<14)
    (mem : Memory.Block B buf length)
    (outside : B.inRam (BitVec.ofNat 32 (0x80005de0+k)) 1=false) :
    ∃ d, Quiet.Steps B img 9 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if lower (bytes ram buf (start+k))=litContentLength[k] then 0x800031d4#32 else 0x8000326e#32) ∧
      (∀ r : Reg, r≠19 → r≠12 → r≠29 → d.get r=c.get r) ∧ d.sameCsr c := by
  let actual := ram (buf+BitVec.ofNat 32 (start+k))
  let expected : BitVec 8 := BitVec.ofNat 8 litContentLength[k]
  obtain ⟨a,t0,p0,v19,f0,s0⟩ := HeadClGuardAdd.contract B c ram _ _ h13 h10 hp
  obtain ⟨b,t1,p1,f1,s1⟩ := HeadClGuard.contract B a ram _ 14#32 false p0 v19
    ((f0 7 (by decide)).trans h7) (HeadClMath.guard start length k width bound hk)
  have p1' : b.pc=0x800031ba#32 := by simpa using p1
  have b31 : b.get 31=buf+BitVec.ofNat 32 (start+k) := (f1 31).trans ((f0 31 (by decide)).trans h31)
  have b30 : b.get 30=BitVec.ofNat 32 (0x80005de0+k) := (f1 30).trans ((f0 30 (by decide)).trans h30)
  obtain ⟨e,t2,p2,v19',v29,v12,f2,s2⟩ := HeadClFoldRaw.contract B b ram _ _ actual expected b31 b30
    (.ram (Memory.block_access mem (by decide) (by omega)) rfl)
    (HeadClMath.literal_byte B ram ⟨k,hk⟩ outside) p1'
  have test : taken .ne (HeadFoldMath.word actual) (BitVec.ofNat 32 expected.toNat)=
      decide (lower (bytes ram buf (start+k))≠litContentLength[k]) := by
    rw [HeadFoldMath.comparison]
    have eb : expected.toNat=litContentLength[k] := by
      change litContentLength[k]%256=litContentLength[k]
      exact Nat.mod_eq_of_lt (HeadClMath.literal_bound ⟨k,hk⟩)
    rw [eb];rfl
  obtain ⟨d,t3,p3,f3,s3⟩ := HeadClCompareBranch.contract B e ram _ _ _ p2 v29 v12 test
  refine ⟨d,by simpa using (t0.trans (t1.trans (t2.trans t3))),?_,?_,s3.trans (s2.trans (s1.trans s0))⟩
  · by_cases same : lower (bytes ram buf (start+k))=litContentLength[k] <;> simpa [same] using p3
  · intro r h19 h12 h29
    exact (f3 r).trans ((f2 r h19 h29 h12).trans ((f1 r).trans (f0 r h19)))
end E5R.Thermostat.HeadClStep
