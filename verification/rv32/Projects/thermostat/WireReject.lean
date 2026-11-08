import Projects.thermostat.WireEngine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireReject
open E5R E5R.Thermostat

theorem rejected (B : Board) (c : Core) (ram : Word → BitVec 8) (p req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (status : Nat)
    (hwire : Wire.Pre B c ram (p+64#32) req pathPtr bodyPtr path body first)
    (hlayout : DecodedEngine.Pre B (c.goto 0x800005f4#32) ram p admin s)
    (hra : c.get 1 = 0x800005f4#32) (hdecode : WireSpec.decode path body first = .error status) :
    ∃ n d, n ≤ 18*body.length+307 ∧
      DetSteps B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram (p+64#32) c⟩ ∧
      d.pc = 0x800005a2#32 ∧ (d.get 20).toNat = status ∧
      Encoding.SnapshotAt (DecodeSave.memory ram (p+64#32) c) (c.get 23+4#32) s ∧
      ramRead (DecodeSave.memory ram (p+64#32) c) (c.get 23) .w = 0#32 ∧ d.get 2 = c.get 2 ∧ d.get 8 = c.get 8 ∧ d.get 9 = c.get 9 ∧
      d.get 22 = c.get 22 ∧ d.get 23 = c.get 23 ∧ d.sameCsr c := by
  obtain ⟨a,n,hn,ht,hpost⟩ := Wire.contract B c ram (p+64#32) req pathPtr bodyPtr path body first hwire
  have hlayout'  := WireEngine.layout B c a ram p path body first admin s hlayout hra hpost
  have he : WireSpec.ResultWord (a.get 10) (.error status) := by
    have hh := hpost.result;rw [hdecode] at hh;exact hh
  obtain ⟨d,td,hpc,hstatus,dframe,dcsr⟩ := WireCaller.error B a (DecodeSave.memory ram (p+64#32) c) status hlayout'.pc he
  have h23 : a.get 23 = c.get 23 := hpost.frame 23 (by decide)
  exact ⟨n+4,d,by omega,ht.trans td,hpc,hstatus,by simpa only [h23] using hlayout'.state,
    by simpa only [h23] using hlayout'.borrow,
    (dframe 2 (by decide) (by decide) (by decide)).trans hpost.sp,
    (dframe 8 (by decide) (by decide) (by decide)).trans hpost.s0,
    (dframe 9 (by decide) (by decide) (by decide)).trans hpost.s1,
    (dframe 22 (by decide) (by decide) (by decide)).trans (hpost.frame 22 (by decide)),
    (dframe 23 (by decide) (by decide) (by decide)).trans h23,dcsr.trans hpost.csr⟩

end E5R.Thermostat.WireReject
