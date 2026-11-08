import Projects.thermostat.PadPositive
import Projects.thermostat.CursorLayoutPreserve
import Projects.thermostat.IntegralReturned
import Projects.thermostat.AppendPost
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PadPositiveCursor
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p fmt obj src dst : Word)
    (cap pos : Nat) (xs : List (BitVec 8))
    (hp : c.pc = 0x80004514#32) (hsp : c.get 2 = p+96#32)
    (h10 : c.get 10 = fmt) (h11 : c.get 11 = 1#32) (h13 : c.get 13 = 0#32)
    (h14 : c.get 14 = src) (h15 : c.get 15 = BitVec.ofNat 32 xs.length)
    (hst : Memory.Block B p 96) (hsa : p.toNat%4 = 0)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hw : ramRead ram fmt .w = obj) (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32)
    (hf : ramRead ram (fmt+8#32) .w = 0#32) (hz : ramRead ram (fmt+12#32) .h = 0#32)
    (hsep : WordRegions.Disjoint fmt 14 p 96) (hrom : B.inRam 0x80005c10#32 4 = false)
    (h : CursorInput.Layout B ram (p+64#32) obj src dst cap pos xs)
    (ho : WordRegions.Disjoint obj 12 p 96) (hs : WordRegions.Disjoint src xs.length p 96) :
    ∃ d n r, n ≤ 6*xs.length+126 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      AppendPost.Post B c d ram r p obj dst 96 cap pos xs := by
  obtain ⟨a,r0,ta,hr,hframe⟩ := PadPositive.contract B c ram p fmt obj src (BitVec.ofNat 32 xs.length)
    hp hsp h10 h11 h13 h14 h15 hst hsa hm ha hw hv hf hz hsep hrom
  have hl : CursorInput.Layout B r0 (p+64#32) obj src dst cap pos xs := CursorInput.preserve h
    (fun i => hframe _ (ho i)) (fun i => hframe _ (hs i))
  have hpre := CursorInput.pre_of_layout hl hr.pc (by
    rw [hr.sp,hsp,BitVec.add_assoc]
    rfl) hr.writer hr.source hr.length
  obtain ⟨d,k,r,hk,td,hpost,hh⟩ := Cursor.contract_full B a r0 (p+64#32) obj src dst cap pos xs hpre
  have hsub (x : Word) (hx : ∀ i : Fin 96, x ≠ p+BitVec.ofNat 32 i.val) :
      ∀ i : Fin 32, x ≠ (p+64#32)+BitVec.ofNat 32 i.val := by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨64+i.val,by have := i.isLt;omega⟩
  refine ⟨d,85+k,r,by omega,ta.trans td,?_,hpost.result,hpost.pointer,hpost.capacity,hpost.position,hpost.written,?_,?_⟩
  · exact IntegralReady.returned hr hpost.returned hh
  · intro hn x hx
    exact (hpost.refused hn x (hsub x hx)).trans (hframe x hx)
  · intro x hx hout hobj
    exact (hpost.frame x (hsub x hx) hout hobj).trans (hframe x hx)
end E5R.Thermostat.PadPositiveCursor
