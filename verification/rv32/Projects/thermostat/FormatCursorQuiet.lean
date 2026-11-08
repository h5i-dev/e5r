-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.FormatCursor
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CursorFullQuiet
import Projects.thermostat.FormatInputQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.FormatCursor
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt obj src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) (h : FormatInput.Pre B c ram sp fmt obj src dst flags cap pos xs)
    (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d n r, n ≤ 6*xs.length+78 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post B c d ram r sp obj dst cap pos xs := by
  obtain ⟨a,ta,ha,hcursor⟩ := E5R.Thermostat.FormatInput.establishes_quiet h hrom
  obtain ⟨d,n,r,hn,td,hpost,hhigh⟩ := E5R.Thermostat.Cursor.contract_full_quiet B a (FormatStrSave.memory ram sp c) (sp+32#32) obj src dst cap pos xs hcursor
  have hf (x : Word) (hx : ∀ i : Fin 64, x ≠ sp+BitVec.ofNat 32 i.val) :
      ∀ i : Fin 32, x ≠ (sp+32#32)+BitVec.ofNat 32 i.val := by
    intro i
    have hi := i.isLt
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨32+i.val,by omega⟩
  refine ⟨d,37+n,r,by omega,ta.trans td,?_,hpost.result,hpost.pointer,hpost.capacity,hpost.position,hpost.written,?_,?_⟩
  · refine ⟨by rw [hpost.returned.pc,ha.x1],hpost.returned.sp.trans ha.sp,hpost.returned.csr.trans ha.csr,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact hpost.returned.x1 |>.trans ha.x1
    · exact hpost.returned.x8 |>.trans ha.x8
    · exact hpost.returned.x9 |>.trans ha.x9
    · exact hpost.returned.x18 |>.trans ha.x18
    · exact hpost.returned.x19 |>.trans ha.x19
    · exact (hhigh 20 (by decide)) |>.trans ha.x20
    · exact (hhigh 21 (by decide)) |>.trans ha.x21
    · exact (hhigh 22 (by decide)) |>.trans ha.x22
    · exact (hhigh 23 (by decide)) |>.trans ha.x23
    · exact (hhigh 24 (by decide)) |>.trans ha.x24
    · exact (hhigh 25 (by decide)) |>.trans ha.x25
    · exact (hhigh 26 (by decide)) |>.trans ha.x26
    · exact (hhigh 27 (by decide)) |>.trans ha.x27
  · intro hn x hx
    exact (hpost.refused hn x (hf x hx)).trans (FormatStrSave.frame ram sp c x hx)
  · intro x hx ho hp
    exact (hpost.frame x (hf x hx) ho hp).trans (FormatStrSave.frame ram sp c x hx)

end E5R.Thermostat.FormatCursor
