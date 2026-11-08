import Projects.thermostat.FormatInput
import Projects.thermostat.CursorFull
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.FormatCursor
open E5R E5R.Thermostat

structure Returned (c d : Core) : Prop where
  pc : d.pc = c.get 1 &&& ~~~1
  sp : d.get 2 = c.get 2
  csr : d.sameCsr c
  x1 : d.get 1 = c.get 1
  x8 : d.get 8 = c.get 8
  x9 : d.get 9 = c.get 9
  x18 : d.get 18 = c.get 18
  x19 : d.get 19 = c.get 19
  x20 : d.get 20 = c.get 20
  x21 : d.get 21 = c.get 21
  x22 : d.get 22 = c.get 22
  x23 : d.get 23 = c.get 23
  x24 : d.get 24 = c.get 24
  x25 : d.get 25 = c.get 25
  x26 : d.get 26 = c.get 26
  x27 : d.get 27 = c.get 27

structure Post (B : Board) (c d : Core) (before after : Word → BitVec 8) (sp obj dst : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  returned : Returned c d
  result : d.get 10 = Cursor.resultWord cap pos xs.length
  pointer : ramRead after obj .w = dst
  capacity : ramRead after (obj+4#32) .w = BitVec.ofNat 32 cap
  position : ramRead after (obj+8#32) .w = BitVec.ofNat 32 (Cursor.nextPosition cap pos xs.length)
  written : pos+xs.length ≤ cap → Bytes.Span B after (dst+BitVec.ofNat 32 pos) xs
  refused : ¬pos+xs.length ≤ cap → ∀ x, (∀ i : Fin 64, x ≠ sp+BitVec.ofNat 32 i.val) → after x = before x
  frame : ∀ x, (∀ i : Fin 64, x ≠ sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) → after x = before x

/-- Actual default Formatter::write_str and actual Cursor/memcpy through real
    return, byte append/refusal and all thirteen callee-saved registers. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp fmt obj src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) (h : FormatInput.Pre B c ram sp fmt obj src dst flags cap pos xs)
    (hrom : B.inRam 0x80005c10#32 4 = false) :
    ∃ d n r, n ≤ 6*xs.length+78 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post B c d ram r sp obj dst cap pos xs := by
  obtain ⟨a,ta,ha,hcursor⟩ := FormatInput.establishes h hrom
  obtain ⟨d,n,r,hn,td,hpost,hhigh⟩ := Cursor.contract_full B a (FormatStrSave.memory ram sp c) (sp+32#32) obj src dst cap pos xs hcursor
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
