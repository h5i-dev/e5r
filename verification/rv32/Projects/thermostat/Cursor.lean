import Projects.thermostat.CursorWritten
import Projects.thermostat.CursorGuard
import Projects.thermostat.CursorExit
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Cursor
open E5R E5R.Thermostat

/-- Independent bounded byte-append outcome. -/
def nextPosition (cap pos len : Nat) : Nat := if pos+len ≤ cap then pos+len else pos
def resultWord (cap pos len : Nat) : Word := if pos+len ≤ cap then 0#32 else 1#32

structure Post (B : Board) (c d : Core) (before after : Word → BitVec 8) (sp obj dst : Word)
    (cap pos : Nat) (xs : List (BitVec 8)) : Prop where
  returned : CursorExit.Returned c d
  result : d.get 10 = resultWord cap pos xs.length
  pointer : ramRead after obj .w = dst
  capacity : ramRead after (obj+4#32) .w = BitVec.ofNat 32 cap
  position : ramRead after (obj+8#32) .w = BitVec.ofNat 32 (nextPosition cap pos xs.length)
  written : pos+xs.length ≤ cap → Bytes.Span B after (dst+BitVec.ofNat 32 pos) xs
  refused : ¬pos+xs.length ≤ cap → ∀ x, (∀ i : Fin 32, x ≠ sp+BitVec.ofNat 32 i.val) → after x = before x
  frame : ∀ x, (∀ i : Fin 32, x ≠ sp+BitVec.ofNat 32 i.val) →
    (∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) → after x = before x

/-- Complete actual Cursor::write_str for the <16-byte pieces used by JSON,
    including capacity refusal, panic exclusion, memcpy, position and realRET. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj src dst : Word) (cap pos : Nat) (xs : List (BitVec 8))
    (h : CursorInput.Pre B c ram sp obj src dst cap pos xs) :
    ∃ d n r, n ≤ 6*xs.length+41 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post B c d ram r sp obj dst cap pos xs := by
  let r0 := CursorSave.memory ram sp c
  have hl := CursorInput.saved_layout h
  obtain ⟨a,ta,apc,asp,aframe,acsr⟩ := CursorSave.contract B c ram sp h.pc h.spReg h.stack h.stackAligned
  have a10 : a.get 10 = obj := (aframe 10 (by decide)).trans h.objectReg
  have a11 : a.get 11 = src := (aframe 11 (by decide)).trans h.sourceReg
  have a12 : a.get 12 = BitVec.ofNat 32 xs.length := (aframe 12 (by decide)).trans h.lengthReg
  obtain ⟨b,tb,bpc,b8,b12,b14,b18,bframe,bcsr⟩ := CursorGuard.contract B a r0 obj cap pos xs.length apc a10 a12
    h.object h.objectAligned hl.capacityWord hl.positionWord h.capacity h.position h.source.length
  have bsp : b.get 2 = sp := (bframe 2 (by decide) (by decide) (by decide) (by decide)).trans asp
  have b10 : b.get 10 = obj := (bframe 10 (by decide) (by decide) (by decide) (by decide)).trans a10
  have b11 : b.get 11 = src := (bframe 11 (by decide) (by decide) (by decide) (by decide)).trans a11
  have bcsr' : b.sameCsr c := bcsr.trans acsr
  by_cases hf : xs.length ≤ cap-pos
  · have hspec : pos+xs.length ≤ cap := by have := h.position;omega
    have bpc' : b.pc = 0x800022ba#32 := by simpa only [ite_eq_left hf] using bpc
    obtain ⟨u,k,hk,tu,upc,usp,u8,u18,ucsr⟩ := CursorWritten.contract B b r0 sp obj src dst cap pos xs hl bpc' bsp b10 b11 b8 b12 b14 hf
    let r1 := CursorMemory.memory r0 obj dst pos xs
    obtain ⟨d,td,hret,d10⟩ := CursorExit.contract B c u ram r1 sp (cap-pos) xs.length upc usp h.spReg
      (u18.trans b18) u8 (by have := h.capacity;omega) h.source.length h.stack h.stackAligned (ucsr.trans bcsr') (CursorMemory.stack hl hf)
    refine ⟨d,6+5+k+8,r1,by omega,((ta.trans tb).trans tu).trans td,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact hret
    · simpa only [CursorFinish.flagWord,ite_eq_left hf,resultWord,ite_eq_left hspec] using d10
    · exact CursorMemory.pointer hl hf
    · exact CursorMemory.capacity hl hf
    · simpa only [nextPosition,ite_eq_left hspec] using CursorMemory.position r0 obj dst pos xs
    · intro _;exact CursorMemory.copied hl hf
    · intro hn;exact False.elim (hn hspec)
    · intro x hst hout hobj
      exact (CursorMemory.frame r0 obj dst x pos xs hout hobj).trans (CursorSave.frame ram sp c x hst)
  · have hspec : ¬pos+xs.length ≤ cap := by have := h.position;omega
    have bpc' : b.pc = 0x800022dc#32 := by simpa only [ite_eq_right hf] using bpc
    obtain ⟨d,td,hret,d10⟩ := CursorExit.contract B c b ram r0 sp (cap-pos) xs.length bpc' bsp h.spReg
      b18 b8 (by have := h.capacity;omega) h.source.length h.stack h.stackAligned bcsr' (fun _ => rfl)
    refine ⟨d,19,r0,by omega,(ta.trans tb).trans td,?_,?_,hl.pointerWord,hl.capacityWord,?_,?_,?_,?_⟩
    · exact hret
    · simpa only [CursorFinish.flagWord,ite_eq_right hf,resultWord,ite_eq_right hspec] using d10
    · simpa only [nextPosition,ite_eq_right hspec] using hl.positionWord
    · intro hfit;exact False.elim (hspec hfit)
    · intro _ x hst;exact CursorSave.frame ram sp c x hst
    · intro x hst _ _;exact CursorSave.frame ram sp c x hst
end E5R.Thermostat.Cursor
