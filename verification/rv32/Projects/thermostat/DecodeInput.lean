import Projects.thermostat.DecodeSave
import Projects.thermostat.Trim
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.DecodeInput
open E5R E5R.Thermostat

/-- Actual Request body slice fields read by this ELF. The parser must later
    establish these checked views; no decoded command is assumed here. -/
structure BodyAt (B : Board) (ram : Word → BitVec 8) (req p : Word) (body : List (BitVec 8)) : Prop where
  object : Memory.Block B req 328
  aligned : req.toNat%4 = 0
  pointer : ramRead ram (req+320#32) .w = p
  length : ramRead ram (req+324#32) .w = BitVec.ofNat 32 body.length
  bytes : Bytes.Span B ram p body

def Separate (req sp : Word) : Prop := ∀ i : Fin 328, ∀ j : Fin 16,
  req+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val

theorem word_preserved (ram : Word → BitVec 8) (sp : Word) (c : Core) (a : Word)
    (hsep : ∀ i : Fin 4, ∀ j : Fin 16, a+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    ramRead (DecodeSave.memory ram sp c) a .w = ramRead ram a .w := by
  apply ramRead_w_congr
  intro i hi;exact DecodeSave.frame ram sp c _ (hsep ⟨i,hi⟩)

theorem body_preserved {B ram req p body} (h : BodyAt B ram req p body) (sp : Word) (c : Core)
    (hsep : Separate req sp)
    (hbsep : ∀ i : Fin body.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    BodyAt B (DecodeSave.memory ram sp c) req p body := by
  have hword (k : Nat) (hk : k+4 ≤ 328) :
      ramRead (DecodeSave.memory ram sp c) (req+BitVec.ofNat 32 k) .w = ramRead ram (req+BitVec.ofNat 32 k) .w := by
    apply word_preserved
    intro i j
    have hi := i.isLt
    rw [BitVec.add_assoc,←BitVec.ofNat_add]
    exact hsep ⟨k+i.val,by omega⟩ j
  exact ⟨h.object,h.aligned,(hword 320 (by decide)).trans h.pointer,
    (hword 324 (by decide)).trans h.length,DecodeSave.preserves_span h.bytes sp c hbsep⟩

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req p : Word) (body : List (BitVec 8))
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32) (hreq : c.get 10 = req)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) (h : BodyAt B ram req p body)
    (hsep : Separate req sp)
    (hbsep : ∀ i : Fin body.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    ∃ d, DetSteps B img 6 ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧ d.pc = 0x80001f7e#32 ∧
      d.get 2 = sp ∧ d.get 11 = p ∧ d.get 12 = BitVec.ofNat 32 body.length ∧
      (∀ r : Reg, r ≠ 2 → r ≠ 11 → r ≠ 12 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,hsteps,apc,asp,aregs,acsr⟩ := DecodeSave.contract B c ram sp hp hsp hm ha
  let r := DecodeSave.memory ram sp c
  have h' : BodyAt B r req p body := body_preserved h sp c hsep hbsep
  let b := a.wr 12 (BitVec.ofNat 32 body.length) 0x80001f7a#32
  let d := b.wr 11 p 0x80001f7e#32
  have a10 : a.get 10 = req := (aregs 10 (by decide)).trans hreq
  have s0 : DetStep B img ⟨a,r⟩ ⟨b,r⟩ := by
    refine detStep_of (by rw [apc];decide) (by rw [apc];exact tr2147491702) fun o => ?_
    rw [exec_load,a10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 81 h.aligned) (Memory.block_access h.object (off := 324) (by decide) (by decide)),h'.length,apc];rfl
  have s1 : DetStep B img ⟨b,r⟩ ⟨d,r⟩ := by
    refine detStep_of (by change (0x80001f7a#32).getLsbD 0 = false;decide) tr2147491706 fun o => ?_
    have b10 : b.get 10 = req := by simp [b,Core.wr_get_ne,a10]
    rw [exec_load,b10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 80 h.aligned) (Memory.block_access h.object (off := 320) (by decide) (by decide)),h'.pointer];rfl
  refine ⟨d,hsteps.trans (.step s0 (.single s1)),rfl,?_,?_,?_,?_,(Core.sameCsr_wr b 11 _ _).trans ((Core.sameCsr_wr a 12 _ _).trans acsr)⟩
  · simpa [d,b,Core.wr_get_ne] using asp
  · simp [d,Core.wr_get]
  · simp [d,b,Core.wr_get_ne,Core.wr_get]
  · intro r h1 h2 h3
    have hh : d.get r = a.get r := by simp [d,b,Core.wr_get_ne,h2,h3]
    exact hh.trans (aregs r h1)

/-- Start at the real function entry, save the caller frame, load the Request
    body view, and complete the actual trim. Only the real save slots change. -/
theorem trim_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req p : Word) (body : List (BitVec 8))
    (hp : c.pc = 0x80001f6e#32) (hsp : c.get 2 = sp+16#32) (hreq : c.get 10 = req)
    (hm : Memory.Block B sp 16) (ha : sp.toNat%4 = 0) (h : BodyAt B ram req p body)
    (hsep : Separate req sp)
    (hbsep : ∀ i : Fin body.length, ∀ j : Fin 16, p+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) :
    ∃ d k, k ≤ 18*body.length+31 ∧ DetSteps B img k ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧
      d.pc = 0x80001fb4#32 ∧ d.get 2 = sp ∧ d.get 10 = req ∧
      Bytes.Span B (DecodeSave.memory ram sp c) (d.get 8) (TrimMath.trim body) ∧
      d.get 9 = BitVec.ofNat 32 (TrimMath.trim body).length ∧ d.sameCsr c := by
  obtain ⟨a,ht,apc,asp,a11,a12,aregs,acsr⟩ := contract B c ram sp req p body hp hsp hreq hm ha h hsep hbsep
  have h' := body_preserved h sp c hsep hbsep
  obtain ⟨d,k,hk,htrim,dpc,d8,d9,dspan,dregs,dcsr⟩ := Trim.contract B a (DecodeSave.memory ram sp c) p body h'.bytes apc a11 a12
  refine ⟨d,6+k,by omega,ht.trans htrim,dpc,?_,?_,dspan,d9,dcsr.trans acsr⟩
  · exact (dregs 2 (by decide)).trans asp
  · exact (dregs 10 (by decide)).trans ((aregs 10 (by decide) (by decide) (by decide)).trans hreq)
end E5R.Thermostat.DecodeInput
