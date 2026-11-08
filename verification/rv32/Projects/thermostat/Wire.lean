import Projects.thermostat.WirePrefix
import Projects.thermostat.CommandBody
import Projects.thermostat.DecodeReturn
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Wire
open E5R E5R.Thermostat

/-- The actual parser-owned Request views and nonaliasing allocation boundary.
    This assumes raw bytes and capture bounds, never a typed command. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8))) : Prop where
  pc : c.pc = 0x80001f6e#32
  stack : c.get 2 = sp+16#32
  request : c.get 10 = req
  stackRam : Memory.Block B sp 16
  aligned : sp.toNat%4 = 0
  bodyView : DecodeInput.BodyAt B ram req bodyPtr body
  pathView : PathDispatch.PathAt B ram req pathPtr path
  params : WireInput.Params B ram req pathPtr path first
  requestSeparate : WireInput.Separate req sp
  bodySeparate : ∀ i : Fin body.length, ∀ j : Fin 16,
    bodyPtr+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val
  pathSeparate : ∀ i : Fin path.length, ∀ j : Fin 16,
    pathPtr+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val

structure Post (c d : Core) (path body : List (BitVec 8)) (first : Option (List (BitVec 8))) : Prop where
  pc : d.pc = c.get 1 &&& ~~~1
  result : WireSpec.ResultWord (d.get 10) (WireSpec.decode path body first)
  sp : d.get 2 = c.get 2
  ra : d.get 1 = c.get 1
  s0 : d.get 8 = c.get 8
  s1 : d.get 9 = c.get 9
  frame : ∀ r : Reg, r.val = 3 ∨ r.val = 4 ∨ r.val = 6 ∨ r.val = 7 ∨ 18 ≤ r.val → d.get r = c.get r
  csr : d.sameCsr c

/-- Complete actual Wire::decode_command: save frame, derive trimmed bytes,
    select raw path, parse numbers/captures, construct exact enum/error and RET.
    Only the actual three saved stack words are written. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (h : Pre B c ram sp req pathPtr bodyPtr path body first) :
    ∃ d n, n ≤ 18*body.length+303 ∧
      DetSteps B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧ Post c d path body first := by
  obtain ⟨a,n,hn,ht,apc,asp,areq,abody,a9,aframe,acsr⟩ := WirePrefix.contract B c ram sp req bodyPtr body
    h.pc h.stack h.request h.stackRam h.aligned h.bodyView h.requestSeparate h.bodySeparate
  let r := DecodeSave.memory ram sp c
  have pathView := WireInput.path_saved h.pathView sp c h.requestSeparate h.pathSeparate
  have params := WireInput.params_saved h.params sp c h.requestSeparate h.pathSeparate
  obtain ⟨b,k,hk,tb,bpc,bval,bframe,bcsr⟩ := CommandBody.contract B a r req pathPtr (a.get 8)
    path (TrimMath.trim body) first pathView params.as_pre abody apc areq rfl a9
  have bsp : b.get 2 = sp := (bframe 2 (by decide) (by decide) (by decide)).trans asp
  obtain ⟨d,td,dpc,dsp,dra,ds0,ds1,dframe,dcsr⟩ := DecodeReturn.contract B b r sp bpc bsp h.stackRam h.aligned
  obtain ⟨savedRA,saved0,saved1⟩ := DecodeSave.saved ram sp c
  refine ⟨d,n+k+5,by omega,(ht.trans tb).trans td,?_,?_,?_,?_,?_,?_,?_,(dcsr.trans bcsr).trans acsr⟩
  · exact dpc.trans (congrArg (fun w : Word => w &&& ~~~1) savedRA)
  · have hv : d.get 10 = b.get 10 := dframe 10 (by decide) (by decide) (by decide) (by decide)
    rw [hv,←CommandSpec.as_decode];exact bval
  · exact dsp.trans h.stack.symm
  · exact dra.trans savedRA
  · exact ds0.trans saved0
  · exact ds1.trans saved1
  · intro r hr
    have hr8 : r.val < 8 ∨ 17 < r.val := by omega
    have hr10 : r.val < 10 ∨ 17 < r.val := by omega
    have ne (k : Reg) (hk : k.val = 1 ∨ k.val = 2 ∨ k.val = 5 ∨ k.val = 8 ∨ k.val = 9) : r ≠ k := by
      intro he;have hv := congrArg Fin.val he;omega
    exact (dframe r (ne 1 (by decide)) (ne 2 (by decide)) (ne 8 (by decide)) (ne 9 (by decide))).trans
      ((bframe r (ne 1 (by decide)) (ne 5 (by decide)) hr10).trans (aframe r (ne 2 (by decide)) hr8))

theorem closed_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp req pathPtr bodyPtr : Word)
    (path body : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (h : Pre B c ram sp req pathPtr bodyPtr path body first) (hm : c.mie_ = false) :
    ∃ d n, n ≤ 18*body.length+303 ∧
      Trace.Closed B img n ⟨c,ram⟩ ⟨d,DecodeSave.memory ram sp c⟩ ∧ Post c d path body first := by
  obtain ⟨d,n,hn,ht,hpost⟩ := contract B c ram sp req pathPtr bodyPtr path body first h
  exact ⟨d,n,hn,Interrupt.close ht hm,hpost⟩
end E5R.Thermostat.Wire
