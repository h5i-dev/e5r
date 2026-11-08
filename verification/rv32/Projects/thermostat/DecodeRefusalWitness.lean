import Projects.thermostat.WriteDecodeRefusal
import Projects.thermostat.ByteUpdate
import Projects.thermostat.HeaderTableFrame
import Projects.thermostat.WriteWitness
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.DecodeRefusalWitness
open E5R E5R.Thermostat

def raw := RequestWitness.raw.set 76 112#8
def body := RequestWitness.body.set 3 112#8
def ram := ramPut WriteWitness.ram 0x8004004c#32 112#8

theorem region (obj : Word) (n : Nat) (hs : WordRegions.Disjoint obj n 0x8004004c#32 1) :
    ViewFrame.Region WriteWitness.ram ram obj n := by
  intro i
  have hh : obj+BitVec.ofNat 32 i.val ≠ 0x8004004c#32 := by
    simpa only [BitVec.add_zero] using hs i ⟨0,by decide⟩
  exact ramPut_ne _ hh

theorem raw_span : Bytes.Span UartPlatform.board ram 0x80040000#32 raw := by
  have hs := ViewFrame.span RequestWitness.raw_span (WriteWitness.region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))))
  exact ByteUpdate.span hs 76 112#8 (by decide)

theorem layout : WriteInput.Layout UartPlatform.board ram 0x80050000#32 0x80020000#32 0x80010000#32
    0x80040000#32 0x80040005#32 0x80040049#32 raw RequestWitness.path body
    RequestWitness.entries none true Spec.initial := by
  have h := WriteWitness.pre.layout
  have he := region 0x80010000#32 25 (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hr := region 0x80020000#32 372 (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hp := region 0x80040005#32 RequestWitness.path.length (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hb : Bytes.Span UartPlatform.board ram 0x80040049#32 body := Bytes.subspan raw_span 73 77 (by decide)
  refine ⟨h.arena,h.aligned,h.app,h.appAligned,h.appSeparate,ViewFrame.snapshot h.state he,?_,?_,
    (ViewFrame.word he 16 (by decide)).trans h.keyPointer,(ViewFrame.word he 20 (by decide)).trans h.keyLength,
    HeaderTableFrame.replace h.headers hr raw_span (by decide),
    ⟨h.bodyView.object,h.bodyView.aligned,(ViewFrame.word hr 320 (by decide)).trans h.bodyView.pointer,
      (ViewFrame.word hr 324 (by decide)).trans h.bodyView.length,hb⟩,
    ViewFrame.path h.pathView (ViewFrame.shrink hr (by decide)) hp,ViewFrame.params h.params hr hp,
    h.requestSeparate,h.bodySeparate,h.pathSeparate,?_⟩
  · have hh := ViewFrame.word he 0 (by decide)
    simpa only [BitVec.add_zero] using hh.trans (by simpa only [BitVec.add_zero] using h.borrow)
  · exact (he ⟨24,by decide⟩).trans h.principal
  · simpa only [raw,List.length_set] using h.rawSeparate

theorem pre : WriteInput.Pre UartPlatform.board WriteWitness.core ram 0x80050000#32 0x80030000#32 0x80060000#32
    0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x80040049#32
    raw RequestWitness.path body RequestWitness.entries none true Spec.initial := by
  have h := WriteWitness.pre
  have hf := region 0x80030000#32 41 (WordRegions.before _ _ _ _ (by decide) (by decide))
  refine ⟨h.pc,h.sp,h.future,h.response,h.stack,h.futureBlock,h.futureAligned,h.futureSeparate,
    (hf ⟨40,by decide⟩).trans h.fresh,(ViewFrame.word hf 4 (by decide)).trans h.request,
    (ViewFrame.word hf 8 (by decide)).trans h.engine,layout,h.appAvoid,h.requestAvoid,?_,h.pathAvoid,h.bodyAvoid⟩
  simpa only [raw,List.length_set] using h.rawAvoid

/-- A one-byte invalid command body in complete authenticated HTTP bytes returns400 through the
    real handler RET, preserves all nonzero caller saves and the initial state. -/
theorem rejects_bad_body :
    ∃ d n r, n ≤ 1010 ∧ Trace.Closed UartPlatform.board img n ⟨WriteWitness.core,ram⟩ ⟨d,r⟩ ∧
      WriteRefusal.Returned WriteWitness.core d ∧ d.pc = 0x80000abc#32 ∧ d.get 2 = 0x800500b0#32 ∧
      StatusMemory.At r 0x80060000#32 400#32 ∧ Encoding.SnapshotAt r (0x80010000#32+4#32) Spec.initial ∧
      ramRead r 0x80010000#32 .w = 0#32 ∧ Engine.InvariantAt r 0x80010000#32 := by
  obtain ⟨d,n,r,hn,ht,hret,hr,hs,hb,hi,_,_⟩ := WriteDecodeRefusal.contract_inv WriteWitness.core ram
    0x80050000#32 0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32
    0x80040000#32 0x80040005#32 0x80040049#32 raw RequestWitness.path body
    RequestWitness.entries none true Spec.initial 400 pre (by decide +kernel) (by decide +kernel) Spec.initial_inv
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    (by decide) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  exact ⟨d,n,r,hn,Interrupt.close ht rfl,hret,hret.pc,hret.sp,hr,hs,hb,hi⟩
end E5R.Thermostat.DecodeRefusalWitness
