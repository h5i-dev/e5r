import Projects.thermostat.WriteStart
import Projects.thermostat.HeaderFrame
import Projects.thermostat.TxnInput
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteInput
open E5R E5R.Thermostat

/-- Core-independent Request/App allocation and byte layout. -/
structure Layout (B : Board) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) : Prop where
  arena : Memory.Block B p 128
  aligned : p.toNat%4 = 0
  app : Memory.Block B eng 25
  appAligned : eng.toNat%4 = 0
  appSeparate : TxnScratch.Separate eng 25 p
  state : Encoding.SnapshotAt ram (eng+4#32) s
  borrow : ramRead ram eng .w = 0#32
  principal : ram (eng+24#32) = Encoding.boolByte admin
  keyPointer : ramRead ram (eng+16#32) .w = 0x80005b7c#32
  keyLength : ramRead ram (eng+20#32) .w = 7#32
  headers : Header.Pre B ram req rawPtr raw entries
  bodyView : DecodeInput.BodyAt B ram req bodyPtr body
  pathView : PathDispatch.PathAt B ram req pathPtr path
  params : WireInput.Params B ram req pathPtr path first
  requestSeparate : TxnScratch.Separate req 372 p
  bodySeparate : TxnScratch.Separate bodyPtr body.length p
  pathSeparate : TxnScratch.Separate pathPtr path.length p
  rawSeparate : TxnScratch.Separate rawPtr raw.length p

theorem of_txn {B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s}
    (h : TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s) :
    Layout B ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s := by
  exact ⟨h.arena,h.aligned,h.app,h.appAligned,h.appSeparate,h.state,h.borrow,h.principal,
    h.keyPointer,h.keyLength,h.headers,h.bodyView,h.pathView,h.params,h.requestSeparate,h.bodySeparate,h.pathSeparate,h.rawSeparate⟩

theorem to_txn {B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s}
    (h : Layout B ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hp : c.pc = 0x8000052e#32) (hsp : c.get 2 = p+80#32) (h21 : c.get 21 = req) (h23 : c.get 23 = eng) :
    TxnInput.Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s := by
  exact ⟨hp,hsp,h21,h23,h.arena,h.aligned,h.app,h.appAligned,h.appSeparate,h.state,h.borrow,h.principal,
    h.keyPointer,h.keyLength,h.headers,h.bodyView,h.pathView,h.params,h.requestSeparate,h.bodySeparate,h.pathSeparate,h.rawSeparate⟩

theorem layout_frame {B before after p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s}
    (h : Layout B before p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (he : ViewFrame.Region before after eng 25) (hr : ViewFrame.Region before after req 372)
    (hraw : ViewFrame.Region before after rawPtr raw.length)
    (hpath : ViewFrame.Region before after pathPtr path.length) (hbody : ViewFrame.Region before after bodyPtr body.length) :
    Layout B after p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s := by
  refine ⟨h.arena,h.aligned,h.app,h.appAligned,h.appSeparate,ViewFrame.snapshot h.state he,?_,?_,
    (ViewFrame.word he 16 (by decide)).trans h.keyPointer,(ViewFrame.word he 20 (by decide)).trans h.keyLength,
    HeaderFrame.header h.headers hr hraw,ViewFrame.body h.bodyView (ViewFrame.shrink hr (by decide)) hbody,
    ViewFrame.path h.pathView (ViewFrame.shrink hr (by decide)) hpath,ViewFrame.params h.params hr hpath,
    h.requestSeparate,h.bodySeparate,h.pathSeparate,h.rawSeparate⟩
  · have hw := ViewFrame.word he 0 (by decide)
    simpa only [BitVec.add_zero] using hw.trans (by simpa only [BitVec.add_zero] using h.borrow)
  · exact (he ⟨24,by decide⟩).trans h.principal

def Avoid (obj : Word) (n : Nat) (sp f : Word) : Prop :=
  (∀ i : Fin n, ∀ j : Fin 96, obj+BitVec.ofNat 32 i.val ≠ sp+BitVec.ofNat 32 j.val) ∧
  (∀ i : Fin n, ∀ j : Fin 41, obj+BitVec.ofNat 32 i.val ≠ f+BitVec.ofNat 32 j.val)

theorem region {obj n sp f} (h : Avoid obj n sp f) (ram : Word → BitVec 8) (c : Core) :
    ViewFrame.Region ram (WriteStart.memory ram sp f c) obj n := by
  intro i
  apply WriteStart.frame
  · exact h.1 i
  · intro j;exact h.2 i ⟨20+j.val,by have := j.isLt;omega⟩

/-- Initial actual call arguments and disjoint allocations, before stack saves. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p f response req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) : Prop where
  pc : c.pc = 0x800004c6#32
  sp : c.get 2 = (p+80#32)+96#32
  future : c.get 11 = f
  response : c.get 10 = response
  stack : Memory.Block B (p+80#32) 96
  futureBlock : Memory.Block B f 41
  futureAligned : f.toNat%4 = 0
  futureSeparate : WriteStart.Separate f (p+80#32)
  fresh : ram (f+40#32) = 0#8
  request : ramRead ram (f+4#32) .w = req
  engine : ramRead ram (f+8#32) .w = eng
  layout : Layout B ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s
  appAvoid : Avoid eng 25 (p+80#32) f
  requestAvoid : Avoid req 372 (p+80#32) f
  rawAvoid : Avoid rawPtr raw.length (p+80#32) f
  pathAvoid : Avoid pathPtr path.length (p+80#32) f
  bodyAvoid : Avoid bodyPtr body.length (p+80#32) f

theorem establishes {B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s}
    (h : Pre B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s) :
    ∃ d, DetSteps B img 31 ⟨c,ram⟩ ⟨d,WriteStart.memory ram (p+80#32) f c⟩ ∧
      TxnInput.Pre B d (WriteStart.memory ram (p+80#32) f c) p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s ∧
      d.get 8 = f ∧ d.get 9 = response ∧
      d.get 19 = ramRead ram (f+12#32) .w ∧ d.get 18 = ramRead ram (f+16#32) .w ∧ d.sameCsr c := by
  obtain ⟨d,td,dpc,dsp,d8,d9,d21,d23,d19,d18,dcsr⟩ := WriteStart.contract B c ram (p+80#32) f response
    h.pc h.sp h.future h.response h.stack (Memory.word_aligned p 20 h.layout.aligned)
    h.futureBlock h.futureAligned h.futureSeparate h.fresh
  have hl := layout_frame h.layout (region h.appAvoid ram c) (region h.requestAvoid ram c)
    (region h.rawAvoid ram c) (region h.pathAvoid ram c) (region h.bodyAvoid ram c)
  exact ⟨d,td,to_txn hl dpc dsp (d21.trans h.request) (d23.trans h.engine),d8,d9,d19,d18,dcsr⟩
end E5R.Thermostat.WriteInput
