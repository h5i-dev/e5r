import Projects.thermostat.TxnScratch
import Projects.thermostat.Header
import Projects.thermostat.WireEngine
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.TxnInput
open E5R E5R.Thermostat

/-- Raw Request/App/stack layout before the real authentication call. There is
    no authenticated principal, decoded CommandAt or acquired borrow premise. -/
structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) : Prop where
  pc : c.pc = 0x8000052e#32
  sp : c.get 2 = p+80#32
  request : c.get 21 = req
  engine : c.get 23 = eng
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

theorem wire_pre (B : Board) (c b : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first header : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (h : Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hpc : b.pc = 0x80001f6e#32) (hsp : b.get 2 = p+80#32) (h10 : b.get 10 = req) :
    Wire.Pre B b (TxnScratch.memory ram (p+80#32) header admin) (p+64#32) req pathPtr bodyPtr path body first := by
  have ho := TxnScratch.region ram p req 372 header admin h.requestSeparate
  have hb := TxnScratch.region ram p bodyPtr body.length header admin h.bodySeparate
  have hp := TxnScratch.region ram p pathPtr path.length header admin h.pathSeparate
  refine ⟨hpc,?_,h10,Memory.sub_block h.arena (by decide) (by decide),Memory.word_aligned p 16 h.aligned,
    ViewFrame.body h.bodyView (ViewFrame.shrink ho (by decide)) hb,
    ViewFrame.path h.pathView (ViewFrame.shrink ho (by decide)) hp,
    ViewFrame.params h.params ho hp,TxnScratch.decoder_separate h.requestSeparate,
    TxnScratch.decoder_separate h.bodySeparate,TxnScratch.decoder_separate h.pathSeparate⟩
  rw [hsp,BitVec.add_assoc];rfl

theorem decoded_layout (B : Board) (c b : Core) (ram : Word → BitVec 8) (p req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first header : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (h : Pre B c ram p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hsp : b.get 2 = p+80#32) (h23 : b.get 23 = eng) :
    DecodedEngine.Pre B (b.goto 0x800005f4#32) (TxnScratch.memory ram (p+80#32) header admin) p admin s := by
  have ho := TxnScratch.region ram p eng 25 header admin h.appSeparate
  refine ⟨rfl,hsp,h.arena,h.aligned,?_,?_,?_,?_,TxnScratch.actor ram p header admin,?_⟩
  · simpa only [Core.goto_get,h23,BitVec.add_zero] using Memory.sub_block (off := 0) (m := 14) h.app (by decide) (by decide)
  · simpa only [Core.goto_get,h23] using h.appAligned
  · simpa only [Core.goto_get,h23] using TxnScratch.engine_separate h.appSeparate
  · simpa only [Core.goto_get,h23] using ViewFrame.snapshot h.state ho
  · rw [Core.goto_get,h23]
    have hw := ViewFrame.word ho 0 (by decide)
    simpa only [BitVec.add_zero,h.borrow] using hw
end E5R.Thermostat.TxnInput
