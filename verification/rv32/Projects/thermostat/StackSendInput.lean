import Projects.thermostat.SendInput
import Projects.thermostat.StackAccess
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackSendInput
open E5R E5R.Thermostat SendInput
abbrev B := StackBoard.board
structure Pre (c : Core) (ram : Word → BitVec 8) (frame obj res tx io ctptr : Word)
    (raw status : Nat) (ct payload : List (BitVec 8)) (close head : Bool) : Prop where
  pc : c.pc=0x8000030e#32
  sp : c.get 2=frame+144#32
  resultArg : c.get 10=res
  objectArg : c.get 11=obj
  stack : Memory.Block B frame 144
  stackAligned : frame.toNat%4=0
  object : Memory.Block B obj 89
  objectAligned : obj.toNat%4=0
  result : Memory.Block B res 8
  resultAligned : res.toNat%4=0
  txBlock : Memory.Block B tx 1024
  txStrict : tx.toNat+1024<2^32
  objectStack : WordRegions.Disjoint obj 89 frame 144
  txStack : WordRegions.Disjoint tx 1024 frame 144
  objectTx : WordRegions.Disjoint obj 89 tx 1024
  resultStack : WordRegions.Disjoint res 8 frame 144
  resultObject : WordRegions.Disjoint res 8 obj 89
  resultTx : WordRegions.Disjoint res 8 tx 1024
  ctStack : WordRegions.Disjoint ctptr ct.length frame 144
  ctObject : WordRegions.Disjoint ctptr ct.length obj 89
  ctTx : WordRegions.Disjoint ctptr ct.length tx 1024
  source : ReadBytes.Span B img ram ctptr ct
  payloadBytes : ReadBytes.Span B img ram (tx+192#32) payload
  rawBound : raw<2^32
  statusLo : 200≤status
  statusHi : status≤599
  ctBound : ct.length≤16
  field : ResponseHeadSpec.Field ct
  clipped : payload.length=min 832 raw
  fresh : ram (obj+45#32)=0#8
  capacity : ramRead ram (obj+12#32) .w=1024#32
  ioWord : ramRead ram (obj+24#32) .w=io
  txWord : ramRead ram (obj+8#32) .w=tx
  ctWord : ramRead ram (obj+28#32) .w=ctptr
  ctLength : ramRead ram (obj+32#32) .w=BitVec.ofNat 32 ct.length
  bodyLength : ramRead ram (obj+36#32) .w=BitVec.ofNat 32 raw
  statusWord : extend .h false (ramRead ram (obj+40#32) .h)=BitVec.ofNat 32 status
  closeWord : extend .b false (ramRead ram (obj+42#32) .b)=ResponseHeadBodyMath.boolWord close
  headWord : extend .b false (ramRead ram (obj+46#32) .b)=ResponseHeadBodyMath.boolWord head

theorem payload_bound {c ram frame obj res tx io ctptr raw status ct payload close head}
    (h : Pre c ram frame obj res tx io ctptr raw status ct payload close head) : payload.length≤832 := by
  rw [h.clipped];exact Nat.min_le_left _ _
end E5R.Thermostat.StackSendInput
