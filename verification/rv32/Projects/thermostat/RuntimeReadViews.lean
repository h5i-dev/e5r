import Projects.thermostat.MainReadDecoded
namespace E5R.Thermostat.RuntimeReadViews
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainReadRouteInput.B
abbrev sp := MainReadRouteInput.sp
abbrev fp := MainReadRouteInput.fp
abbrev rx := MainReadRouteInput.rx
abbrev req := MainReadRouteInput.req
abbrev decodeSp := MainReadRouteInput.decodeSp
structure RouteReady (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (head : Head) (amount served : Nat) (close isHead : Bool) : Prop where
  wire : Wire.Pre B c ram decodeSp req (rx+BitVec.ofNat 32 head.target.1) (rx+BitVec.ofNat 32 head.len)
    (WireSpec.ascii "/state") (MainRequestSpans.body input head amount) none
  stable : MainTransactionStable.At c ram input s
  serve : MainServeLayout.At ram served
  closeByte : ram (sp+3304#32)=Encoding.boolByte close
  ret : c.get 1=0x800019e8#32
  engine : c.get 9=0x80ffebbc#32
  capacity : c.get 20=832#32
  payload : c.get 24=0x80fff4d4#32
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  method : ram 0x80fff9f4#32=Encoding.boolByte isHead
  actor : ram 0x80fffe68#32=0#8

structure DecodedReady (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) (served : Nat) (close isHead : Bool) : Prop where
  acquiredInput : ReadAcquire.Pre B c ram s
  stable : MainTransactionStable.At c ram input s
  serve : MainServeLayout.At ram served
  closeByte : ram 0x80fff878#32=Encoding.boolByte close
  capacity : c.get 20=832#32
  payload : c.get 24=0x80fff4d4#32
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  method : ram 0x80fff9f4#32=Encoding.boolByte isHead

end E5R.Thermostat.RuntimeReadViews
