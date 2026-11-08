import Projects.thermostat.MainTempWriteInput
import Projects.thermostat.MainSetpointWriteInput
import Projects.thermostat.MainWriteReturnJoin
set_option autoImplicit false
namespace E5R.Thermostat.MainApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev fp : Word := 0x80fff814#32

/-- Shared G3/G5 interface for the four real call/return sites. Every field is
    derived by a caller proof; address bounds are used only for frame separation. -/
structure Ready (kind : Fin 4) (future : Word) (path : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot)
    (head : Head) (amount served : Nat) (close : Bool) : Prop where
  pre : WriteInput.Pre B c ram 0x80ffeae0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
    (MainRequestSpans.raw input head amount) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s
  ret : c.get 1=MainWriteReturnJoin.entry kind
  sp : c.get 2=0x80ffeb90#32
  fp : c.get 8=MainApiWriteCaller.fp
  two : c.get 18=2#32
  one : c.get 22=1#32
  app : AppState.At ram s
  invariant : Spec.Inv s
  stack : Memory.Block B 0x80ff0000#32 65536
  serve : MainServeLayout.At ram served
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  pointer : ramRead ram (future+12#32) .w=0x80fff4d4#32
  capacity : ramRead ram (future+16#32) .w=832#32
  closeByte : ram 0x80fff878#32=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
  notHead : MainMethod.head (ram 0x80fff9f4#32)=false
  futureBounds : 0x80fffa2c≤future.toNat ∧ future.toNat≤0x80fffab0

theorem of_temp {c ram input s head amount served close}
    (h : MainTempWriteInput.Ready c ram input s head amount served close) :
    Ready 1 0x80fffa84#32 (WireSpec.ascii "/temp") none c ram input s head amount served close := by
  refine ⟨h.pre,h.ret,h.sp,h.fp,h.two,h.one,h.app,h.invariant,h.stack,h.serve,h.replyCapacity,
    h.pointer,h.capacity,h.closeByte,h.closeSpec,?_,by decide +kernel⟩
  rw [h.method];rfl

theorem of_setpoint {c ram input s head amount served close}
    (h : MainSetpointWriteInput.Ready c ram input s head amount served close) :
    Ready 0 0x80fffab0#32 (WireSpec.ascii "/setpoint") none c ram input s head amount served close := by
  refine ⟨h.pre,h.ret,h.sp,h.fp,h.two,h.one,h.app,h.invariant,h.stack,h.serve,h.replyCapacity,
    h.pointer,h.capacity,h.closeByte,h.closeSpec,?_,by decide +kernel⟩
  rw [h.method];rfl
end E5R.Thermostat.MainApiWriteCaller
