import Projects.thermostat.RuntimeApiWriteCaller
import Projects.thermostat.StackBoard
set_option autoImplicit false
namespace E5R.Thermostat.StackRuntimeApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec RuntimeApiWriteCaller
structure Ready (kind : Fin 4) (future : Word) (path : List (BitVec 8)) (first : Option (List (BitVec 8)))
    (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot)
    (head : Head) (amount rawUsed served : Nat) (close : Bool) : Prop where
  pre : WriteInput.Pre StackBoard.board c ram 0x80ffeae0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
    (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s
  ret : c.get 1=MainWriteReturnJoin.entry kind
  sp : c.get 2=0x80ffeb90#32
  fp : c.get 8=RuntimeApiWriteCaller.fp
  two : c.get 18=2#32
  one : c.get 22=1#32
  app : AppState.At ram s
  invariant : Spec.Inv s
  stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536
  serve : MainServeLayout.At ram served
  replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32
  pointer : ramRead ram (future+12#32) .w=0x80fff4d4#32
  capacity : ramRead ram (future+16#32) .w=832#32
  closeByte : ram 0x80fff878#32=Encoding.boolByte close
  closeSpec : close=MainCloseSpec.mustClose head.minor served (RuntimeRequestSpans.raw input rawUsed) (MainRequestInputs.entries head)
  notHead : MainMethod.head (ram 0x80fff9f4#32)=false
  futureBounds : 0x80fffa2c≤future.toNat ∧ future.toNat≤0x80fffab0

end E5R.Thermostat.StackRuntimeApiWriteCaller
