import Projects.thermostat.MainServeLayout
import Projects.thermostat.MainHeaderLoopTwo
set_option autoImplicit false
namespace E5R.Thermostat.MainTransactionStable
open E5R E5R.Thermostat

/-- The live transaction envelope after Request construction. The parser's
    temporary slice/Head storage is intentionally absent: it has been reused. -/
structure At (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot) : Prop where
  sp : c.get 2=0x80ffeb90#32
  fp : c.get 8=0x80fff814#32
  uart : c.get 19=0x10000000#32
  one : c.get 22=1#32
  bound : input.length≤2048
  filled : ramRead ram (0x80fff814#32+84#32) .w=BitVec.ofNat 32 input.length
  bytes : Bytes.At ram 0x80ffec14#32 input
  app : AppState.At ram s
  invariant : Spec.Inv s
  stack : Memory.Block UartPlatform.board 0x80ff0000#32 65536
  masked : c.mie_=false
/-- The376-byte Request slot, including three trailing padding bytes, lies in the initialized stack arena. -/
theorem request {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} (h : At c ram input s) :
    Memory.Block UartPlatform.board (0x80ffeb90#32+3312#32) 376 := by
  have block := Memory.sub_block h.stack (off := 63616) (m := 376) (by decide) (by decide)
  simpa only [show 0x80ff0000#32+63616#32=0x80ffeb90#32+3312#32 by decide +kernel] using block

end E5R.Thermostat.MainTransactionStable
