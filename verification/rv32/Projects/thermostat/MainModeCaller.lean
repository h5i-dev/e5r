import Projects.thermostat.MainModeWriteInput
import Projects.thermostat.MainApiWriteTransaction
namespace E5R.Thermostat.MainApiWriteCaller
open E5R E5R.Thermostat HttpRequestSpec
theorem of_mode {c ram input s head amount served close}
    (h : MainModeWriteInput.Ready c ram input s head amount served close) :
    Ready 2 0x80fffa58#32 (WireSpec.ascii "/mode") none c ram input s head amount served close := by
  refine ⟨h.pre,h.ret,h.sp,h.fp,h.two,h.one,h.app,h.invariant,h.stack,h.serve,h.replyCapacity,
    h.pointer,h.capacity,h.closeByte,h.closeSpec,?_,by decide +kernel⟩
  rw [h.method];rfl

end E5R.Thermostat.MainApiWriteCaller
