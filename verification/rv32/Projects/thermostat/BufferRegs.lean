import Theories.Logic
namespace E5R.Thermostat.BufferRegs
open E5R

/-- The write handler keeps Future/Response and output capacity/pointer live across calls. -/
structure Frame (before after : Core) : Prop where
  capacity : after.get 18 = before.get 18
  pointer : after.get 19 = before.get 19
  future : after.get 8 = before.get 8
  response : after.get 9 = before.get 9
  completion : after.get 22 = before.get 22

theorem trans {a b c} (h : Frame a b) (g : Frame b c) : Frame a c :=
  ⟨g.capacity.trans h.capacity,g.pointer.trans h.pointer,g.future.trans h.future,g.response.trans h.response,g.completion.trans h.completion⟩
end E5R.Thermostat.BufferRegs
