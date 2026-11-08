import Projects.thermostat.BufferRegs
namespace E5R.Thermostat.BufferRegs
open E5R

/-- Authentication sets the completion constant and preserves the four live
    object/output registers. This does not claim x22 was unchanged. -/
structure Ready (before after : Core) : Prop where
  capacity : after.get 18 = before.get 18
  pointer : after.get 19 = before.get 19
  future : after.get 8 = before.get 8
  response : after.get 9 = before.get 9
  completion : after.get 22 = 1#32

theorem Ready.trans {a b c} (h : Ready a b) (g : Frame b c) : Ready a c :=
  ⟨g.capacity.trans h.capacity,g.pointer.trans h.pointer,g.future.trans h.future,
    g.response.trans h.response,g.completion.trans h.completion⟩
end E5R.Thermostat.BufferRegs
