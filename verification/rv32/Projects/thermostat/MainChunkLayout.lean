import Projects.thermostat.Memory
namespace E5R.Thermostat.MainChunkLayout
open E5R E5R.Thermostat

/-- Fixed fields of the actual read-request future. The filled count and
    read/write cursors are separate changing fields. -/
structure At (ram : Word → BitVec 8) (sp : Word) : Prop where
  rx : ramRead ram (sp+3312#32) .w=sp+132#32
  capacity : ramRead ram (sp+3316#32) .w=2048#32
  limits : ramRead ram (sp+3636#32) .w=sp+3280#32
  maxBody : ramRead ram (sp+3284#32) .w=1024#32
  filledPtr : ramRead ram (sp+3640#32) .w=sp+3288#32

theorem preserve {before after sp} (h : At before sp)
    (hf : ∀ off : Nat, 2180≤off → off+4≤3656 →
      ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead before (sp+BitVec.ofNat 32 off) .w) :
    At after sp := by
  exact ⟨(hf 3312 (by decide) (by decide)).trans h.rx,
    (hf 3316 (by decide) (by decide)).trans h.capacity,
    (hf 3636 (by decide) (by decide)).trans h.limits,
    (hf 3284 (by decide) (by decide)).trans h.maxBody,
    (hf 3640 (by decide) (by decide)).trans h.filledPtr⟩

end E5R.Thermostat.MainChunkLayout
