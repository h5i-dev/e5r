import Projects.thermostat.FutureSetup
import Projects.thermostat.ViewFrame
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainServeLayout
open E5R E5R.Thermostat
abbrev fp := 0x80fff814#32

def slots : List Nat := [0,4,8,44,48,52,56,60,64,68,72,88]

/-- Static serve configuration and live request counter in the real future.
    Filled84 and used92 are deliberately separate changing fields. -/
structure At (ram : Word → BitVec 8) (served : Nat) : Prop where
  headMax : ramRead ram (fp+0#32) .w=1024#32
  bodyMax : ramRead ram (fp+4#32) .w=1024#32
  requests : ramRead ram (fp+8#32) .w=100#32
  config : ramRead ram (fp+44#32) .w=fp
  router : ramRead ram (fp+48#32) .w=0x80ffebd8#32
  app : ramRead ram (fp+52#32) .w=0x80ffebbc#32
  rx : ramRead ram (fp+56#32) .w=0x80ffec14#32
  capacity : ramRead ram (fp+60#32) .w=2048#32
  tx : ramRead ram (fp+64#32) .w=0x80fff414#32
  txCapacity : ramRead ram (fp+68#32) .w=1024#32
  uart : ramRead ram (fp+72#32) .w=0x80ffffc7#32
  servedWord : ramRead ram (fp+88#32) .w=BitVec.ofNat 32 served

def Frame (before after : Word → BitVec 8) : Prop := ∀ off∈slots,
  ramRead after (fp+BitVec.ofNat 32 off) .w=ramRead before (fp+BitVec.ofNat 32 off) .w

theorem refl (ram : Word → BitVec 8) : Frame ram ram := fun _ _ => rfl

theorem trans {a b c : Word → BitVec 8} (ab : Frame a b) (bc : Frame b c) : Frame a c := fun off safe => (bc off safe).trans (ab off safe)

theorem preserve {before after count} (frame : Frame before after) (h : At before count) : At after count :=
  ⟨(frame 0 (by decide)).trans h.headMax,(frame 4 (by decide)).trans h.bodyMax,(frame 8 (by decide)).trans h.requests,
    (frame 44 (by decide)).trans h.config,(frame 48 (by decide)).trans h.router,(frame 52 (by decide)).trans h.app,
    (frame 56 (by decide)).trans h.rx,(frame 60 (by decide)).trans h.capacity,(frame 64 (by decide)).trans h.tx,
    (frame 68 (by decide)).trans h.txCapacity,(frame 72 (by decide)).trans h.uart,(frame 88 (by decide)).trans h.servedWord⟩

theorem bounds (off : Nat) (mem : off∈slots) : off+4≤92 ∧ (off+4≤84 ∨ 88≤off) := by
  have casesSlot : off=0 ∨ off=4 ∨ off=8 ∨ off=44 ∨ off=48 ∨ off=52 ∨ off=56 ∨ off=60 ∨ off=64 ∨ off=68 ∨ off=72 ∨ off=88 := by
    simpa only [slots,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using mem
  rcases casesSlot with h|h|h|h|h|h|h|h|h|h|h|h <;> subst off <;> decide

theorem region {before after : Word → BitVec 8} (h : ViewFrame.Region before after fp 92) : Frame before after :=
  fun off mem => ViewFrame.word h off (bounds off mem).1

theorem initialized (ram : Word → BitVec 8) (capacity : ramRead ram 0x80ffeba0#32 .w=2048#32) : At (FutureSetup.memory ram) 0 := by
  rw [FutureSetup.memory_initialized ram capacity]
  constructor <;> simp [fp,FutureSetup.initialized,ramRead,ramWrite,ramPut,byteOf]
end E5R.Thermostat.MainServeLayout
