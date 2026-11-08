import Projects.thermostat.ChunkStepWitness
namespace E5R.Thermostat.ChunkStepFixtures
open E5R E5R.Thermostat HttpRequestSpec ChunkStepWitness

def Example (s : CState) (b : BitVec 8) (next : CState) (out : COut) : Prop :=
  ∃ n d after, 24≤n ∧ n≤56 ∧
    Trace.Closed UartPlatform.board img n ⟨core b 1024,ram s⟩ ⟨d,after⟩ ∧
    Observed.Steps UartPlatform.board img n ⟨core b 1024,ram s⟩ ⟨d,after⟩ [] [] ∧
    d.pc=0x80000f10#32 ∧ d.get 2=0x80ffeb90#32 ∧
    ChunkLayout.At after dst next ∧ ChunkLayout.OutAt after dst out ∧
    ChunkSpecInvariant.Inv 1024 next

theorem checked (s : CState) (b : BitVec 8) (next : CState) (out : COut)
    (hi : ChunkSpecInvariant.Inv 1024 s) (step : chunkStep s b.toNat 1024=(next,out)) :
    Example s b next out := by
  have h := execution s b 1024 hi (by decide)
  simpa only [Example,step] using h

theorem lower_f : Example cStart 102#8 ⟨0,15,1,0⟩ .nothing :=
  checked _ _ _ _ (ChunkSpecInvariant.initial 1024) (by decide +kernel)

theorem ninth_digit : Example ⟨0,4294967295,8,0⟩ 48#8 ⟨0,4294967295,8,0⟩ (.reject 400) :=
  checked _ _ _ _ (by constructor <;> decide +kernel) (by decide +kernel)

theorem payload_limit : Example ⟨0,1025,3,0⟩ 13#8 ⟨0,1025,3,0⟩ (.reject 413) :=
  checked _ _ _ _ (by constructor <;> decide +kernel) (by decide +kernel)

theorem final_lf : Example ⟨6,0,1,7⟩ 10#8 ⟨7,0,1,7⟩ .done :=
  checked _ _ _ _ (by constructor <;> decide +kernel) (by decide +kernel)

theorem binary_data : Example ⟨2,2,0,3⟩ 255#8 ⟨2,1,0,3⟩ .data :=
  checked _ _ _ _ (by constructor <;> decide +kernel) (by decide +kernel)

theorem bad_data_lf_resets_size : Example ⟨4,7,2,9⟩ 0#8 ⟨4,0,2,9⟩ (.reject 400) :=
  checked _ _ _ _ (by constructor <;> decide +kernel) (by decide +kernel)

end E5R.Thermostat.ChunkStepFixtures
