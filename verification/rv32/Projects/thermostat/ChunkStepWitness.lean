import Projects.thermostat.ChunkStep
import Projects.thermostat.ChunkEncode
import Projects.thermostat.UartPlatform
import Projects.thermostat.Interrupt
namespace E5R.Thermostat.ChunkStepWitness
open E5R E5R.Thermostat HttpRequestSpec

-- The actual main call uses SP+4864 and SP+4824, and returns to 0x80000f10.
def src : Word := 0x80fffe90#32
def dst : Word := 0x80fffe68#32

def core (b : BitVec 8) (maxBody : Nat) : Core :=
  ⟨0x80002998#32,(fun r => if r=1 then 0x80000f10#32 else if r=2 then 0x80ffeb90#32
    else if r=8 then 0x80fff814#32 else if r=10 then dst else if r=11 then src
    else if r=12 then BitVec.ofNat 32 b.toNat else if r=13 then BitVec.ofNat 32 maxBody else 0#32),
    false,false,3,0,0,0,0,0,false⟩

def ram (s : CState) := ChunkEncode.memory (fun _ => 0#8) src s

theorem ready (s : CState) (b : BitVec 8) (maxBody : Nat)
    (hi : ChunkSpecInvariant.Inv maxBody s) (hm : maxBody<4294967296) :
    ChunkStep.Pre UartPlatform.board (core b maxBody) (ram s) src dst s b maxBody := by
  constructor
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · unfold Memory.Block UartPlatform.board QemuVirtRv32.board
    rw [ThermostatImage.image_rwBase]
    decide +kernel
  · unfold Memory.Block UartPlatform.board QemuVirtRv32.board
    rw [ThermostatImage.image_rwBase]
    decide +kernel
  · decide +kernel
  · decide +kernel
  · exact ChunkEncode.at_state _ _ s (by have := hi.phase;omega)
  · exact hi
  · exact hm

/-- Concrete satisfiable machine callers for every bounded state and byte,
    using the actual board and main's call-area addresses. -/
theorem execution (s : CState) (b : BitVec 8) (maxBody : Nat)
    (hi : ChunkSpecInvariant.Inv maxBody s) (hm : maxBody<4294967296) :
    ∃ n d after, 24≤n ∧ n≤56 ∧
      Trace.Closed UartPlatform.board img n ⟨core b maxBody,ram s⟩ ⟨d,after⟩ ∧
      Observed.Steps UartPlatform.board img n ⟨core b maxBody,ram s⟩ ⟨d,after⟩ [] [] ∧
      d.pc=0x80000f10#32 ∧ d.get 2=0x80ffeb90#32 ∧
      ChunkLayout.At after dst (chunkStep s b.toNat maxBody).1 ∧
      ChunkLayout.OutAt after dst (chunkStep s b.toNat maxBody).2 ∧
      ChunkSpecInvariant.Inv maxBody (chunkStep s b.toNat maxBody).1 := by
  obtain ⟨n,d,after,hlo,hn,trace,post,inv⟩ :=
    ChunkStep.contract UartPlatform.board (core b maxBody) (ram s) src dst s b maxBody (ready s b maxBody hi hm)
  have ret : d.pc=0x80000f10#32 := by
    simpa only [show (core b maxBody).get 1=0x80000f10#32 by rfl,
      show 0x80000f10#32 &&& ~~~1=0x80000f10#32 by decide +kernel] using post.1
  have sp : d.get 2=0x80ffeb90#32 := post.2.2.2.2.1 2 (Or.inr (Or.inl rfl))
  exact ⟨n,d,after,hlo,hn,Interrupt.close trace.det rfl,trace.observed,ret,sp,post.2.1,post.2.2.1,inv⟩

end E5R.Thermostat.ChunkStepWitness
