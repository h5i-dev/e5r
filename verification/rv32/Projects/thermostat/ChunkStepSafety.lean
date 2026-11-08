import Projects.thermostat.ChunkStep
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.ChunkStepSafety
open E5R E5R.Thermostat HttpRequestSpec

/-- All actual observed executions through this function agree with its
    byte specification. Every strict prefix is safe; the return boundary
    requires the caller's next certificate. Scheduling and input arrival
    remain outside this finite execution statement. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word)
    (s : CState) (b : BitVec 8) (maxBody : Nat)
    (h : ChunkStep.Pre B c ram src dst s b maxBody) (hm : c.mie_=false) :
    ∃ n d after, 24≤n ∧ n≤56 ∧
      Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      ChunkStep.Post c d ram after dst (chunkStep s b.toNat maxBody).1 (chunkStep s b.toNat maxBody).2 ∧
      ChunkSpecInvariant.Inv maxBody (chunkStep s b.toNat maxBody).1 ∧
      (∀ k e reads evs, k<n → Observed.Steps B img k ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) ∧
      (∀ e reads evs, Observed.Steps B img n ⟨c,ram⟩ e reads evs →
        e=⟨d,after⟩ ∧ reads=[] ∧ evs=[]) := by
  obtain ⟨n,d,after,hlo,hn,trace,post,inv⟩ := ChunkStep.contract B c ram src dst s b maxBody h
  exact ⟨n,d,after,hlo,hn,Interrupt.close trace.det hm,post,inv,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace hm hk actual,
    fun _ _ _ actual => QuietPrefix.complete trace hm actual⟩

end E5R.Thermostat.ChunkStepSafety
