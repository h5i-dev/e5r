import Projects.thermostat.MainChunkLoopNothing
import Projects.thermostat.MainChunkLoopData
import Projects.thermostat.MainChunkLoopTerminal
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.MainChunkLoopStep
open E5R E5R.Thermostat HttpRequestSpec

def byte (ram : Word → BitVec 8) (sp : Word) (read : Nat) : BitVec 8 := ram ((sp+132#32)+BitVec.ofNat 32 read)
def next (ram : Word → BitVec 8) (sp : Word) (read : Nat) (s : CState) := chunkStep s (byte ram sp read).toNat 1024

def AppFrame (before after : Word → BitVec 8) (sp : Word) : Prop :=
  sp=0x80ffeb90#32 → ∀ state, AppState.At before state → AppState.At after state

def Finished (c : Core) (ram : Word → BitVec 8) (sp : Word) (start read written : Nat)
    (s : CState) (d : Core) (after : Word → BitVec 8) : Prop :=
  d.pc=0x8000106c#32 ∧ ChunkLayout.At after (sp+3680#32) (next ram sp read s).1 ∧
  ChunkDecodedInvariant.Inv 1024 (next ram sp read s).1 (written-start) ∧
  ramRead after (sp+3656#32) .w=BitVec.ofNat 32 (read+1) ∧
  ramRead after (sp+3660#32) .w=BitVec.ofNat 32 written ∧
  (∀ code, (next ram sp read s).2=.reject code → (code=400 ∨ code=413) ∧ d.get 27=BitVec.ofNat 32 code) ∧
  MainChunkLayout.At after sp ∧ ViewFrame.Region ram after (sp+132#32) 2048 ∧
  d.get 10=ChunkOutputView.tag (next ram sp read s).2 ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c ∧ AppFrame ram after sp

def Post (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (start read written filled : Nat) (s : CState) (d : Core) (after : Word → BitVec 8) : Prop :=
  match (next ram sp read s).2 with
  | .nothing => MainChunkLoopInvariant.At B d after sp start (read+1) written filled (next ram sp read s).1 ∧
      ViewFrame.Region ram after (sp+132#32) 2048 ∧ AppFrame ram after sp
  | .data => MainChunkLoopInvariant.At B d after sp start (read+1) (written+1) filled (next ram sp read s).1 ∧
      after ((sp+132#32)+BitVec.ofNat 32 written)=byte ram sp read ∧
      (∀ k, k<2048 → k≠written → after ((sp+132#32)+BitVec.ofNat 32 k)=ram ((sp+132#32)+BitVec.ofNat 32 k)) ∧
      AppFrame ram after sp
  | .done | .reject _ => Finished c ram sp start read written s d after

/-- Universal one-buffered-byte refinement, including actual dispatch and
    in-place dechunking. No future input arrival is assumed. -/
theorem contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled) :
    ∃ n d after, 81≤n ∧ n≤125 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post B c ram sp start read written filled s d after := by
  cases he : (next ram sp read s).2 with
  | nothing =>
    obtain ⟨n,d,after,hlo,hn,trace,inv,rx,app⟩ := MainChunkLoopNothing.contract h available he
    refine ⟨n,d,after,hlo,by omega,trace,?_⟩
    simp only [Post,he]
    exact ⟨inv,rx,app⟩
  | data =>
    obtain ⟨n,d,after,hlo,hn,trace,inv,stored,rx,app⟩ := MainChunkLoopData.contract h available he
    refine ⟨n,d,after,by omega,hn,trace,?_⟩
    simp only [Post,he]
    exact ⟨inv,stored,rx,app⟩
  | done =>
    obtain ⟨n,d,after,hlo,hn,trace,post⟩ := MainChunkLoopTerminal.contract h available (Or.inl he)
    refine ⟨n,d,after,hlo,by omega,trace,?_⟩
    simp only [Post,he]
    exact post
  | reject status =>
    obtain ⟨n,d,after,hlo,hn,trace,post⟩ := MainChunkLoopTerminal.contract h available (Or.inr ⟨status,he⟩)
    refine ⟨n,d,after,hlo,by omega,trace,?_⟩
    simp only [Post,he]
    exact post

/-- All actual strict execution prefixes agree with the finite certificate
    and have no accepted device reads, events, or fault/unsupported escape. -/
theorem safe_contract {B c ram sp start read written filled s}
    (h : MainChunkLoopInvariant.At B c ram sp start read written filled s) (available : read<filled) :
    ∃ n d after, 81≤n ∧ n≤125 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post B c ram sp start read written filled s d after ∧
      (∀ k e reads evs, k<n → Observed.Steps B img k ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hn,trace,post⟩ := contract h available
  exact ⟨n,d,after,hlo,hn,Interrupt.close trace.det h.masked,post,
    fun _ _ _ _ hk actual => QuietPrefix.safe trace h.masked hk actual⟩

end E5R.Thermostat.MainChunkLoopStep
