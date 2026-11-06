/- Concrete shared-memory model regression, not the FP4 program. Every lane
executes; each warp publishes its own ID through one lane, synchronizes, reads
it back, then participates in a CTA barrier. Successful schedules imply actual
Reach through the checked scheduler theorem, not a surrogate result spec. -/
import Ptx.Logic.WarpSchedule
namespace WarpSharedRegression
open Ptx

def K : Kernel where
  name := "shared_warp_regression"
  params := []
  regs := []
  shared := [⟨"slots", 4, 8⟩]
  labels := []
  body := [
    ⟨none, .mov .u32 "tid" (.sreg (.tid .x))⟩,
    ⟨none, .shr .u32 "warp" (.reg "tid") (.imm 5)⟩,
    ⟨none, .mulLo .u32 "addr" (.reg "warp") (.imm 4)⟩,
    ⟨none, .and .b32 "lane" (.reg "tid") (.imm 31)⟩,
    ⟨none, .setp .eq .u32 "leader" (.reg "lane") (.imm 0)⟩,
    ⟨some ⟨"leader", false⟩, .stVolatileShared32 (.reg "addr" 0) (.reg "warp")⟩,
    ⟨none, .warpBar⟩,
    ⟨none, .ldVolatileShared32 "read" (.reg "addr" 0)⟩,
    ⟨none, .bar⟩,
    ⟨none, .ret⟩]

def L : Launch := {grid := ⟨1,1,1⟩, block := ⟨64,1,1⟩, params := fun _ => 0, alloc := []}
def initial : Warp.State := Warp.State.init (fun _ _ => 17) (fun _ _ => true)
  (fun _ => 0xa5) (fun _ _ => 0x5a)
def schedule : List Warp.Choice :=
  L.threads.map (fun t => .run t 6) ++
  [.warp ⟨⟨0,0,0⟩,0⟩, .warp ⟨⟨0,0,0⟩,1⟩] ++
  L.threads.map (fun t => .run t 1) ++ [.cta ⟨0,0,0⟩]
def resultB (c : Warp.State) : Bool :=
  Warp.doneB K L c && L.threads.all fun t =>
    (c.cfg.ts t).r "read" == BitVec.ofNat 64 (t.tid.x.toNat/32)

theorem actual_shared_execution : ∃ c,
    Warp.Reach K L initial c ∧ Warp.Done K L c ∧
    ∀ t ∈ L.threads, (c.cfg.ts t).r "read" = BitVec.ofNat 64 (t.tid.x.toNat/32) := by
  have h : (Warp.execute K L initial schedule).any resultB = true := by
    set_option maxRecDepth 100000 in
    set_option maxHeartbeats 4000000 in
    decide +kernel
  cases he : Warp.execute K L initial schedule with
  | none => simp [he] at h
  | some c =>
    simp only [he, Option.any_some, resultB, Bool.and_eq_true] at h
    refine ⟨c, Warp.execute_reach schedule he, Warp.doneB_spec h.1, ?_⟩
    intro t ht
    exact beq_iff_eq.mp (List.all_eq_true.mp h.2 t ht)

#print axioms actual_shared_execution
end WarpSharedRegression
