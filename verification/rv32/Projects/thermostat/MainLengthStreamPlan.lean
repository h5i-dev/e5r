import Projects.thermostat.MainLengthWait
import Projects.thermostat.MainHeaderStreamSpec
namespace E5R.Thermostat.MainLengthStreamPlan
open E5R E5R.Thermostat
abbrev Plan := ChunkReceivePlan.Plan
abbrev Valid := ChunkReceivePlan.Valid

def logs (plan : Plan) : Nat → Nat → List Observed.Read
  | _,0 => []
  | first,count+1 => MainLengthWait.reads (plan.pending first) (plan.ready first) (plan.datum first)++logs plan (first+1) count

def cost (plan : Plan) : Nat → Nat → Nat
  | _,0 => 0
  | first,count+1 => 25+4*(plan.pending first).length+cost plan (first+1) count

theorem logs_input (plan : Plan) (first count : Nat) :
    Observed.input (logs plan first count)=MainHeaderStreamSpec.arrivals (ChunkReceivePlan.byte plan) first count := by
  induction count generalizing first with
  | zero => rfl
  | succ count ih =>
    rw [logs,Observed.input_append,MainLengthWait.input,ih,MainHeaderStreamSpec.arrivals_succ]
    rfl
/-- Input-stream projection follows the actual accepted RBR reads, over just
    the prefix consumed by the program. LSR values do not become input bytes. -/
theorem logs_wire (plan : Plan) (wire : Nat → BitVec 8) (first count available : Nat)
    (valid : Valid plan wire first available) (bound : count≤available) :
    Observed.input (logs plan first count)=MainHeaderStreamSpec.arrivals wire first count := by
  rw [logs_input]
  unfold MainHeaderStreamSpec.arrivals
  apply List.map_congr_left
  intro i hi
  have index : i<count := List.mem_range.mp hi
  exact (valid (first+i) (by omega) (by omega)).2.2

end E5R.Thermostat.MainLengthStreamPlan
