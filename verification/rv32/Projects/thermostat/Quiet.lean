import Projects.thermostat.Observed
namespace E5R.Thermostat.Quiet
open E5R

/-- Stronger than DetStep: no accepted device reads as well as no events.
    The explicit observed equality rules out ignored MMIO reads. -/
def Step (B : Board) (img : List Segment) (m d : Machine) : Prop :=
  ∀ o, Observed.stepInstr B img m o=⟨.ok d.core d.ram [],[]⟩

inductive Steps (B : Board) (img : List Segment) : Nat → Machine → Machine → Prop
  | refl (m) : Steps B img 0 m m
  | step {n a b c} : Step B img a b → Steps B img n b c → Steps B img (n+1) a c

theorem Step.det {B img m d} (h : Step B img m d) : DetStep B img m d := by
  intro o
  rw [←Observed.erase_step B img m o,h o]

theorem Step.observed {B img m d} (h : Step B img m d) : Observed.Step B img m d [] [] := by
  let o : Oracle := fun _ => 0#32
  have hh : Observed.Step B img m d (Observed.stepInstr B img m o).reads [] := .instr o (by rw [h o])
  simpa only [h o] using hh

theorem Steps.single {B img m d} (h : Step B img m d) : Steps B img 1 m d := .step h (.refl _)
theorem Steps.trans {B img n k a b c} (h : Steps B img n a b) (hk : Steps B img k b c) : Steps B img (n+k) a c := by
  induction h with
  | refl => simpa only [Nat.zero_add] using hk
  | step hs _ ih => simpa only [Nat.add_right_comm] using Steps.step hs (ih hk)

theorem Steps.observed {B img n m d} (h : Steps B img n m d) : Observed.Steps B img n m d [] [] := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs.observed ih

theorem Steps.det {B img n m d} (h : Steps B img n m d) : DetSteps B img n m d := by
  induction h with
  | refl => exact .refl _
  | step hs _ ih => exact .step hs.det ih

theorem step_of {B img m d i len}
    (hal : m.core.pc.getLsbD 0=false) (hf : fetchDecode img m.core.pc=some (i,len))
    (he : ∀ o, Observed.interp B img o (exec m.core len i) m.ram 0 [] []=⟨.ok d.core d.ram [],[]⟩) : Step B img m d := by
  intro o;rw [Observed.stepInstr_of hal hf];exact he o
end E5R.Thermostat.Quiet
