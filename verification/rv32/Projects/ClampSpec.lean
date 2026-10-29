import Theories.RV32
namespace Clamp
open RV32

def spec (input : Nat) : Nat := min (input+7) 100

def initial (image : List Region) (entry input : Nat) : Except Fault State := do
  let mem ← writeWord image 0x2000 input
  return { pc := entry, mem := mem }

def check (image : List Region) (entry stop maxSteps input : Nat) : Bool :=
  match initial image entry input with
  | .error _ => false
  | .ok start =>
    match reach (maxSteps+2) stop start, writeWord start.mem 0x2004 (spec input) with
    | .ok (steps, final), .ok expected =>
      steps > 0 && steps ≤ maxSteps && final.pc == stop &&
      final.mem == expected && reg final 0 == 0 &&
      decide (readWord final.mem 0x2004 = .ok (spec input)) &&
      spec input ≤ 100 &&
      final.accesses == [.load 0x2000, .store 0x2004 (spec input)] &&
      decide (readWord final.mem stop true = .ok 0x0000006f)
    | _, _ => false

/-- A successful finite execution with exact output, bounded accesses and a
    whole-memory frame. Reaching the observation PC is not hardware shutdown. -/
def Ensures (image : List Region) (entry stop maxSteps input : Nat) : Prop :=
  ∃ start final steps expected,
    initial image entry input = .ok start ∧
    reach (maxSteps+2) stop start = .ok (steps, final) ∧
    writeWord start.mem 0x2004 (spec input) = .ok expected ∧
    0 < steps ∧ steps ≤ maxSteps ∧ final.pc = stop ∧
    final.mem = expected ∧ reg final 0 = 0 ∧
    readWord final.mem 0x2004 = .ok (spec input) ∧ spec input ≤ 100 ∧
    final.accesses = [.load 0x2000, .store 0x2004 (spec input)] ∧
    readWord final.mem stop true = .ok 0x0000006f

theorem check_sound {image entry stop maxSteps input}
    (h : check image entry stop maxSteps input = true) :
    Ensures image entry stop maxSteps input := by
  unfold check at h
  split at h
  · contradiction
  · rename_i start hi
    split at h
    · rename_i steps final expected hr hw
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨hpos, hmax⟩, hpc⟩, hmem⟩, hx0⟩, hread⟩, hbound⟩, haccess⟩, hfetch⟩
      exact ⟨start, final, steps, expected, hi, hr, hw, hpos, hmax, hpc, hmem,
        hx0, hread, hbound, haccess, hfetch⟩
    · contradiction

#print axioms check_sound
end Clamp
