import Projects.thermostat.Control
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Control
open E5R

def IsSystem : Instr → Bool
  | .csr _ _ _ _ | .mret => true
  | _ => false

theorem compressed (w : Word) (i : Instr) (h : decode16 w = some i) : IsSystem i = false := by
  dsimp only [decode16] at h
  split at h <;>
    repeat' first
      | contradiction
      | (simp only [Option.map_some,Option.some.injEq] at h; subst i; rfl)
      | split at h

theorem non_system_opcode (w : Word) (i : Instr) (h : decode32 w = some i)
    (hop : bits w 0 7 ≠ 0x73) : IsSystem i = false := by
  dsimp only [decode32] at h
  split at h <;>
    repeat' first
      | contradiction
      | (simp only [Option.map_some,Option.some.injEq] at h; subst i; rfl)
      | split at h

 theorem non_system_safe (i : Instr) (h : IsSystem i = false) : Safe i := by
  cases i <;> simp_all [IsSystem,Safe]
end E5R.Thermostat.Control
