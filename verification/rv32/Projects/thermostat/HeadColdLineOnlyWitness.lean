import Projects.thermostat.HeadColdLineOnly
import Projects.thermostat.HeadRequestWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadColdLineOnlyWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp

def index (kind : Fin 2) : Fin 13 := ⟨kind.val,by have := kind.isLt;omega⟩
def input (kind : Fin 2) := HeadRequestWitness.input (index kind)
def core (kind : Fin 2) := HeadRequestWitness.core (index kind)
def ram (kind : Fin 2) := ramWrite (HeadRequestWitness.ram (index kind)) (sp+3668#32) 1024#32 .w

theorem max_head : ∀ kind : Fin 2, ramRead (ram kind) (sp+3664#32) .w=1024#32 := by decide +kernel
theorem max_body : ∀ kind : Fin 2, ramRead (ram kind) (sp+3668#32) .w=1024#32 := by decide +kernel
theorem bytes : ∀ kind : Fin 2, Bytes.At (ram kind) (sp+516#32) (input kind) := by unfold Bytes.At;decide +kernel
theorem no_header : ∀ kind : Fin 2, min (input kind).length 1024≤HeadRequestInputStorage.line (input kind)+2 := by decide +kernel
theorem parsed : ∀ kind : Fin 2, HttpRequestBytes.parse (input kind) 1024 1024=HeadR.incomplete := by decide +kernel

theorem app (kind : Fin 2) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

/-- Two actual cold ELF calls, HTTP1.1/1.0 first lines without any header line,
    initialize fields and fully restore the ABI with encoded Incomplete.
    The explicit main caller PC and persisted App invariant are preserved. -/
theorem execution (kind : Fin 2) : ∃ n d after, n≤1600 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧
      d.pc=0x80000a26#32 ∧ d.get 2=0x80ffeb90#32 ∧ HeadSaved.CoreAt d (core kind).get ∧
      HeadResultView.At after (sp+4904#32) .incomplete ∧ AppState.At after Spec.initial := by
  have length : (input kind).length≤32 := HeadRequestWitness.length_bound (index kind)
  have cap : min (input kind).length 1024≤32 := Nat.le_trans (Nat.min_le_left _ _) length
  obtain ⟨n,d,after,nlo,nhi,trace,pc,stack,abi,result,rx,appFrame,csr⟩ := HeadColdLineOnly.contract B (core kind) (ram kind) sp (input kind)
    rfl (by rfl) (by rfl) (by rfl) rfl (by rfl) HeadEarlyWitness.stack (by decide +kernel) (by omega)
    (max_head kind) (bytes kind) (HeadRequestWitness.complete (index kind)) (max_body kind) (no_header kind)
  rw [parsed kind] at result
  refine ⟨n,d,after,by omega,Interrupt.close trace.det rfl,?_,stack,abi,result,appFrame rfl Spec.initial (app kind)⟩
  change d.pc=0x80000a26#32 &&& ~~~1 at pc
  simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
end E5R.Thermostat.HeadColdLineOnlyWitness
