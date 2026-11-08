import Projects.thermostat.HeadFieldsLoop
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadFieldsLoopWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp
abbrev buf := sp+516#32

def input (kind : Fin 32) : List (BitVec 8) :=
  match kind.val with
  | 0 => [72#8,111#8,115#8,116#8,58#8,32#8,120#8,13#8,10#8,13#8,10#8]
  | 1 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,32#8,49#8,48#8,50#8,52#8,13#8,10#8,13#8,10#8]
  | 2 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,32#8,49#8,48#8,50#8,53#8,13#8,10#8,13#8,10#8]
  | 3 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,32#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,13#8,10#8]
  | 4 => [72#8,111#8,115#8,116#8,58#8,97#8,13#8,10#8,72#8,111#8,115#8,116#8,58#8,98#8,13#8,10#8,13#8,10#8]
  | 5 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,49#8,13#8,10#8,67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,49#8,13#8,10#8,13#8,10#8]
  | 6 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,13#8,10#8]
  | 7 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,49#8,13#8,10#8,84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,13#8,10#8]
  | 8 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,49#8,13#8,10#8,13#8,10#8]
  | 9 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,13#8,10#8,13#8,10#8]
  | 10 => [84#8,82#8,65#8,78#8,83#8,70#8,69#8,82#8,45#8,69#8,78#8,67#8,79#8,68#8,73#8,78#8,71#8,58#8,32#8,67#8,72#8,85#8,78#8,75#8,69#8,68#8,13#8,10#8,13#8,10#8]
  | 11 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,103#8,122#8,105#8,112#8,13#8,10#8,13#8,10#8]
  | 12 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,32#8,99#8,104#8,117#8,110#8,107#8,101#8,100#8,32#8,13#8,10#8,13#8,10#8]
  | 13 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,32#8,48#8,48#8,48#8,48#8,13#8,10#8,13#8,10#8]
  | 14 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,32#8,48#8,48#8,48#8,48#8,48#8,49#8,48#8,50#8,52#8,13#8,10#8,13#8,10#8]
  | 15 => [88#8,58#8,97#8,13#8,10#8,72#8,111#8,115#8,116#8,58#8,120#8,13#8,10#8,67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,51#8,13#8,10#8,13#8,10#8]
  | 16 => [88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,13#8,10#8]
  | 17 => [88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,88#8,58#8,97#8,13#8,10#8,13#8,10#8]
  | 18 => [13#8,10#8]
  | 19 => [88#8,58#8,97#8]
  | 20 => [88#8,58#8,97#8,13#8,10#8]
  | 21 => [10#8]
  | 22 => [66#8,97#8,100#8,32#8,78#8,97#8,109#8,101#8,58#8,120#8,13#8,10#8,13#8,10#8]
  | 23 => [88#8,58#8,127#8,13#8,10#8,13#8,10#8]
  | 24 => [88#8,58#8,128#8,13#8,10#8,13#8,10#8]
  | 25 => [88#8,58#8,9#8,32#8,97#8,32#8,9#8,13#8,10#8,13#8,10#8]
  | 26 => [88#8,58#8,97#8,9#8,98#8,13#8,10#8,13#8,10#8]
  | 27 => [88#8,58#8,0#8,13#8,10#8,13#8,10#8]
  | 28 => [88#8,59#8,122#8,13#8,10#8,13#8,10#8]
  | 29 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,13#8,10#8,13#8,10#8]
  | 30 => [67#8,111#8,110#8,116#8,101#8,110#8,116#8,45#8,76#8,101#8,110#8,103#8,116#8,104#8,58#8,32#8,49#8,32#8,13#8,10#8,13#8,10#8]
  | 31 => [84#8,114#8,97#8,110#8,115#8,102#8,101#8,114#8,45#8,69#8,110#8,99#8,111#8,100#8,105#8,110#8,103#8,58#8,13#8,10#8,13#8,10#8]
  | _ => [0#8]

def minor (kind : Fin 32) : Nat := if kind.val=9 then 0 else 1
def g (kind : Fin 32) : Nat → Nat := window ((input kind).map BitVec.toNat) (input kind).length

def ordinary16 : List Field := (List.range 16).map (fun i => ⟨5*i,5*i+1,5*i+2,5*i+3⟩)

def expected (kind : Fin 32) : Fielded :=
  match kind.val with
  | 0 => .done ⟨[⟨0,4,6,7⟩],true,false,0,false⟩ 11
  | 1 => .done ⟨[⟨0,14,16,20⟩],false,true,1024,false⟩ 24
  | 2 => .bad 413
  | 3 => .done ⟨[⟨0,17,19,26⟩],false,false,0,true⟩ 30
  | 10 => .done ⟨[⟨0,17,19,26⟩],false,false,0,true⟩ 30
  | 11 => .bad 501
  | 13 => .done ⟨[⟨0,14,16,20⟩],false,true,0,false⟩ 24
  | 14 => .done ⟨[⟨0,14,16,25⟩],false,true,1024,false⟩ 29
  | 15 => .done ⟨[⟨0,1,2,3⟩,⟨5,9,10,11⟩,⟨13,27,28,29⟩],true,true,3,false⟩ 33
  | 16 => .done ⟨ordinary16,false,false,0,false⟩ 82
  | 17 => .bad 431
  | 18 => .done Fields.empty 2
  | 19 => .more
  | 20 => .more
  | 24 => .done ⟨[⟨0,1,2,3⟩],false,false,0,false⟩ 7
  | 25 => .done ⟨[⟨0,1,4,5⟩],false,false,0,false⟩ 11
  | 26 => .done ⟨[⟨0,1,2,5⟩],false,false,0,false⟩ 9
  | 31 => .bad 501
  | _ => .bad 400

def core (kind : Fin 32) : Core :=
  ⟨0x80002f58#32,(fun r => if r=2 then sp else if r=16 then 10#32 else if r=17 then 13#32
    else if r=5 then 33#32 else if r=6 then 48#32 else if r=7 then 14#32
    else if r=28 then 58#32 else if r=27 then 91#32 else if r=8 then BitVec.ofNat 32 (minor kind)
    else if r=18 then BitVec.ofNat 32 (1-minor kind)
    else if r=22 then 0#32-BitVec.ofNat 32 (input kind).length else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 32) : Word → BitVec 8 :=
  let base := fun a => if buf.toNat≤a.toNat ∧ a.toNat<buf.toNat+(input kind).length then
      (input kind)[a.toNat-buf.toNat]?.getD 0#8 else ReadSendWitness.ram false false a
  let r0 := ramWrite base (sp+8#32) 1024#32 .w
  let r1 := ramWrite r0 (sp+12#32) (BitVec.ofNat 32 (input kind).length+0xffffffff#32) .w
  let r2 := ramWrite r1 (sp+16#32) (buf+1#32) .w
  let r3 := ramWrite r2 (sp+32#32) 9409#32 .w
  let r4 := ramWrite r3 (sp+36#32) 1024#32 .w
  let r5 := ramWrite r4 (sp+40#32) (BitVec.ofNat 32 (input kind).length) .w
  let r6 := ramWrite r5 (sp+44#32) buf .w
  let r7 := ramWrite r6 (sp+48#32) (BitVec.ofNat 32 (input kind).length) .w
  ramWrite r7 (sp+52#32) (sp+4904#32) .w

theorem regs (kind : Fin 32) : HeadFieldsRegs.At (core kind) sp 0 (input kind).length (minor kind) Fields.empty := by
  constructor <;> rfl

theorem metadata (kind : Fin 32) : HeadFieldsMeta.At (ram kind) sp (input kind).length (input kind).length := by
  constructor <;> revert kind <;> decide +kernel

theorem empty_fields (kind : Fin 32) : HeadFieldsView.At (ram kind) sp Fields.empty := by
  constructor <;> revert kind <;> decide +kernel

theorem actual_bytes : ∀ kind : Fin 32, ∀ k : Fin (input kind).length,
    HeadLineScanSpec.bytes (ram kind) buf k.val=g kind k.val := by decide +kernel

theorem limits : ∀ kind : Fin 32, 0<(input kind).length ∧ (input kind).length≤128 ∧ minor kind≤1 := by decide +kernel

theorem parsed : ∀ kind : Fin 32,
    fields (g kind) (input kind).length (minor kind) 1024 0 Fields.empty=expected kind := by decide +kernel

theorem app (kind : Fin 32) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

def pc : Fielded → Word
  | .more => 0x800033ea#32
  | .bad _ => 0x8000342c#32
  | .done _ _ => 0x80003456#32

theorem at_pc {c after length minor result}
    (h : HeadFieldsLoop.At c after sp length minor result) : c.pc=pc result := by
  cases result with
  | more => exact h
  | bad _ => exact h.1
  | done _ _ => exact h.1

/-- Thirty-two real F58 header-block executions include multiple headers,
    sixteen accepted fields/17th refusal, exactCL1024/1025, duplicate/conflicting
    fields, real TE reload before subsequent CL, minor0, byte/OWS failures and
    incomplete input. These are not reset/cold-parser/HTTP-response witnesses. -/
theorem execution (kind : Fin 32) : ∃ n d after, 10≤n ∧ n≤246262 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=pc (expected kind) ∧
    HeadFieldsLoop.At d after sp (input kind).length (minor kind) (expected kind) ∧ AppState.At after Spec.initial := by
  obtain ⟨positive,bound,version⟩ := limits kind
  obtain ⟨n,d,after,lo,hi,trace,result,metaAfter,constantsAfter,memoryAfter,regFrame,csr⟩ := HeadFieldsLoop.contract B (core kind) (ram kind) sp (g kind)
    0 (input kind).length (input kind).length (minor kind) Fields.empty (regs kind) (metadata kind) (empty_fields kind)
    (fun k hk => actual_bytes kind ⟨k,hk⟩) positive (by omega) (by omega) version HeadEarlyWitness.stack (by decide +kernel)
    HeadHeaderLiterals.content_outside HeadHeaderLiterals.transfer_outside
  rw [parsed kind] at result
  have numerical : HeadFieldsLoop.budget (input kind).length Fields.empty.headers.length≤246262 := by
    change 17*(662+108*(input kind).length)≤246262
    omega
  refine ⟨n,d,after,lo,by omega,Interrupt.close trace.det rfl,at_pc result,result,?_⟩
  apply AppState.preserve (ram kind) after Spec.initial (app kind)
  have region := memoryAfter 428 25 (by decide) (by decide)
  simpa only [ViewFrame.Region,show sp+428#32=0x80ffebbc#32 by decide +kernel] using region
end E5R.Thermostat.HeadFieldsLoopWitness
