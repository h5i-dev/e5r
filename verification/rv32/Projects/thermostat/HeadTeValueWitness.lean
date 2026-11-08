import Projects.thermostat.HeadTeValue
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadTeValueWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp
abbrev buf := sp+516#32

def minor (kind : Fin 10) : Nat := if kind.val=1 then 0 else 1
def oldTe (kind : Fin 10) : Bool := decide (kind.val=2)
def oldCl (kind : Fin 10) : Bool := decide (kind.val=3)
def fieldState (kind : Fin 10) : Fields :=
  ⟨[],false,oldCl kind,(if oldCl kind then 1024 else 0),oldTe kind⟩
def input (kind : Fin 10) : List Nat :=
  if kind.val=5 then [] else if kind.val=6 then [103,122,105,112]
  else if kind.val=7 then [67,72,85,78,75,69,68]
  else if kind.val=8 then [99,104,117,110,107,101,120]
  else if kind.val=9 then [99,104,117,110,107,101,100,120]
  else [99,104,117,110,107,101,100]
def ve (kind : Fin 10) : Nat := 18+(input kind).length
def le (kind : Fin 10) : Nat := ve kind+(if kind.val=4 then 1 else 0)
def expected (kind : Fin 10) : Option Nat :=
  if kind.val=0 ∨ kind.val=7 then none else if kind.val≤4 then some 400 else some 501

def core (kind : Fin 10) : Core :=
  ⟨0x800032ae#32,(fun r => if r=1 then 400#32 else if r=2 then sp
    else if r=18 then BitVec.ofNat 32 (1-minor kind)
    else if r=23 then (if oldTe kind then 1#32 else 0#32)
    else if r=15 then 18#32 else if r=26 then BitVec.ofNat 32 (le kind)
    else if r=21 then BitVec.ofNat 32 (le kind) else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 10) : Word → BitVec 8 :=
  let base := fun a => if buf.toNat+18≤a.toNat ∧ a.toNat<buf.toNat+32 then
      BitVec.ofNat 8 ((input kind).getD (a.toNat-(buf.toNat+18)) 32)
    else ReadSendWitness.ram false false a
  let r0 := ramWrite base (sp+0#32) (BitVec.ofNat 32 (le kind)-BitVec.ofNat 32 (ve kind)) .w
  let r1 := ramWrite r0 (sp+44#32) buf .w
  let r2 := ramWrite r1 (sp+48#32) 32#32 .w
  let r3 := ramWrite r2 (sp+312#32) (BitVec.ofNat 32 (fieldState kind).cl) .w
  let r4 := ramWrite r3 (sp+316#32) 0#32 .w
  let r5 := ramWrite r4 (sp+320#32) 0#32 .w
  let r6 := ramWrite r5 (sp+324#32) 0#32 .b
  let r7 := ramWrite r6 (sp+325#32) (if oldCl kind then 1#32 else 0#32) .b
  ramWrite r7 (sp+326#32) (if oldTe kind then 1#32 else 0#32) .b

theorem fields_view (kind : Fin 10) : HeadFieldsView.At (ram kind) sp (fieldState kind) := by
  constructor <;> revert kind <;> decide +kernel

theorem scratch : ∀ kind : Fin 10,
    ramRead (ram kind) (sp+0#32) .w=BitVec.ofNat 32 (le kind)-BitVec.ofNat 32 (ve kind) := by decide +kernel

theorem metadata : ∀ kind : Fin 10,
    ramRead (ram kind) (sp+44#32) .w=buf ∧ ramRead (ram kind) (sp+48#32) .w=32#32 := by decide +kernel

theorem bounds : ∀ kind : Fin 10,
    0≤18 ∧ 18≤ve kind ∧ ve kind≤le kind ∧ le kind≤32 ∧ minor kind≤1 := by decide +kernel

theorem specification : ∀ kind : Fin 10,
    HeadTeValue.outcome (HeadLineScanSpec.bytes (ram kind) buf) (fieldState kind) 18 (ve kind) (le kind) (minor kind)=expected kind := by decide +kernel

theorem app (kind : Fin 10) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

/-- Ten satisfiable internal ELF call states cover good/mixed-case chunked,
    HTTP1.0, duplicateTE, CL conflict, trailingOWS, empty/wrong-length values
    and a last-byte mismatch. These are not cold-parser reachability claims. -/
theorem execution (kind : Fin 10) : ∃ n d after, 2≤n ∧ n≤81 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧
    HeadTeValue.Post (ram kind) after sp d (expected kind) ∧
    HeadFieldsView.At after sp (if expected kind=none then {fieldState kind with te := true} else fieldState kind) ∧
    AppState.At after Spec.initial := by
  obtain ⟨b0,b1,b2,b3,b4⟩ := bounds kind
  obtain ⟨mb,mr⟩ := metadata kind
  have mem : Memory.Block B buf 32 := Memory.sub_block HeadEarlyWitness.stack (off := 516) (by decide) (by decide)
  obtain ⟨n,d,after,lo,hi,trace,result,view,frame,csr⟩ := HeadTeValue.contract B (core kind) (ram kind) sp buf (fieldState kind)
    0 18 (ve kind) (le kind) 32 (minor kind) rfl rfl rfl rfl rfl rfl rfl rfl rfl (scratch kind) mb mr (fields_view kind)
    ⟨b0,b1,b2,b3⟩ (by decide) b4 mem HeadEarlyWitness.stack (by decide +kernel)
  rw [specification kind] at result view
  refine ⟨n,d,after,lo,hi,Interrupt.close trace.det rfl,result,view,?_⟩
  have unchanged : after=ram kind ∨ after=HeadTeFlagStore.memory (ram kind) sp := by
    cases h : expected kind with
    | none =>
      have got : d.pc=0x800033b6#32 ∧ after=HeadTeFlagStore.memory (ram kind) sp := by simpa only [HeadTeValue.Post,h] using result
      exact Or.inr got.2
    | some status =>
      have got : d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status ∧ after=ram kind := by simpa only [HeadTeValue.Post,h] using result
      exact Or.inl got.2.2
  rcases unchanged with h|h
  · rw [h];exact app kind
  · rw [h]
    apply AppState.preserve (ram kind) _ Spec.initial (app kind)
    have region := HeadTeFlagMemory.region (ram kind) sp 428 25 (by decide) (by decide)
    simpa only [ViewFrame.Region,show sp+428#32=0x80ffebbc#32 by decide +kernel] using region
end E5R.Thermostat.HeadTeValueWitness
