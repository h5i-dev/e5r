import Projects.thermostat.HeadClValue
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadClValueWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp
abbrev buf := sp+516#32

def oldTe (kind : Fin 16) : Bool := decide (kind.val=13)
def oldCl (kind : Fin 16) : Bool := decide (kind.val=12)
def fieldState (kind : Fin 16) : Fields :=
  ⟨[],false,oldCl kind,(if oldCl kind then 1024 else 0),oldTe kind⟩
def text (kind : Fin 16) : String :=
  match kind.val with
  | 0 => "0" | 1 => "1" | 2 => "1024" | 3 => "1025"
  | 4 => "9999999999999999999999" | 5 => "01" | 6 => "-1" | 7 => "+1"
  | 8 => "" | 9 => "1a" | 10 => "1.0" | 11 => "000000000000000000001"
  | 12 => "1" | 13 => "1" | 14 => "1" | _ => "18446744073709551616"
def input (kind : Fin 16) : List Nat := (WireSpec.ascii (text kind)).map BitVec.toNat
def ve (kind : Fin 16) : Nat := 18+(input kind).length
def le (kind : Fin 16) : Nat := ve kind+(if kind.val=14 then 1 else 0)
def expected (kind : Fin 16) : Num :=
  match kind.val with
  | 0 => .ok 0 | 1 => .ok 1 | 2 => .ok 1024 | 3 => .bad 413 | 4 => .bad 413
  | 5 => .ok 1 | 11 => .ok 1 | 15 => .bad 413 | _ => .bad 400

def core (kind : Fin 16) : Core :=
  ⟨0x800031dc#32,(fun r => if r=1 then 400#32 else if r=2 then sp
    else if r=23 then (if oldTe kind then 1#32 else 0#32)
    else if r=15 then 18#32 else if r=26 then BitVec.ofNat 32 (le kind)
    else if r=11 then BitVec.ofNat 32 (le kind) else if r=16 then 10#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 16) : Word → BitVec 8 :=
  let base := fun a => if buf.toNat+18≤a.toNat ∧ a.toNat<buf.toNat+64 then
      BitVec.ofNat 8 ((input kind).getD (a.toNat-(buf.toNat+18)) 32)
    else ReadSendWitness.ram false false a
  let r0 := ramWrite base (sp+0#32) (BitVec.ofNat 32 (le kind)-BitVec.ofNat 32 (ve kind)) .w
  let r1 := ramWrite r0 (sp+44#32) buf .w
  let r2 := ramWrite r1 (sp+48#32) 64#32 .w
  let r3 := ramWrite r2 (sp+312#32) (BitVec.ofNat 32 (fieldState kind).cl) .w
  let r4 := ramWrite r3 (sp+316#32) 0#32 .w
  let r5 := ramWrite r4 (sp+320#32) 0#32 .w
  let r6 := ramWrite r5 (sp+324#32) 0#32 .b
  let r7 := ramWrite r6 (sp+325#32) (if oldCl kind then 1#32 else 0#32) .b
  let r8 := ramWrite r7 (sp+326#32) (if oldTe kind then 1#32 else 0#32) .b
  ramWrite r8 (sp+8#32) 1024#32 .w

theorem fields_view (kind : Fin 16) : HeadFieldsView.At (ram kind) sp (fieldState kind) := by
  constructor <;> revert kind <;> decide +kernel

theorem scratch : ∀ kind : Fin 16,
    ramRead (ram kind) (sp+0#32) .w=BitVec.ofNat 32 (le kind)-BitVec.ofNat 32 (ve kind) := by decide +kernel

theorem metadata : ∀ kind : Fin 16,
    ramRead (ram kind) (sp+44#32) .w=buf ∧ ramRead (ram kind) (sp+48#32) .w=64#32 ∧ ramRead (ram kind) (sp+8#32) .w=1024#32 := by decide +kernel

theorem bounds : ∀ kind : Fin 16,
    18≤ve kind ∧ ve kind≤le kind ∧ le kind≤64 ∧ ve kind-18≤22 := by decide +kernel

theorem specification : ∀ kind : Fin 16,
    HeadClValue.outcome (HeadLineScanSpec.bytes (ram kind) buf) (fieldState kind) 18 (ve kind) (le kind)=expected kind := by decide +kernel

theorem app (kind : Fin 16) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

/-- Sixteen satisfiable internal call states include exact1024/1025, leading
    zeros, long zero prefixes, huge numerals, non-digits, empty value, duplicate
    CL, TE conflict and trailingOWS. No cold/reset reachability is asserted. -/
theorem execution (kind : Fin 16) : ∃ n d after, 7≤n ∧ n≤680 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧
    HeadClNumber.Post (ram kind) after sp d (expected kind) ∧
    HeadFieldsView.At after sp (HeadClNumber.updated (fieldState kind) (expected kind)) ∧
    AppState.At after Spec.initial := by
  obtain ⟨b0,b1,b2,b3⟩ := bounds kind
  obtain ⟨mb,mr,ml⟩ := metadata kind
  have mem : Memory.Block B buf 64 := Memory.sub_block HeadEarlyWitness.stack (off := 516) (by decide) (by decide)
  obtain ⟨n,d,after,lo,hi,trace,result,view,frame,csr⟩ := HeadClValue.contract B (core kind) (ram kind) sp buf
    18 (ve kind) (le kind) 64 (fieldState kind) rfl rfl rfl rfl rfl rfl rfl rfl (scratch kind) mb mr ml (fields_view kind)
    ⟨b0,b1,b2⟩ (by decide) mem HeadEarlyWitness.stack (by decide +kernel)
  rw [specification kind] at result view
  refine ⟨n,d,after,lo,by omega,Interrupt.close trace.det rfl,result,view,?_⟩
  cases h : expected kind with
  | bad status =>
    have got : d.pc=0x8000342c#32 ∧ d.get 1=BitVec.ofNat 32 status ∧ after=ram kind := by simpa only [HeadClNumber.Post,h] using result
    rw [got.2.2];exact app kind
  | ok value =>
    have got : d.pc=0x800033b6#32 ∧ after=HeadClStoreRaw.memory (ram kind) sp (BitVec.ofNat 32 value) := by simpa only [HeadClNumber.Post,h] using result
    rw [got.2]
    apply AppState.preserve (ram kind) _ Spec.initial (app kind)
    have region := HeadClStoreMemory.region (ram kind) sp (BitVec.ofNat 32 value) 428 25 (by decide) (by decide) (by decide)
    simpa only [ViewFrame.Region,show sp+428#32=0x80ffebbc#32 by decide +kernel] using region
end E5R.Thermostat.HeadClValueWitness
