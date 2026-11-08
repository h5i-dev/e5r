import Projects.thermostat.HeadMethodBadInput
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
namespace E5R.Thermostat.HeadMethodBadWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp

def input (kind : Fin 6) : List (BitVec 8) := WireSpec.ascii (
  if kind=0 then "\r\n" else if kind=1 then " / HTTP/1.1\r\n" else if kind=2 then "@ / HTTP/1.1\r\n"
  else if kind=3 then "PO@ST / HTTP/1.1\r\n" else if kind=4 then "POST\r\n" else "POST\t/ HTTP/1.1\r\n")

def core (kind : Fin 6) : Core :=
  ⟨0x80002c46#32,(fun r => if r=1 then 0x80000a26#32 else if r=2 then 0x80ffeb90#32
    else if r=8 then 0x80fff814#32 else if r=10 then 0x80fffd38#32 else if r=11 then 0x80ffec14#32
    else if r=12 then BitVec.ofNat 32 (input kind).length else if r=13 then 0x80fff860#32
    else if r=19 then 0x10000000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 6) (a : Word) : BitVec 8 :=
  if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec14+(input kind).length then
    (input kind)[a.toNat-0x80ffec14]?.getD 0#8
  else if a=0x80fff861#32 then 4#8
  else if a=0x80fff860#32 ∨ a=0x80fff862#32 ∨ a=0x80fff863#32 then 0#8
  else ReadSendWitness.ram false false a

theorem max_head : ∀ kind : Fin 6, ramRead (ram kind) (sp+3664#32) .w=1024#32 := by decide +kernel

theorem app (kind : Fin 6) : AppState.At (ram kind) Spec.initial := by
  have cases : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 := by
    have := kind.isLt; omega
  rcases cases with h|h|h|h|h|h
  all_goals subst kind; constructor
  all_goals first
    | (change ∀ i : Fin 10, ram _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem bytes : ∀ kind : Fin 6, Bytes.At (ram kind) (sp+516#32) (input kind) := by
  unfold Bytes.At
  decide +kernel

theorem complete : ∀ kind : Fin 6, HeadByteInput.term (input kind)=0 := by decide +kernel

theorem bad : ∀ kind : Fin 6, HeadMethodInputSpec.Bad (input kind) := by decide +kernel

theorem length_bound : ∀ kind : Fin 6, (input kind).length≤18 := by decide +kernel

/-- Six satisfiable real caller layouts, including the zero-length method,
    invalid first/interior byte, absent delimiter and TAB instead of SP. -/
theorem execution (kind : Fin 6) : ∃ n d after, n≤518 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=0x80000a26#32 ∧ d.get 2=0x80ffeb90#32 ∧
    HeadSaved.CoreAt d (core kind).get ∧ HeadResultView.At after (sp+4904#32) (.reject 400) ∧
    AppState.At after Spec.initial := by
  have len : (input kind).length≤2048 := by have := length_bound kind;omega
  obtain ⟨n,d,hlo,hn,trace,pc,stack,abi,result,rx,appFrame,csr⟩ := HeadMethodBadInput.contract B (core kind) (ram kind) sp (input kind)
    rfl (by rfl) (by rfl) (by rfl) rfl (by rfl) HeadEarlyWitness.stack (by decide +kernel) len (max_head kind) (bytes kind) (complete kind) (bad kind)
  rw [HeadMethodInputSpec.classification _ (complete kind) (bad kind)] at result
  have cap : min (input kind).length 1024≤18 := by have := length_bound kind;have := Nat.min_le_left (input kind).length 1024;omega
  have pc' : d.pc=0x80000a26#32 := by simpa only [show (core kind).get 1=0x80000a26#32 from rfl,
    show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  exact ⟨n,d,_,by omega,Interrupt.close trace.det rfl,pc',stack,abi,result,appFrame rfl Spec.initial (app kind)⟩
end E5R.Thermostat.HeadMethodBadWitness
