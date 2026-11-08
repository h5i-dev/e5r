import Projects.thermostat.HeadRequestInput
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadRequestWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp

def input (kind : Fin 13) : List (BitVec 8) := WireSpec.ascii (
  if kind=0 then "POST /mode HTTP/1.1\r\n" else if kind=1 then "POST /mode HTTP/1.0\r\n"
  else if kind=2 then "POST /mode HTTP/2.0\r\n" else if kind=3 then "POST /mode HTTP/1.9\r\n"
  else if kind=4 then "POST /mode HTTX/1.1\r\n" else if kind=5 then "POST /mode HTTP/1x1\r\n"
  else if kind=6 then "POST /mode HTTP/:.1\r\n" else if kind=7 then "POST /mode HTTP/1.:\r\n"
  else if kind=8 then "POST /mode HTTP/1\r\n" else if kind=9 then "POST x HTTP/1.1\r\n"
  else if kind=10 then "POST /m\tHTTP/1.1\r\n" else if kind=11 then "\r\n" else "PO@ST /mode HTTP/1.1\r\n")

def expected (kind : Fin 13) : ReqLine :=
  if kind=0 then .ok 0 4 5 10 1 else if kind=1 then .ok 0 4 5 10 0
  else if kind=2 ∨ kind=3 then .bad 505 else .bad 400

def core (kind : Fin 13) : Core :=
  ⟨0x80002c46#32,(fun r => if r=1 then 0x80000a26#32 else if r=2 then 0x80ffeb90#32
    else if r=8 then 0x80fff814#32 else if r=10 then 0x80fffd38#32 else if r=11 then 0x80ffec14#32
    else if r=12 then BitVec.ofNat 32 (input kind).length else if r=13 then 0x80fff860#32
    else if r=19 then 0x10000000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 13) (a : Word) : BitVec 8 :=
  if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec14+(input kind).length then
    (input kind)[a.toNat-0x80ffec14]?.getD 0#8
  else if a=0x80fff861#32 then 4#8
  else if a=0x80fff860#32 ∨ a=0x80fff862#32 ∨ a=0x80fff863#32 then 0#8
  else ReadSendWitness.ram false false a

theorem max_head : ∀ kind : Fin 13, ramRead (ram kind) (sp+3664#32) .w=1024#32 := by decide +kernel

theorem app (kind : Fin 13) : AppState.At (ram kind) Spec.initial := by
  have cases : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 ∨ kind=8 ∨ kind=9 ∨ kind=10 ∨ kind=11 ∨ kind=12 := by
    have := kind.isLt;omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals subst kind;constructor
  all_goals first
    | (change ∀ i : Fin 10, ram _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem bytes : ∀ kind : Fin 13, Bytes.At (ram kind) (sp+516#32) (input kind) := by
  unfold Bytes.At
  decide +kernel

theorem complete : ∀ kind : Fin 13, HeadByteInput.term (input kind)=0 := by decide +kernel

theorem parsed : ∀ kind : Fin 13, HeadRequestInput.request (input kind)=expected kind := by decide +kernel

theorem length_bound : ∀ kind : Fin 13, (input kind).length≤32 := by decide +kernel

def finish (kind : Fin 13) : Word := if kind=0 ∨ kind=1 then 0x80002f0e#32 else 0x80000a26#32

/-- Keep the concrete main return PC explicit, independently of the input RA. -/
theorem outcome_pc (kind : Fin 13) (d : Core) (after : Word → BitVec 8)
    (out : HeadRequestOutcome.At d after sp (core kind).get (HeadRequestInput.line (input kind))
      (input kind).length (min (input kind).length 1024) (expected kind)) : d.pc=finish kind := by
  have cases : kind=0 ∨ kind=1 ∨ kind=2 ∨ kind=3 ∨ kind=4 ∨ kind=5 ∨ kind=6 ∨ kind=7 ∨ kind=8 ∨ kind=9 ∨ kind=10 ∨ kind=11 ∨ kind=12 := by
    have := kind.isLt;omega
  rcases cases with h|h|h|h|h|h|h|h|h|h|h|h|h
  · subst kind
    change d.pc=0x80002f0e#32
    exact out.2.2.pc
  · subst kind
    change d.pc=0x80002f0e#32
    exact out.2.2.pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  · subst kind
    change d.pc=0x80000a26#32
    have pc := out.1
    change d.pc=0x80000a26#32 &&& ~~~1 at pc
    simpa only [show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc

/-- Thirteen satisfiable actual caller inputs exercise valid HTTP/1.0/1.1
    header entries and complete 400/505 returns. All original App bytes survive. -/
theorem execution (kind : Fin 13) : ∃ n d after, n≤1305 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=finish kind ∧
    HeadRequestOutcome.At d after sp (core kind).get (HeadRequestInput.line (input kind))
      (input kind).length (min (input kind).length 1024) (expected kind) ∧ AppState.At after Spec.initial := by
  have len : (input kind).length≤2048 := by have := length_bound kind;omega
  obtain ⟨n,d,after,hlo,hn,trace,result,rx,appFrame,savedAfter,csr⟩ := HeadRequestInput.contract B (core kind) (ram kind) sp (input kind)
    rfl (by rfl) (by rfl) (by rfl) rfl (by rfl) HeadEarlyWitness.stack (by decide +kernel) len (max_head kind) (bytes kind) (complete kind)
  rw [parsed kind] at result
  have cap : min (input kind).length 1024≤32 := by have := length_bound kind;have := Nat.min_le_left (input kind).length 1024;omega
  exact ⟨n,d,after,by omega,Interrupt.close trace.det rfl,outcome_pc kind d after result,result,appFrame rfl Spec.initial (app kind)⟩
end E5R.Thermostat.HeadRequestWitness
