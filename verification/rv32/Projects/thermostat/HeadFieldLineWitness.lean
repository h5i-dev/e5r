import Projects.thermostat.HeadFieldLine
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadFieldLineWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp

def input (kind : Fin 20) : List (BitVec 8) :=
  if kind=0 then WireSpec.ascii "Host: x\r\n" else if kind=1 then WireSpec.ascii "\r\n"
  else if kind=2 then WireSpec.ascii "\n" else if kind=3 then WireSpec.ascii "Bad Name: x\r\n"
  else if kind=4 then WireSpec.ascii "\tX: y\r\n" else if kind=5 then WireSpec.ascii "X:\t a \t\r\n"
  else if kind=6 then WireSpec.ascii "X:"++[127#8]++WireSpec.ascii "\r\n"
  else if kind=7 then WireSpec.ascii "X:"++[128#8]++WireSpec.ascii "\r\n"
  else if kind=8 then WireSpec.ascii "X:\r\n" else if kind=9 then WireSpec.ascii "X: \t\r\n"
  else if kind=10 then WireSpec.ascii "X; z\r\n" else if kind=11 then WireSpec.ascii "X: z\r"
  else if kind=12 then WireSpec.ascii "X: z\n" else if kind=13 then WireSpec.ascii "X: z\rX"
  else if kind=14 then WireSpec.ascii "X: z" else if kind=15 then WireSpec.ascii "XX\r\n"
  else if kind=16 then WireSpec.ascii ": z\r\n"
  else if kind=17 then WireSpec.ascii "X: a"++[11#8]++WireSpec.ascii "\r\n"
  else if kind=18 then WireSpec.ascii "X: a"++[0#8]++WireSpec.ascii "\r\n"
  else WireSpec.ascii "X: a\tb\r\n"

def expected (kind : Fin 20) : HeadFieldLineSpec.Next :=
  if kind=0 then .header 7 (.ok 4 6 7) else if kind=1 then .done 2
  else if kind=2 then .bad 400 else if kind=3 then .header 11 (.bad 400)
  else if kind=4 then .header 5 (.bad 400) else if kind=5 then .header 7 (.ok 1 4 5)
  else if kind=6 then .header 3 (.bad 400) else if kind=7 then .header 3 (.ok 1 2 3)
  else if kind=8 then .header 2 (.ok 1 2 2) else if kind=9 then .header 4 (.ok 1 4 4)
  else if kind=10 then .header 4 (.bad 400) else if kind=11 then .more
  else if kind=12 ∨ kind=13 then .bad 400 else if kind=14 then .more
  else if kind=15 then .header 2 (.bad 400) else if kind=16 then .header 3 (.bad 400)
  else if kind=17 ∨ kind=18 then .header 5 (.bad 400) else .header 6 (.ok 1 3 6)

def core (kind : Fin 20) : Core :=
  ⟨0x80002f58#32,(fun r => if r=2 then sp else if r=16 then 10#32 else if r=17 then 13#32
    else if r=5 then 33#32 else if r=6 then 48#32 else if r=7 then 14#32
    else if r=28 then 58#32 else if r=27 then 91#32 else if r=8 then 1#32
    else if r=22 then 0#32-BitVec.ofNat 32 (input kind).length else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 20) : Word → BitVec 8 :=
  let base := fun a => if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec14+(input kind).length then
      (input kind)[a.toNat-0x80ffec14]?.getD 0#8 else ReadSendWitness.ram false false a
  let r0 := ramWrite base (sp+8#32) 1024#32 .w
  let r1 := ramWrite r0 (sp+12#32) (BitVec.ofNat 32 (input kind).length+0xffffffff#32) .w
  let r2 := ramWrite r1 (sp+16#32) ((sp+516#32)+1#32) .w
  let r3 := ramWrite r2 (sp+32#32) 9409#32 .w
  let r4 := ramWrite r3 (sp+36#32) 1024#32 .w
  let r5 := ramWrite r4 (sp+40#32) (BitVec.ofNat 32 (input kind).length) .w
  let r6 := ramWrite r5 (sp+44#32) (sp+516#32) .w
  let r7 := ramWrite r6 (sp+48#32) (BitVec.ofNat 32 (input kind).length) .w
  ramWrite r7 (sp+52#32) (sp+4904#32) .w

theorem regs (kind : Fin 20) : HeadFieldsRegs.At (core kind) sp 0 (input kind).length 1 Fields.empty := by
  constructor <;> rfl

theorem metadata (kind : Fin 20) : HeadFieldsMeta.At (ram kind) sp (input kind).length (input kind).length := by
  constructor <;> revert kind <;> decide +kernel

theorem bytes : ∀ kind : Fin 20, Bytes.At (ram kind) (sp+516#32) (input kind) := by
  unfold Bytes.At
  decide +kernel

theorem lengths : ∀ kind : Fin 20, 0<(input kind).length ∧ (input kind).length≤24 := by decide +kernel

theorem parsed : ∀ kind : Fin 20,
    HeadFieldLineSpec.next (HeadLineScanSpec.bytes (ram kind) (sp+516#32)) 0 (input kind).length=expected kind := by decide +kernel

def finish (kind : Fin 20) : Word :=
  if kind=0 ∨ kind=5 ∨ kind=7 ∨ kind=8 ∨ kind=9 ∨ kind=19 then 0x800030fa#32
  else if kind=1 then 0x80003456#32 else if kind=11 ∨ kind=14 then 0x800033ea#32 else 0x8000342c#32

def resultPc : HeadFieldLineSpec.Next → Word
  | .more => 0x800033ea#32
  | .bad _ => 0x8000342c#32
  | .done _ => 0x80003456#32
  | .header _ (.bad _) => 0x8000342c#32
  | .header _ (.ok _ _ _) => 0x800030fa#32

theorem at_pc (c : Core) (after : Word → BitVec 8) (r : HeadFieldLineSpec.Next)
    (atResult : HeadFieldLineSpec.At c after sp 0 r) : c.pc=resultPc r := by
  cases r with
  | more => exact atResult
  | bad _ => exact atResult.1
  | done _ => exact atResult.1
  | header _ parsed => cases parsed <;> exact atResult.1.1

theorem expected_pc : ∀ kind : Fin 20, resultPc (expected kind)=finish kind := by decide +kernel

theorem app (kind : Fin 20) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

/-- Twenty satisfiable real F58 loop entries exercise bounded line parsing,
    byte validation, trimming and every More/Bad/empty-line/header endpoint.
    This is not an end-to-end HTTP response or completed HeadR witness. -/
theorem execution (kind : Fin 20) : ∃ n d after, n≤1916 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=finish kind ∧
      HeadFieldLineSpec.At d after sp 0 (expected kind) ∧ AppState.At after Spec.initial := by
  obtain ⟨positive,bound⟩ := lengths kind
  obtain ⟨n,d,after,nlo,nhi,trace,result,region,metadataAfter,frame,csr⟩ := HeadFieldLine.contract B (core kind) (ram kind) sp 0 (input kind).length (input kind).length 1 Fields.empty
    (regs kind) (metadata kind) positive (by omega) (by omega) HeadEarlyWitness.stack (by decide +kernel)
  rw [parsed kind] at result
  refine ⟨n,d,after,by omega,Interrupt.close trace.det rfl,(at_pc d after (expected kind) result).trans (expected_pc kind),result,?_⟩
  apply AppState.preserve (ram kind) after Spec.initial (app kind)
  intro i
  have frame := region ⟨420+i.val,by have hi := i.isLt;omega⟩
  have addr : (sp+8#32)+BitVec.ofNat 32 (420+i.val)=0x80ffebbc#32+BitVec.ofNat 32 i.val := by
    rw [BitVec.ofNat_add,←BitVec.add_assoc];rfl
  simpa only [addr] using frame
end E5R.Thermostat.HeadFieldLineWitness
