import Projects.thermostat.HeadHeaderCommit
import Projects.thermostat.HeadEarlyWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeadHeaderCommitWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev sp := HeadEarlyWitness.sp

def count (kind : Fin 4) : Nat := if kind.val<2 then 0 else 15
def te (kind : Fin 4) : Bool := decide (kind.val%2=1)
def cap (kind : Fin 4) : Nat := if kind.val%2=0 then 21 else 14
def entry : Field := ⟨7,8,9,12⟩
def oldEntry : Field := ⟨0,1,2,3⟩
def fields (kind : Fin 4) : Fields :=
  ⟨List.replicate (count kind) oldEntry,true,!(te kind),(if te kind then 0 else 1024),te kind⟩

def core (kind : Fin 4) : Core :=
  ⟨0x800033b6#32,(fun r => if r=2 then sp else if r=16 then 10#32 else if r=17 then 13#32
    else if r=5 then 33#32 else if r=6 then 48#32 else if r=7 then 14#32
    else if r=28 then 58#32 else if r=27 then 91#32 else if r=8 then 1#32
    else if r=22 then 0#32-32#32 else if r=9 then BitVec.ofNat 32 (count kind)
    else if r=24 then 7#32 else if r=15 then 9#32 else if r=25 then 12#32
    else if r=21 then 5#32 else if r=23 then 2#32 else if r=1 then 400#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Fin 4) : Word → BitVec 8 :=
  let base := fun a => if 0x80ffea48≤a.toNat ∧ a.toNat<0x80ffeb48 then
      let byte := (a.toNat-0x80ffea48)%16
      if byte=4 then 1#8 else if byte=8 then 2#8 else if byte=12 then 3#8 else 0#8
    else ReadSendWitness.ram false false a
  let r0 := ramWrite base (sp+4#32) 8#32 .w
  let r1 := ramWrite r0 (sp+8#32) 1024#32 .w
  let r2 := ramWrite r1 (sp+12#32) 31#32 .w
  let r3 := ramWrite r2 (sp+16#32) ((sp+516#32)+1#32) .w
  let r4 := ramWrite r3 (sp+32#32) 9409#32 .w
  let r5 := ramWrite r4 (sp+36#32) 1024#32 .w
  let r6 := ramWrite r5 (sp+40#32) (BitVec.ofNat 32 (cap kind)) .w
  let r7 := ramWrite r6 (sp+44#32) (sp+516#32) .w
  let r8 := ramWrite r7 (sp+48#32) 32#32 .w
  let r9 := ramWrite r8 (sp+52#32) (sp+4904#32) .w
  let r10 := ramWrite r9 (sp+312#32) (BitVec.ofNat 32 (fields kind).cl) .w
  let r11 := ramWrite r10 (sp+316#32) 0#32 .w
  let r12 := ramWrite r11 (sp+320#32) (BitVec.ofNat 32 (count kind)) .w
  let r13 := ramWrite r12 (sp+324#32) 1#32 .b
  let r14 := ramWrite r13 (sp+325#32) (if te kind then 0#32 else 1#32) .b
  ramWrite r14 (sp+326#32) (if te kind then 1#32 else 0#32) .b

theorem constants (kind : Fin 4) : HeadFieldsConstants.At (core kind) sp 32 1 := by constructor <;> rfl

theorem metadata (kind : Fin 4) : HeadFieldsMeta.At (ram kind) sp 32 (cap kind) := by
  constructor <;> revert kind <;> decide +kernel

theorem fields_view (kind : Fin 4) : HeadFieldsView.At (ram kind) sp (fields kind) := by
  constructor <;> revert kind <;> decide +kernel

theorem name_word : ∀ kind : Fin 4, ramRead (ram kind) (sp+4#32) .w=8#32 := by decide +kernel
theorem room : ∀ kind : Fin 4, (fields kind).headers.length<16 := by decide +kernel
theorem capacities : ∀ kind : Fin 4, 12≤cap kind ∧ cap kind≤32 := by decide +kernel

theorem app (kind : Fin 4) : AppState.At (ram kind) Spec.initial := by
  constructor
  all_goals try unfold Encoding.SnapshotAt
  all_goals revert kind
  all_goals decide +kernel

def finish (kind : Fin 4) : Word := if kind.val%2=0 then 0x80002f58#32 else 0x800033ea#32

theorem branch_test : ∀ kind : Fin 4, decide (12+2<cap kind)=decide (kind.val%2=0) := by decide +kernel

/-- Four satisfiable internal commit states cover slots0/15 and both loop/More
    endpoints. An intentionally stale TE register2 is replaced by the actual
    RAM boolean before the guard. These are not reset-reachability witnesses. -/
theorem execution (kind : Fin 4) : ∃ d after,
    Trace.Closed B img 18 ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=finish kind ∧
      d.get 2=sp ∧ d.get 23=(if te kind then 1#32 else 0#32) ∧
      HeadFieldsView.At after sp {fields kind with headers := (fields kind).headers++[entry]} ∧
      ramRead after (sp+320#32) .w=BitVec.ofNat 32 ((fields kind).headers.length+1) ∧
      ramRead after (sp+312#32) .w=BitVec.ofNat 32 (fields kind).cl ∧ AppState.At after Spec.initial := by
  have h9 : (core kind).get 9=BitVec.ofNat 32 (fields kind).headers.length := by
    simp only [fields,List.length_replicate]
    rfl
  obtain ⟨lo,hi⟩ := capacities kind
  obtain ⟨d,trace,next,view,metaAfter,countAfter,posAfter,teAfter,frame,csr⟩ := HeadHeaderCommit.contract B (core kind) (ram kind) sp entry 12 32 (cap kind) 1 (fields kind)
    rfl (constants kind) (fields_view kind) (metadata kind) h9 rfl rfl rfl rfl (name_word kind) (room kind)
    (by decide) lo hi (by decide) HeadEarlyWitness.stack (by decide +kernel)
  let after := HeadHeaderCommitMemory.memory (ram kind) sp (fields kind).headers.length entry
  refine ⟨d,after,Interrupt.close trace.det rfl,?_,(frame 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),teAfter,view,
    HeadHeaderCommitMemory.count_word (ram kind) sp (fields kind).headers.length entry,view.clLow,?_⟩
  · by_cases more : 12+2<cap kind
    · have atLoop : d.pc=0x80002f58#32 := (by simpa only [more,ite_true] using next : HeadFieldsRegs.At d sp 14 32 1 _).pc
      have chosen : kind.val%2=0 := of_decide_eq_true ((branch_test kind).symm.trans (decide_eq_true more))
      simpa only [finish,chosen,ite_true] using atLoop
    · have atMore : d.pc=0x800033ea#32 := by simpa only [more,ite_false] using next
      have chosen : ¬kind.val%2=0 := of_decide_eq_false ((branch_test kind).symm.trans (decide_eq_false more))
      simpa only [finish,chosen,ite_false] using atMore
  · apply AppState.preserve (ram kind) after Spec.initial (app kind)
    have region := HeadHeaderCommitMemory.region (ram kind) sp (fields kind).headers.length entry 428 25 (room kind) (by decide) (by have := room kind;omega) (by decide)
    simpa only [ViewFrame.Region,show sp+428#32=0x80ffebbc#32 by decide +kernel] using region
end E5R.Thermostat.HeadHeaderCommitWitness
