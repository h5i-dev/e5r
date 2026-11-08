import Projects.thermostat.UartTxPoll
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.UartTxWait
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def read (status : Word) : Observed.Read := ⟨0x10000005#32,.b,UartPoll.byte status,0⟩
def log (statuses : List Word) : List Observed.Read := statuses.map read

theorem cycle (c : Core) (ram : Word → BitVec 8) (status : Word)
    (hp : c.pc=0x800007f8#32) (hu : c.get 13=0x10000000#32) (hz : UartTxPoll.mask status=0#32) :
    ∃ d, Observed.Steps B img 5 ⟨c,ram⟩ ⟨d,ram⟩ [read status] [] ∧ d.pc=0x800007f8#32 ∧
      d.get 17=0#32 ∧ (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,a17,ar,ac⟩ := UartTxPoll.test c ram status false hp hu (by rw [hz];decide)
  have pa' : a.pc=0x80000804#32 := by simpa only [Bool.false_eq_true,ite_false] using pa
  let b := a.goto 0x80000808#32
  let d := b.goto 0x800007f8#32
  have tb : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨a,ram⟩) (by rw [pa'];decide) (by rw [pa'];exact up2147485700)
    change Eff.done (a.goto (a.pc+4#32))=.done b
    rw [pa'];rfl
  have td : Observed.Step B img ⟨b,ram⟩ ⟨d,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨b,ram⟩) (by change (0x80000808#32).getLsbD 0=false;decide) up2147485704
    rw [exec_jal]
    change jump b (0x80000808#32+0xfffffff0#32)=.done d
    rw [show 0x80000808#32+0xfffffff0#32=0x800007f8#32 by decide +kernel,jump_ok _ _ (by decide)]
  refine ⟨d,?_,rfl,a17.trans hz,ar,ac⟩
  simpa only [read,List.append_nil,Nat.reduceAdd] using (ta.trans (.single tb)).trans (.single td)

/-- Any finite prefix of not-ready LSR values has an exact silent execution.
    It consumes status reads only and leaves RAM and every other register. -/
theorem wait_prefix (c : Core) (ram : Word → BitVec 8) (statuses : List Word)
    (hp : c.pc=0x800007f8#32) (hu : c.get 13=0x10000000#32)
    (hz : ∀ v ∈ statuses, UartTxPoll.mask v=0#32) :
    ∃ d, Observed.Steps B img (5*statuses.length) ⟨c,ram⟩ ⟨d,ram⟩ (log statuses) [] ∧ d.pc=0x800007f8#32 ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  induction statuses generalizing c with
  | nil => exact ⟨c,.refl _,hp,fun _ _ => rfl,Core.sameCsr_refl c⟩
  | cons v vs ih =>
    obtain ⟨a,ta,pa,_,ar,ac⟩ := cycle c ram v hp hu (hz v (by simp))
    obtain ⟨d,td,pd,dr,dc⟩ := ih a pa ((ar 13 (by decide)).trans hu) (fun v hv => hz v (by simp [hv]))
    refine ⟨d,?_,pd,fun r hr => (dr r hr).trans (ar r hr),dc.trans ac⟩
    simpa only [log,List.map_cons,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm,List.singleton_append,List.append_nil] using ta.trans td

/-- Conditional progress for precisely a finite not-ready schedule followed
    by one ready status. No bound or fairness is asserted for the environment. -/
theorem ready_after (c : Core) (ram : Word → BitVec 8) (statuses : List Word) (last : Word)
    (hp : c.pc=0x800007f8#32) (hu : c.get 13=0x10000000#32)
    (hz : ∀ v ∈ statuses, UartTxPoll.mask v=0#32) (hr : UartTxPoll.mask last≠0#32) :
    ∃ d, Observed.Steps B img (5*statuses.length+3) ⟨c,ram⟩ ⟨d,ram⟩ (log (statuses++[last])) [] ∧
      d.pc=0x800007ea#32 ∧ d.get 17=UartTxPoll.mask last ∧
      (∀ r : Reg, r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨a,ta,pa,ar,ac⟩ := wait_prefix c ram statuses hp hu hz
  obtain ⟨d,td,pd,d17,dr,dc⟩ := UartTxPoll.test a ram last true pa ((ar 13 (by decide)).trans hu)
    (by simp [taken,hr])
  refine ⟨d,?_,by simpa only [ite_true] using pd,d17,fun r hr => (dr r hr).trans (ar r hr),dc.trans ac⟩
  simpa only [log,read,List.map_append,List.map_cons,List.map_nil,List.nil_append] using ta.trans td

theorem no_input (statuses : List Word) : Observed.input (log statuses)=[] := by
  induction statuses with
  | nil => rfl
  | cons v vs ih => simpa [log,Observed.input,read] using ih
end E5R.Thermostat.UartTxWait
