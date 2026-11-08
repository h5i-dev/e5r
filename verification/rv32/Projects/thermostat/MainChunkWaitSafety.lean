import Projects.thermostat.MainChunkPoll
import Projects.thermostat.MainChunkRbr
import Projects.thermostat.Interrupt
namespace E5R.Thermostat.MainChunkWaitSafety
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def Waiting (c : Core) : Prop :=
  c.pc=0x80000fb0#32 ∨ c.pc=0x80000fb4#32 ∨ c.pc=0x80000fb6#32 ∨
  c.pc=0x80000fba#32 ∨ c.pc=0x80000fbe#32

def At (c : Core) : Prop := Waiting c ∧ c.get 19=0x10000000#32 ∧ c.mie_=false

def Exit (c : Core) : Prop := c.pc=0x80000e80#32 ∧ c.get 19=0x10000000#32 ∧ c.mie_=false

def LsrOnly (reads : List Observed.Read) : Prop := reads=[] ∨
  ∃ v, reads=[⟨0x10000005#32,.b,v,0⟩]

/-- Every oracle choice in the actual wait region is safe. The result may
    remain waiting forever; no input arrival or readiness is assumed here. -/
theorem next {c : Core} (ram : Word → BitVec 8) (h : At c) (o : Oracle) :
    ∃ d reads, Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (At d ∨ Exit d) ∧ LsrOnly reads ∧
      (∀ r : Reg, r≠11 → d.get r=c.get r) ∧ d.sameCsr c := by
  rcases h with ⟨hp,hu,hm⟩
  rcases hp with hp|hp|hp|hp|hp
  · let d := c.wr 11 (UartPoll.byte (o 0)) 0x80000fb4#32
    refine ⟨d,_,MainChunkPoll.load c ram o hp hu,Or.inl ⟨Or.inr (Or.inl rfl),?_,hm⟩,
      Or.inr ⟨_,rfl⟩,?_,rfl⟩
    · simpa only [d,Core.wr_get_ne _ _ _ _ _ (by decide : (19:Reg)≠11)] using hu
    · intro r hr;exact Core.wr_get_ne _ _ _ _ _ hr
  · let d := c.wr 11 (c.get 11 &&& 1#32) 0x80000fb6#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)),?_,hm⟩,Or.inl rfl,?_,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact cr2147487668),exec_opimm,hp]
      rfl
    · simpa only [d,Core.wr_get_ne _ _ _ _ _ (by decide : (19:Reg)≠11)] using hu
    · intro r hr;exact Core.wr_get_ne _ _ _ _ _ hr
  · let ready := taken .ne (c.get 11) (0 : Word)
    let d := c.goto (if ready then 0x80000e80#32 else 0x80000fba#32)
    refine ⟨d,[],?_,?_,Or.inl rfl,fun _ _ => rfl,rfl⟩
    · rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact cr2147487670),exec_branch,Core.get_zero,hp]
      cases he : ready with
      | false => change Observed.interp B img o (if ready=true then _ else _) ram 0 [] []=_;rw [he];simp only [d,he];rfl
      | true =>
        change Observed.interp B img o (if ready=true then _ else _) ram 0 [] []=_
        rw [he]
        simp only [ite_true]
        rw [show 0x80000fb6#32+0xfffffeca#32=0x80000e80#32 by decide +kernel,jump_ok _ _ (by decide)]
        simp only [d,he,ite_true]
        rfl
    · cases he : ready with
      | false => exact Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inl (by simp [d,he])))),hu,hm⟩
      | true => exact Or.inr ⟨by simp [d,he],hu,hm⟩
  · let d := c.goto 0x80000fbe#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inr (Or.inr (Or.inr (Or.inr rfl))),hu,hm⟩,
      Or.inl rfl,fun _ _ => rfl,rfl⟩
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact cr2147487674)]
    change Observed.interp B img o (Eff.done (c.goto (c.pc+4#32))) ram 0 [] []=_
    rw [hp,show 0x80000fba#32+4#32=0x80000fbe#32 by decide +kernel]
    rfl
  · let d := c.goto 0x80000fb0#32
    refine ⟨d,[],?_,Or.inl ⟨Or.inl rfl,hu,hm⟩,Or.inl rfl,fun _ _ => rfl,rfl⟩
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact cr2147487678),exec_jal,Core.set_zero,hp]
    rw [show 0x80000fbe#32+0xfffffff2#32=0x80000fb0#32 by decide +kernel,jump_ok _ _ (by decide)]
    rfl

theorem safe {c ram} (h : At c) : ¬Escapes B img ⟨c,ram⟩ := by
  rintro (⟨o,f,hf⟩|⟨code,e,enabled,_⟩)
  · obtain ⟨d,reads,he,_⟩ := next ram h o
    have erase := Observed.erase_step B img ⟨c,ram⟩ o
    rw [he] at erase
    rw [←erase] at hf
    cases hf
  · simp [irqEnabled,h.2.2] at enabled

/-- Every actual platform/IRQ-aware observed step remains in the wait
    invariant or reaches the ready cutpoint. Only LSR reads occur here. -/
theorem step {c ram d reads evs} (h : At c)
    (actual : Observed.Step B img ⟨c,ram⟩ d reads evs) :
    d.ram=ram ∧ (At d.core ∨ Exit d.core) ∧ LsrOnly reads ∧ evs=[] := by
  cases actual with
  | instr o he =>
    obtain ⟨e,log,hk,post,only,frame,csr⟩ := next ram h o
    rw [hk] at he
    cases he
    exact ⟨rfl,post,by simpa only [hk] using only,rfl⟩
  | irq code enabled _ => simp [irqEnabled,h.2.2] at enabled
theorem exit_safe {c ram} (h : Exit c) : ¬Escapes B img ⟨c,ram⟩ := by
  rintro (⟨o,f,hf⟩|⟨code,e,enabled,_⟩)
  · have he := MainChunkRbr.load c ram o h.1 h.2.1
    have erase := Observed.erase_step B img ⟨c,ram⟩ o
    rw [he] at erase
    rw [←erase] at hf
    cases hf
  · simp [irqEnabled,h.2.2] at enabled

/-- Actual execution prefixes stopped at the first ready cutpoint. The
    constructor requires the source PC still to be inside the wait region. -/
inductive Run (start : Machine) : Machine → List Observed.Read → Prop
  | init : At start.core → Run start start []
  | step {m d old reads evs} : Run start m old → At m.core →
      Observed.Step B img m d reads evs → Run start d (old++reads)

theorem run_observed {start m reads} (h : Run start m reads) :
    Observed.Reach B img (fun e => e=start ∧ At e.core) m reads [] := by
  induction h with
  | init hs => exact .init ⟨rfl,hs⟩
  | step path waiting actual ih =>
    obtain ⟨ram,post,only,evs⟩ := step waiting actual
    rw [evs] at actual
    simpa only [List.append_nil] using Observed.Reach.step ih actual

theorem run_invariant {start m reads} (h : Run start m reads) :
    m.ram=start.ram ∧ (At m.core ∨ Exit m.core) ∧
      (∀ r ∈ reads, r.addr=0x10000005#32 ∧ r.width=.b ∧ r.oracleIndex=0) := by
  induction h with
  | init hs => exact ⟨rfl,Or.inl hs,by simp⟩
  | step path waiting actual ih =>
    obtain ⟨ram,post,only,evs⟩ := step waiting actual
    refine ⟨ram.trans ih.1,post,?_⟩
    intro r hr
    rcases List.mem_append.mp hr with old|new
    · exact ih.2.2 r old
    · rcases only with hz|⟨v,hv⟩
      · rw [hz] at new;contradiction
      · rw [hv] at new
        have eq := List.mem_singleton.mp new
        rw [eq]
        exact ⟨rfl,rfl,rfl⟩

/-- Unconditional safety up to readiness, even for arbitrarily many repeated
    not-ready polls. This is distinct from the finite readiness progress proof. -/
theorem fragment_safety {start m reads} (h : Run start m reads) :
    E5R.Reach B img (fun e => e=start ∧ At e.core) m [] ∧ m.ram=start.ram ∧
      (At m.core ∨ Exit m.core) ∧ ¬Escapes B img m ∧
      (∀ r ∈ reads, r.addr=0x10000005#32 ∧ r.width=.b ∧ r.oracleIndex=0) := by
  obtain ⟨ram,post,only⟩ := run_invariant h
  refine ⟨Observed.reach_erase (run_observed h),ram,post,?_,only⟩
  rcases post with inside|exit
  · exact safe inside
  · exact exit_safe exit

end E5R.Thermostat.MainChunkWaitSafety
