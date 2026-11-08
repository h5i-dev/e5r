import Projects.thermostat.Upper
import Projects.thermostat.Stack
import Projects.thermostat.Dispatch
import Projects.thermostat.Outcome

set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Call
open E5R E5R.Thermostat

/-- Caller objects are disjoint from all 64 bytes of the callee's stack frame. -/
def Separate (c : Core) (p : Word) (n : Nat) : Prop :=
  ∀ i : Fin n, ∀ j : Fin 64, p+BitVec.ofNat 32 i.val ≠ Stack.base c+BitVec.ofNat 32 j.val

theorem separate_saved {c p n} (h : Separate c p n) (k : Fin n) (i : Fin 7) (j : Fin 4) :
    p+BitVec.ofNat 32 k.val ≠ Stack.base c+BitVec.ofNat 32 (60-4*i.val)+BitVec.ofNat 32 j.val := by
  have hi := i.isLt
  have hj := j.isLt
  have hb : 60-4*i.val+j.val < 64 := by omega
  simpa only [BitVec.ofNat_add,BitVec.add_assoc] using h k ⟨60-4*i.val+j.val,hb⟩

structure Pre (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) : Prop where
  pc : c.pc = 0x80000052
  stateRam : Memory.Block B (c.get 12) 10
  stateAlign : (c.get 12).toNat % 2 = 0
  commandRam : Memory.Block B (c.get 13) 4
  commandAlign : (c.get 13).toNat % 2 = 0
  actorRam : Memory.Block B (c.get 11) 1
  outRam : Memory.Block B (c.get 10) 20
  outAlign : (c.get 10).toNat % 2 = 0
  stackRam : Memory.Block B (Stack.base c) 64
  stackAlign : (Stack.base c).toNat % 4 = 0
  stateAt : Encoding.SnapshotAt ram (c.get 12) s
  commandAt : Encoding.CommandAt ram (c.get 13) cmd
  actorAt : ram (c.get 11) = Encoding.boolByte admin
  stateSep : Separate c (c.get 12) 10
  commandSep : Separate c (c.get 13) 4
  actorSep : Separate c (c.get 11) 1
  outSep : Separate c (c.get 10) 20

theorem stack_accessible {B c ram admin s cmd} (h : Pre B c ram admin s cmd) :
    Stack.Accessible B (Stack.base c) := by
  intro i
  have hi := i.isLt
  constructor
  · rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    have hp := (Stack.base c).isLt
    have hn := h.stackRam.2.2
    have ha := h.stackAlign
    omega
  · exact Memory.block_access (B := B) (p := Stack.base c) (n := 64) (off := 60-4*i.val) (width := 4)
      h.stackRam (by decide) (by omega)

structure Entered (before after : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) : Prop where
  pc : after.pc = Dispatch.entry (Encoding.tagFin cmd)
  outPtr : after.get 10 = before.get 10
  actorPtr : after.get 11 = before.get 11
  statePtr : after.get 12 = before.get 12
  commandPtr : after.get 13 = before.get 13
  sp : after.get 2 = Stack.base before
  csr : after.sameCsr before
  stateAt : Encoding.SnapshotAt (Stack.save before ram) (before.get 12) s
  commandAt : Encoding.CommandAt (Stack.save before ram) (before.get 13) cmd
  actorAt : Stack.save before ram (before.get 11) = Encoding.boolByte admin
  upper : Upper.Frame before after

theorem enter (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram admin s cmd) :
    ∃ n cd, n ≤ 15 ∧ DetSteps B img n ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩ ∧ Entered c cd ram admin s cmd := by
  obtain ⟨cp,hpRun,hpPc,hpSp,hpRegs,hpCsr⟩ := Stack.prologue B c ram h.pc (stack_accessible h)
  have hTag : Stack.save c ram (c.get 13) = BitVec.ofNat 8 (Encoding.tagFin cmd).val := by
    rw [Stack.save_frame c ram _ (by
      intro i j
      have he := separate_saved h.commandSep ⟨0,by decide⟩ i j
      simpa using he),Encoding.command_tag h.commandAt,Encoding.tag_fin]
  have hCmdRead : B.inRam (cp.get 13) 1 = true := by
    rw [hpRegs 13 (by decide)]
    simpa using Memory.block_access (B := B) (p := c.get 13) (n := 4) (off := 0) (width := 1)
      h.commandRam (by decide) (by decide)
  have hCmdPtr : cp.get 13 = c.get 13 := hpRegs 13 (by decide)
  obtain ⟨nd,cd,hn,hdRun,hdPc,hdRegs,hdCsr⟩ := Dispatch.contract B cp (Stack.save c ram)
    (Encoding.tagFin cmd) hpPc hCmdRead (by simpa only [hCmdPtr] using hTag)
  have hArg (r : Reg) (h2 : r ≠ 2) (h14 : r ≠ 14) (h15 : r ≠ 15) : cd.get r = c.get r :=
    (hdRegs r h14 h15).trans (hpRegs r h2)
  refine ⟨8+nd,cd,by omega,hpRun.trans hdRun,?_⟩
  refine ⟨hdPc,hArg 10 (by decide) (by decide) (by decide),hArg 11 (by decide) (by decide) (by decide),
    hArg 12 (by decide) (by decide) (by decide),hArg 13 (by decide) (by decide) (by decide),
    (hdRegs 2 (by decide) (by decide)).trans hpSp,hdCsr.trans hpCsr,?_,?_,?_,?_⟩
  · intro k
    rw [Stack.save_frame c ram _ (separate_saved h.stateSep k)]
    exact h.stateAt k
  · apply Encoding.command_preserve ram (Stack.save c ram) (c.get 13) cmd h.commandAt
    intro k
    exact Stack.save_frame c ram _ (separate_saved h.commandSep k)
  · rw [Stack.save_frame c ram _ (by
      intro i j
      have he := separate_saved h.actorSep ⟨0,by decide⟩ i j
      simpa using he)]
    exact h.actorAt
  · intro r hr
    exact hArg r (Upper.ne_low r hr 2 (by decide)) (Upper.ne_low r hr 14 (by decide)) (Upper.ne_low r hr 15 (by decide))


/-- The kernel's exact output representation, return and caller-memory frame.
    Saved names are ra,s0..s5, the registers this function spills. -/
structure Post (before : Core) (ram : Word → BitVec 8) (after : Machine)
    (res : Except Spec.Error Spec.Success) : Prop where
  pc : after.core.pc = before.get 1 &&& ~~~1
  sp : after.core.get 2 = before.get 2
  saved : ∀ i : Fin 7, after.core.get (Stack.reg i) = before.get (Stack.reg i)
  csr : after.core.sameCsr before
  outcome : Outcome.At after.ram (before.get 10) res
  frame : ∀ x, (∀ k : Fin 20, x ≠ before.get 10+BitVec.ofNat 32 k.val) →
    (∀ k : Fin 64, x ≠ Stack.base before+BitVec.ofNat 32 k.val) → after.ram x = ram x

  upper : Upper.Frame before after.core

/-- Sound composition with the actual epilogue; the body proof is supplied
    separately for each command arm, never assumed in a completed arm theorem. -/

theorem finish (B : Board) (c cd cb : Core) (ram ram' : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Except Spec.Error Spec.Success)
    (npre nbody : Nat) (h : Pre B c ram admin s cmd)
    (hpre : DetSteps B img npre ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩)
    (hbody : DetSteps B img nbody ⟨cd,Stack.save c ram⟩ ⟨cb,ram'⟩)
    (hpc : cb.pc = 0x800001ac) (hsp : cb.get 2 = Stack.base c) (hcsr : cb.sameCsr c)
    (hupper : Upper.Frame c cb)
    (houtcome : Outcome.At ram' (c.get 10) res)
    (hframe : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → ram' x = Stack.save c ram x) :
    ∃ d, DetSteps B img (npre+nbody+9) ⟨c,ram⟩ ⟨d,ram'⟩ ∧ Post c ram ⟨d,ram'⟩ res := by
  have hSaved : ∀ i : Fin 7,
      ramRead ram' (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w = c.get (Stack.reg i) := by
    intro i
    calc
      ramRead ram' (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w =
          ramRead (Stack.save c ram) (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w := by
        apply ramRead_w_congr
        intro k hk
        apply hframe
        intro j
        exact Ne.symm (separate_saved h.outSep j i ⟨k,hk⟩)
      _ = c.get (Stack.reg i) := Stack.saved_word c ram i
  obtain ⟨d,hr,hpc',hsp',hsaved,hregs,hcsr'⟩ := Stack.epilogue B c cb ram' hpc hsp (stack_accessible h) hSaved
  refine ⟨d,(hpre.trans hbody).trans hr,hpc',hsp',hsaved,hcsr'.trans hcsr,houtcome,?_,?_⟩
  · intro x hout hstack
    change ram' x = ram x
    rw [hframe x hout]
    apply Stack.save_frame
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hb : 60-4*i.val+j.val < 64 := by omega
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hstack ⟨60-4*i.val+j.val,hb⟩

  · intro r hr
    exact (hregs r (Upper.ne_low r hr 1 (by decide)) (Upper.ne_low r hr 2 (by decide)) (Upper.ne_low r hr 8 (by decide)) (Upper.ne_low r hr 9 (by decide)) (Upper.ne_low r hr 18 (by decide)) (Upper.ne_low r hr 19 (by decide)) (Upper.ne_low r hr 20 (by decide)) (Upper.ne_low r hr 21 (by decide))).trans (hupper r hr)

/-- Composition allowing local bytes 0..35 while protecting spilled registers. -/
theorem finish_local (B : Board) (c cd cb : Core) (ram ram' : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Except Spec.Error Spec.Success)
    (npre nbody : Nat) (h : Pre B c ram admin s cmd)
    (hpre : DetSteps B img npre ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩)
    (hbody : DetSteps B img nbody ⟨cd,Stack.save c ram⟩ ⟨cb,ram'⟩)
    (hpc : cb.pc = 0x800001ac) (hsp : cb.get 2 = Stack.base c) (hcsr : cb.sameCsr c)
    (hupper : Upper.Frame c cb)
    (houtcome : Outcome.At ram' (c.get 10) res)
    (hframe : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 36, x ≠ Stack.base c+BitVec.ofNat 32 i.val) → ram' x = Stack.save c ram x) :
    ∃ d, DetSteps B img (npre+nbody+9) ⟨c,ram⟩ ⟨d,ram'⟩ ∧ Post c ram ⟨d,ram'⟩ res := by
  have hSaved : ∀ i : Fin 7,
      ramRead ram' (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w = c.get (Stack.reg i) := by
    intro i
    calc
      ramRead ram' (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w =
          ramRead (Stack.save c ram) (Stack.base c+BitVec.ofNat 32 (60-4*i.val)) .w := by
        apply ramRead_w_congr
        intro k hk
        apply hframe
        · intro j
          exact Ne.symm (separate_saved h.outSep j i ⟨k,hk⟩)
        · intro j he
          simp only [BitVec.add_assoc,BitVec.add_right_inj] at he
          have hn := congrArg BitVec.toNat he
          simp only [BitVec.toNat_add,BitVec.toNat_ofNat] at hn
          have hi := i.isLt
          have hj := j.isLt
          omega
      _ = c.get (Stack.reg i) := Stack.saved_word c ram i
  obtain ⟨d,hr,hpc',hsp',hsaved,hregs,hcsr'⟩ := Stack.epilogue B c cb ram' hpc hsp (stack_accessible h) hSaved
  refine ⟨d,(hpre.trans hbody).trans hr,hpc',hsp',hsaved,hcsr'.trans hcsr,houtcome,?_,?_⟩
  · intro x hout hstack
    change ram' x = ram x
    have hlocal : ∀ i : Fin 36, x ≠ Stack.base c+BitVec.ofNat 32 i.val := by
      intro i
      exact hstack ⟨i.val,by have := i.isLt;omega⟩
    rw [hframe x hout hlocal]
    apply Stack.save_frame
    intro i j
    have hi := i.isLt
    have hj := j.isLt
    have hb : 60-4*i.val+j.val < 64 := by omega
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hstack ⟨60-4*i.val+j.val,hb⟩
  · intro r hr
    exact (hregs r (Upper.ne_low r hr 1 (by decide)) (Upper.ne_low r hr 2 (by decide)) (Upper.ne_low r hr 8 (by decide)) (Upper.ne_low r hr 9 (by decide)) (Upper.ne_low r hr 18 (by decide)) (Upper.ne_low r hr 19 (by decide)) (Upper.ne_low r hr 20 (by decide)) (Upper.ne_low r hr 21 (by decide))).trans (hupper r hr)

end E5R.Thermostat.Call
