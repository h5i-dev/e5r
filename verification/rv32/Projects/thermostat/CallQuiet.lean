-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.Call
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.DispatchQuiet
import Projects.thermostat.StackQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.Call
theorem enter_quiet (B : Board) (c : Core) (ram : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (h : Pre B c ram admin s cmd) :
    ∃ n cd, n ≤ 15 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩ ∧ Entered c cd ram admin s cmd := by
  obtain ⟨cp,hpRun,hpPc,hpSp,hpRegs,hpCsr⟩ := E5R.Thermostat.Stack.prologue_quiet B c ram h.pc (stack_accessible h)
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
  obtain ⟨nd,cd,hn,hdRun,hdPc,hdRegs,hdCsr⟩ := E5R.Thermostat.Dispatch.contract_quiet B cp (Stack.save c ram)
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

end E5R.Thermostat.Call
namespace E5R.Thermostat.Call
theorem finish_quiet (B : Board) (c cd cb : Core) (ram ram' : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Except Spec.Error Spec.Success)
    (npre nbody : Nat) (h : Pre B c ram admin s cmd)
    (hpre : Quiet.Steps B img npre ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩)
    (hbody : Quiet.Steps B img nbody ⟨cd,Stack.save c ram⟩ ⟨cb,ram'⟩)
    (hpc : cb.pc = 0x800001ac) (hsp : cb.get 2 = Stack.base c) (hcsr : cb.sameCsr c)
    (hupper : Upper.Frame c cb)
    (houtcome : Outcome.At ram' (c.get 10) res)
    (hframe : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → ram' x = Stack.save c ram x) :
    ∃ d, Quiet.Steps B img (npre+nbody+9) ⟨c,ram⟩ ⟨d,ram'⟩ ∧ Post c ram ⟨d,ram'⟩ res := by
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
  obtain ⟨d,hr,hpc',hsp',hsaved,hregs,hcsr'⟩ := E5R.Thermostat.Stack.epilogue_quiet B c cb ram' hpc hsp (stack_accessible h) hSaved
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

end E5R.Thermostat.Call
namespace E5R.Thermostat.Call
theorem finish_local_quiet (B : Board) (c cd cb : Core) (ram ram' : Word → BitVec 8)
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command) (res : Except Spec.Error Spec.Success)
    (npre nbody : Nat) (h : Pre B c ram admin s cmd)
    (hpre : Quiet.Steps B img npre ⟨c,ram⟩ ⟨cd,Stack.save c ram⟩)
    (hbody : Quiet.Steps B img nbody ⟨cd,Stack.save c ram⟩ ⟨cb,ram'⟩)
    (hpc : cb.pc = 0x800001ac) (hsp : cb.get 2 = Stack.base c) (hcsr : cb.sameCsr c)
    (hupper : Upper.Frame c cb)
    (houtcome : Outcome.At ram' (c.get 10) res)
    (hframe : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 36, x ≠ Stack.base c+BitVec.ofNat 32 i.val) → ram' x = Stack.save c ram x) :
    ∃ d, Quiet.Steps B img (npre+nbody+9) ⟨c,ram⟩ ⟨d,ram'⟩ ∧ Post c ram ⟨d,ram'⟩ res := by
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
  obtain ⟨d,hr,hpc',hsp',hsaved,hregs,hcsr'⟩ := E5R.Thermostat.Stack.epilogue_quiet B c cb ram' hpc hsp (stack_accessible h) hSaved
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
