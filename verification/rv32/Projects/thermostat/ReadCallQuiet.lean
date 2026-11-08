-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ReadCall
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CallQuiet
import Projects.thermostat.ReadBodyQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
open E5R E5R.Thermostat
namespace E5R.Thermostat.ReadCall
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (admin : Bool) (s : Spec.Snapshot)
    (h : Call.Pre B c ram admin s .read) :
    ∃ n m, n ≤ 37 ∧ Quiet.Steps B img n ⟨c,ram⟩ m ∧ Call.Post c ram m (Spec.transition admin s .read) := by
  obtain ⟨ne,cd,hne,heRun,he⟩ := E5R.Thermostat.Call.enter_quiet B c ram admin s .read h
  let r0 := Stack.save c ram
  have hOut10 : Memory.Block B (c.get 10+10#32) 10 :=
    Memory.sub_block (B := B) (p := c.get 10) (n := 20) (off := 10) (m := 10) h.outRam (by decide) (by decide)
  have hOut0 : B.inRam (c.get 10) 1 = true := by
    simpa using Memory.block_access (B := B) (p := c.get 10) (n := 20) (off := 0) (width := 1)
      h.outRam (by decide) (by decide)
  obtain ⟨cb,hbRun,hbPc,hbRegs,hbCsr⟩ := E5R.Thermostat.ReadBody.contract_quiet B cd r0 (c.get 12) (c.get 10)
    (by exact he.pc) he.statePtr he.outPtr (Memory.half_block h.stateRam h.stateAlign)
    (Memory.half_block hOut10 (Memory.half_aligned (c.get 10) 5 h.outAlign)) hOut0
  let r' := ReadBody.result r0 (c.get 12) (c.get 10)
  have hOutcome : Outcome.At r' (c.get 10) (Spec.transition admin s .read) :=
    ⟨ReadBody.none r0 (c.get 12) (c.get 10),ReadBody.reply r0 (c.get 12) (c.get 10) s he.stateAt⟩
  have hSp : cb.get 2 = Stack.base c :=
    (hbRegs 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans he.sp
  have hFrame : ∀ x, (∀ i : Fin 20, x ≠ c.get 10+BitVec.ofNat 32 i.val) → r' x = r0 x :=
    fun x hx => ReadBody.frame r0 (c.get 12) (c.get 10) x hx
  obtain ⟨d,hrun,hpost⟩ := E5R.Thermostat.Call.finish_quiet B c cd cb ram r' admin s .read (Spec.transition admin s .read)
    ne 13 h heRun hbRun hbPc hSp (hbCsr.trans he.csr) (Upper.trans he.upper (fun r hr => hbRegs r (Upper.ne_low r hr 11 (by decide)) (Upper.ne_low r hr 12 (by decide)) (Upper.ne_low r hr 13 (by decide)) (Upper.ne_low r hr 14 (by decide)) (Upper.ne_low r hr 15 (by decide)) (Upper.ne_low r hr 16 (by decide)))) hOutcome hFrame
  exact ⟨ne+13+9,⟨d,r'⟩,by omega,hrun,hpost⟩

end E5R.Thermostat.ReadCall
