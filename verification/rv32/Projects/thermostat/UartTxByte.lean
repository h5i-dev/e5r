import Projects.thermostat.UartTxCode
import Projects.thermostat.ObservedByte
import Projects.thermostat.UartStore
namespace E5R.Thermostat.UartTxByte
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def word (v : BitVec 8) : Word := v.setWidth 32

theorem word_mask (v : BitVec 8) : devVal .b (word v)=word v := by
  have hh := ReadBytes.extend_byte v
  simpa only [word,Memory.ofNat_width,devVal,extend] using hh

theorem output (v : BitVec 8) : Observed.output [⟨0x10000000#32,word v⟩]=[v] := by
  change [(v.setWidth 32).setWidth 8]=[v]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth]
  have hv := v.isLt
  omega

theorem load (c : Core) (ram : Word → BitVec 8) (src : Word) (v : BitVec 8)
    (hp : c.pc=0x800007f4#32) (h12 : c.get 12=src) (hs : ReadBytes.Byte B img ram src v) :
    Observed.Step B img ⟨c,ram⟩ ⟨c.wr 16 (word v) 0x800007f8#32,ram⟩ [] [] := by
  have hk (o : Oracle) : Observed.stepInstr B img ⟨c,ram⟩ o = ⟨.ok (c.wr 16 (word v) 0x800007f8#32) ram [],[]⟩ := by
    rw [Observed.stepInstr_of (by rw [hp];decide) (by rw [hp];exact tx2147485684),exec_load,h12,BitVec.add_zero,
      ObservedByte.load hs o _ 0 [] [],ReadBytes.extend_byte,hp]
    rfl
  have ho : Oracle := fun _ => 0#32
  have ht : Observed.Step B img ⟨c,ram⟩ ⟨c.wr 16 (word v) 0x800007f8#32,ram⟩ (Observed.stepInstr B img ⟨c,ram⟩ ho).reads [] :=
    .instr ho (by rw [hk])
  simpa only [hk] using ht

/-- Actual source-pointer increment, UART THR SB and final/next-byte branch.
    The only output event is exactly the source byte. RAM is unchanged. -/
theorem emit (c : Core) (ram : Word → BitVec 8) (src finish : Word) (v : BitVec 8) (last : Bool)
    (hp : c.pc=0x800007ea#32) (h12 : c.get 12=src) (h14 : c.get 14=finish)
    (h15 : c.get 15=0x10000000#32) (h16 : c.get 16=word v)
    (ht : taken .eq (src+1#32) finish=last) :
    ∃ d, Observed.Steps B img 3 ⟨c,ram⟩ ⟨d,ram⟩ [] [⟨0x10000000#32,word v⟩] ∧
      d.pc=(if last then 0x8000080a#32 else 0x800007f4#32) ∧ d.get 12=src+1#32 ∧
      (∀ r : Reg, r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 12 (src+1#32) 0x800007ec#32
  let b := a.goto 0x800007f0#32
  let d := b.goto (if last then 0x8000080a#32 else 0x800007f4#32)
  have t0 : Observed.Step B img ⟨c,ram⟩ ⟨a,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨c,ram⟩) (by rw [hp];decide) (by rw [hp];exact tx2147485674)
    rw [exec_opimm,h12,hp];rfl
  have t1 : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ [] [⟨0x10000000#32,word v⟩] := by
    have a15 : a.get 15=0x10000000#32 := by simp [a,Core.wr_get_ne,h15]
    have a16 : a.get 16=word v := by simp [a,Core.wr_get_ne,h16]
    have hk (o : Oracle) := UartStore.store ⟨a,ram⟩ o 15 16 0#32 4#32 0x10000000#32 (word v) UartPlatform.data
      (by change (0x800007ec#32).getLsbD 0=false;decide) tx2147485676 (by rw [a15];decide +kernel) a16
      (by decide) UartPlatform.data_device rfl rfl
    have he (o : Oracle) : Observed.stepInstr B img ⟨a,ram⟩ o = ⟨.ok b ram [⟨0x10000000#32,word v⟩],[]⟩ := by
      simpa only [word_mask,show a.pc+4#32=0x800007f0#32 by rfl] using hk o
    let o : Oracle := fun _ => 0#32
    have hh : Observed.Step B img ⟨a,ram⟩ ⟨b,ram⟩ (Observed.stepInstr B img ⟨a,ram⟩ o).reads [⟨0x10000000#32,word v⟩] :=
      .instr o (by rw [he])
    simpa only [he] using hh
  have t2 : Observed.Step B img ⟨b,ram⟩ ⟨d,ram⟩ [] [] := by
    apply Observed.pure_step (m := ⟨b,ram⟩) (by change (0x800007f0#32).getLsbD 0=false;decide) tx2147485680
    have b12 : b.get 12=src+1#32 := by simp [b,a,Core.wr_get]
    have b14 : b.get 14=finish := by simp [b,a,Core.wr_get_ne,h14]
    rw [exec_branch,b12,b14,ht]
    cases last with
    | false => rfl
    | true =>
      simp only [ite_true]
      change jump b (0x800007f0#32+26#32)=.done d
      rw [show 0x800007f0#32+26#32=0x8000080a#32 by decide +kernel,jump_ok _ _ (by decide)]
      rfl
  refine ⟨d,.step t0 (.step t1 (.single t2)),rfl,?_,?_,by rfl⟩
  · simp [d,b,a,Core.wr_get]
  · intro reg hr;simp [d,b,a,Core.wr_get_ne,hr]
end E5R.Thermostat.UartTxByte
