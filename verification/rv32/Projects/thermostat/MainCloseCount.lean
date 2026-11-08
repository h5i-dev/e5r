import Projects.thermostat.MainCloseCode
import Projects.thermostat.HeaderCount
import Projects.thermostat.QuietDet
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseCount
open E5R E5R.Thermostat

/-- The actual count bound and empty-table branch, before any span is read. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (req : Word) (count : Nat)
    (bounded : count≤16) (hp : c.pc=0x8000240a#32) (h10 : c.get 10=req)
    (object : Memory.Block B req 336) (aligned : req.toNat%4=0)
    (stored : ramRead ram (req+288#32) .w=BitVec.ofNat 32 count) :
    ∃ d, Quiet.Steps B img 4 ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if count=0 then 0x8000267c#32 else 0x80002418#32) ∧
      d.get 11=BitVec.ofNat 32 count ∧ (∀ r : Reg, r≠11 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 11 (BitVec.ofNat 32 count) 0x8000240e#32
  let b := a.wr 12 17#32 0x80002410#32
  let e := b.goto 0x80002414#32
  let d := e.goto (if count=0 then 0x8000267c#32 else 0x80002418#32)
  have s : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine QuietDet.step_of (by rw [hp];decide) (by rw [hp];exact re2147492874) fun o => ?_
    rw [exec_load,h10,interp_load_ram (B := B) (img := img) (w := .w) o
      (Memory.word_aligned req 72 aligned) (Memory.block_access object (off := 288) (by decide) (by decide)),stored,hp];rfl
  have t : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
    refine QuietDet.step_of (by change (0x8000240e#32).getLsbD 0=false;decide) re2147492878 fun o => ?_
    rw [exec_opimm,Core.get_zero];rfl
  have u : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002410#32).getLsbD 0=false;decide) re2147492880 fun o => ?_
    have b11 : b.get 11=BitVec.ofNat 32 count := by simp [b,a,Core.wr_get_ne,Core.wr_get]
    have b12 : b.get 12=17#32 := by simp [b,Core.wr_get]
    have safe : taken .geu (BitVec.ofNat 32 count) 17#32=false := by
      change (!taken .ltu (BitVec.ofNat 32 count) (BitVec.ofNat 32 17))=false
      rw [ParamMath.ult count 17 (by omega) (by decide),decide_eq_true (by omega)];rfl
    rw [exec_branch,b11,b12,safe];rfl
  have v : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
    refine QuietDet.step_of (by change (0x80002414#32).getLsbD 0=false;decide) re2147492884 fun o => ?_
    have e11 : e.get 11=BitVec.ofNat 32 count := by simp [e,b,a,Core.wr_get_ne,Core.wr_get]
    rw [exec_branch,e11,Core.get_zero]
    change interp B img o (if taken .eq (BitVec.ofNat 32 count) (BitVec.ofNat 32 0) then _ else _) ram 0 []=_
    rw [Usize.eq count 0 (by omega) (by decide)]
    by_cases empty : count=0
    · rw [decide_eq_true empty];simp only [ite_true,d,ite_eq_left empty]
      change interp B img o (jump e (0x80002414#32+0x268#32)) ram 0 []=_
      rw [show 0x80002414#32+0x268#32=0x8000267c#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
    · rw [decide_eq_false empty];simp only [Bool.false_eq_true,ite_false,d,ite_eq_right empty];rfl
  refine ⟨d,.step s (.step t (.step u (.single v))),rfl,?_,?_,by rfl⟩
  · simp [d,e,b,a,Core.wr_get_ne,Core.wr_get]
  · intro r n11 n12;simp [d,e,b,a,Core.wr_get_ne,n11,n12]
end E5R.Thermostat.MainCloseCount
