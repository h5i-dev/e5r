import Projects.thermostat.MemcpyCode
import Projects.thermostat.Memory
set_option maxRecDepth 3000
namespace E5R.Thermostat.AlignedCopyTurn
open E5R E5R.Thermostat

/-- The actual optimized memcpy word loop. Source is checked read-only ROM;
    no word-copy behavior is postulated. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst finish value : Word) (again : Bool)
    (hp : c.pc = 0x80005212#32) (h16 : c.get 16 = src) (h14 : c.get 14 = dst) (h13 : c.get 13 = finish)
    (has : src.toNat%4=0) (had : dst.toNat%4=0) (ho : B.inRam src 4 = false)
    (hv : romRead? img src.toNat 4 false = some value) (hd : B.inRam dst 4 = true)
    (ht : taken .ltu (dst+4#32) finish = again) :
    ∃ d, DetSteps B img 5 ⟨c,ram⟩ ⟨d,ramWrite ram dst value .w⟩ ∧
      d.pc = (if again then 0x80005212#32 else 0x80005222#32) ∧ d.get 14 = dst+4#32 ∧ d.get 16 = src+4#32 ∧
      (∀ r : Reg, r ≠ 14 → r ≠ 16 → r ≠ 17 → d.get r = c.get r) ∧ d.sameCsr c := by
  let a := c.wr 17 value 0x80005216#32
  let r := ramWrite ram dst value .w
  let b := a.goto 0x8000521a#32
  let z := b.wr 14 (dst+4#32) 0x8000521c#32
  let u := z.wr 16 (src+4#32) 0x8000521e#32
  let d := u.goto (if again then 0x80005212#32 else 0x80005222#32)
  have t0 : DetStep B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine detStep_of (by rw [hp];decide) (by rw [hp];exact cp2147504658) fun o => ?_
    rw [exec_load,h16,BitVec.add_zero,interp_load_rom (B := B) (img := img) (w := .w) o has ho rfl hv,hp];rfl
  have t1 : DetStep B img ⟨a,ram⟩ ⟨b,r⟩ := by
    refine detStep_of (by change (0x80005216#32).getLsbD 0 = false;decide) cp2147504662 fun o => ?_
    have a14 : a.get 14 = dst := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h14
    have a17 : a.get 17 = value := by simp [a,Core.wr_get]
    rw [exec_store,a14,a17,BitVec.add_zero,interp_store_ram (B := B) (img := img) (w := .w) o had hd];rfl
  have t2 : DetStep B img ⟨b,r⟩ ⟨z,r⟩ := by
    refine detStep_of (by change (0x8000521a#32).getLsbD 0 = false;decide) cp2147504666 fun o => ?_
    have b14 : b.get 14 = dst := by simp [b,a,Core.wr_get_ne,h14]
    rw [exec_opimm,b14];rfl
  have t3 : DetStep B img ⟨z,r⟩ ⟨u,r⟩ := by
    refine detStep_of (by change (0x8000521c#32).getLsbD 0 = false;decide) cp2147504668 fun o => ?_
    have z16 : z.get 16 = src := by simp [z,b,a,Core.wr_get_ne,h16]
    rw [exec_opimm,z16];rfl
  have t4 : DetStep B img ⟨u,r⟩ ⟨d,r⟩ := by
    refine detStep_of (by change (0x8000521e#32).getLsbD 0 = false;decide) cp2147504670 fun o => ?_
    have u14 : u.get 14 = dst+4#32 := by simp [u,z,Core.wr_get_ne,Core.wr_get]
    have u13 : u.get 13 = finish := by simp [u,z,b,a,Core.wr_get_ne,h13]
    rw [exec_branch,u14,u13,ht]
    cases again with
    | false => rfl
    | true =>
      simp only [ite_true]
      change interp B img o (jump u (0x8000521e#32+0xfffffff4#32)) r 0 [] = _
      rw [show (0x8000521e#32+0xfffffff4#32)=0x80005212#32 by decide +kernel,jump_ok _ _ (by decide)];rfl
  refine ⟨d,.step t0 (.step t1 (.step t2 (.step t3 (.single t4)))),rfl,?_,?_,?_,by rfl⟩
  · simp [d,u,z,Core.wr_get_ne,Core.wr_get]
  · simp [d,u,Core.wr_get]
  · intro reg h14 h16 h17
    simp [d,u,z,b,a,Core.wr_get_ne,h14,h16,h17]
end E5R.Thermostat.AlignedCopyTurn
