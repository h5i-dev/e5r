import Projects.thermostat.KernelCode
import Projects.thermostat.Memory
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.Dispatch
open E5R E5R.Thermostat

def entry (tag : Fin 5) : Word := match tag.val with
 | 0 => 0x800000d6 | 1 => 0x80000158 | 2 => 0x800000fe | 3 => 0x80000078 | _ => 0x80000128

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (tag : Fin 5)
    (hp : c.pc = 0x80000062) (hr : B.inRam (c.get 13) 1 = true)
    (ht : ram (c.get 13) = BitVec.ofNat 8 tag.val) :
    ∃ n d, n ≤ 7 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = entry tag ∧
      (∀ r : Reg, r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  have hv := tag.isLt
  have hc : tag.val = 0 ∨ tag.val = 1 ∨ tag.val = 2 ∨ tag.val = 3 ∨ tag.val = 4 := by omega
  rcases hc with htag|htag|htag|htag|htag
  ·
    let c1 := c.wr 14 0#32 0x80000066
    let c2 := c1.wr 15 1#32 0x80000068
    let c3 := c2.goto 0x800000d4
    let c4 := c3.goto 0x800000d6
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp]; decide)
        (by rw [hp]; exact d2147483746) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ht,htag,hp]
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80000066 : Word).getLsbD 0 = false; decide)
        (by exact d2147483750) fun o => ?_
      rw [exec_opimm]
      rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000068 : Word).getLsbD 0 = false; decide)
        (by exact d2147483752) fun o => ?_
      rw [exec_branch]
      have ha : c2.get 14 = 0#32 := by simp [c2,c1,Core.wr_get]
      rw [ha]
      have hb : c2.get 15 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_left (by decide +kernel)]
      rw [jump_ok _ _ (by change (0x800000d4 : Word).getLsbD 0 = false; decide)]
      rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x800000d4 : Word).getLsbD 0 = false; decide)
        (by exact d2147483860) fun o => ?_
      rw [exec_branch]
      have ha : c3.get 14 = 0#32 := by simp [c3,c2,c1,Core.wr_get]
      rw [ha]
      rw [Core.get_zero]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    refine ⟨4,c4,by decide,.step s0 (.step s1 (.step s2 (.single s3))),?_,?_,?_⟩
    · simp [entry,htag,c4]
    · intro r h14 h15
      simp [c4,c3,c2,c1,Core.wr_get_ne,h14,h15]
    · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c))))
  ·
    let c1 := c.wr 14 1#32 0x80000066
    let c2 := c1.wr 15 1#32 0x80000068
    let c3 := c2.goto 0x800000d4
    let c4 := c3.goto 0x80000158
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp]; decide)
        (by rw [hp]; exact d2147483746) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ht,htag,hp]
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80000066 : Word).getLsbD 0 = false; decide)
        (by exact d2147483750) fun o => ?_
      rw [exec_opimm]
      rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000068 : Word).getLsbD 0 = false; decide)
        (by exact d2147483752) fun o => ?_
      rw [exec_branch]
      have ha : c2.get 14 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [ha]
      have hb : c2.get 15 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_left (by decide +kernel)]
      rw [jump_ok _ _ (by change (0x800000d4 : Word).getLsbD 0 = false; decide)]
      rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x800000d4 : Word).getLsbD 0 = false; decide)
        (by exact d2147483860) fun o => ?_
      rw [exec_branch]
      have ha : c3.get 14 = 1#32 := by simp [c3,c2,c1,Core.wr_get]
      rw [ha]
      rw [Core.get_zero]
      rw [ite_eq_left (by decide +kernel)]
      rw [jump_ok _ _ (by change (0x80000158 : Word).getLsbD 0 = false; decide)]
      rfl
    refine ⟨4,c4,by decide,.step s0 (.step s1 (.step s2 (.single s3))),?_,?_,?_⟩
    · simp [entry,htag,c4]
    · intro r h14 h15
      simp [c4,c3,c2,c1,Core.wr_get_ne,h14,h15]
    · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c))))
  ·
    let c1 := c.wr 14 2#32 0x80000066
    let c2 := c1.wr 15 1#32 0x80000068
    let c3 := c2.goto 0x8000006c
    let c4 := c3.wr 15 2#32 0x8000006e
    let c5 := c4.goto 0x800000fe
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp]; decide)
        (by rw [hp]; exact d2147483746) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ht,htag,hp]
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80000066 : Word).getLsbD 0 = false; decide)
        (by exact d2147483750) fun o => ?_
      rw [exec_opimm]
      rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000068 : Word).getLsbD 0 = false; decide)
        (by exact d2147483752) fun o => ?_
      rw [exec_branch]
      have ha : c2.get 14 = 2#32 := by simp [c2,c1,Core.wr_get]
      rw [ha]
      have hb : c2.get 15 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x8000006c : Word).getLsbD 0 = false; decide)
        (by exact d2147483756) fun o => ?_
      rw [exec_opimm]
      rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine detStep_of (by change (0x8000006e : Word).getLsbD 0 = false; decide)
        (by exact d2147483758) fun o => ?_
      rw [exec_branch]
      have ha : c4.get 14 = 2#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [ha]
      have hb : c4.get 15 = 2#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_left (by decide +kernel)]
      rw [jump_ok _ _ (by change (0x800000fe : Word).getLsbD 0 = false; decide)]
      rfl
    refine ⟨5,c5,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.single s4)))),?_,?_,?_⟩
    · simp [entry,htag,c5]
    · intro r h14 h15
      simp [c5,c4,c3,c2,c1,Core.wr_get_ne,h14,h15]
    · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c)))))
  ·
    let c1 := c.wr 14 3#32 0x80000066
    let c2 := c1.wr 15 1#32 0x80000068
    let c3 := c2.goto 0x8000006c
    let c4 := c3.wr 15 2#32 0x8000006e
    let c5 := c4.goto 0x80000072
    let c6 := c5.wr 15 3#32 0x80000074
    let c7 := c6.goto 0x80000078
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp]; decide)
        (by rw [hp]; exact d2147483746) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ht,htag,hp]
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80000066 : Word).getLsbD 0 = false; decide)
        (by exact d2147483750) fun o => ?_
      rw [exec_opimm]
      rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000068 : Word).getLsbD 0 = false; decide)
        (by exact d2147483752) fun o => ?_
      rw [exec_branch]
      have ha : c2.get 14 = 3#32 := by simp [c2,c1,Core.wr_get]
      rw [ha]
      have hb : c2.get 15 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x8000006c : Word).getLsbD 0 = false; decide)
        (by exact d2147483756) fun o => ?_
      rw [exec_opimm]
      rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine detStep_of (by change (0x8000006e : Word).getLsbD 0 = false; decide)
        (by exact d2147483758) fun o => ?_
      rw [exec_branch]
      have ha : c4.get 14 = 3#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [ha]
      have hb : c4.get 15 = 2#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine detStep_of (by change (0x80000072 : Word).getLsbD 0 = false; decide)
        (by exact d2147483762) fun o => ?_
      rw [exec_opimm]
      rfl
    have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine detStep_of (by change (0x80000074 : Word).getLsbD 0 = false; decide)
        (by exact d2147483764) fun o => ?_
      rw [exec_branch]
      have ha : c6.get 14 = 3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get]
      rw [ha]
      have hb : c6.get 15 = 3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    refine ⟨7,c7,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),?_,?_,?_⟩
    · simp [entry,htag,c7]
    · intro r h14 h15
      simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h14,h15]
    · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c)))))))
  ·
    let c1 := c.wr 14 4#32 0x80000066
    let c2 := c1.wr 15 1#32 0x80000068
    let c3 := c2.goto 0x8000006c
    let c4 := c3.wr 15 2#32 0x8000006e
    let c5 := c4.goto 0x80000072
    let c6 := c5.wr 15 3#32 0x80000074
    let c7 := c6.goto 0x80000128
    have s0 : DetStep B img ⟨c,ram⟩ ⟨c1,ram⟩ := by
      refine detStep_of (by rw [hp]; decide)
        (by rw [hp]; exact d2147483746) fun o => ?_
      rw [exec_load,BitVec.add_zero,interp_load_ram (B := B) (img := img) (w := .b) o (by simp only [Width.bytes,Nat.mod_one]) hr]
      rw [Memory.load_byte]
      dsimp only
      rw [ht,htag,hp]
      rfl
    have s1 : DetStep B img ⟨c1,ram⟩ ⟨c2,ram⟩ := by
      refine detStep_of (by change (0x80000066 : Word).getLsbD 0 = false; decide)
        (by exact d2147483750) fun o => ?_
      rw [exec_opimm]
      rfl
    have s2 : DetStep B img ⟨c2,ram⟩ ⟨c3,ram⟩ := by
      refine detStep_of (by change (0x80000068 : Word).getLsbD 0 = false; decide)
        (by exact d2147483752) fun o => ?_
      rw [exec_branch]
      have ha : c2.get 14 = 4#32 := by simp [c2,c1,Core.wr_get]
      rw [ha]
      have hb : c2.get 15 = 1#32 := by simp [c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    have s3 : DetStep B img ⟨c3,ram⟩ ⟨c4,ram⟩ := by
      refine detStep_of (by change (0x8000006c : Word).getLsbD 0 = false; decide)
        (by exact d2147483756) fun o => ?_
      rw [exec_opimm]
      rfl
    have s4 : DetStep B img ⟨c4,ram⟩ ⟨c5,ram⟩ := by
      refine detStep_of (by change (0x8000006e : Word).getLsbD 0 = false; decide)
        (by exact d2147483758) fun o => ?_
      rw [exec_branch]
      have ha : c4.get 14 = 4#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [ha]
      have hb : c4.get 15 = 2#32 := by simp [c4,c3,c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_right (by decide +kernel)]
      rfl
    have s5 : DetStep B img ⟨c5,ram⟩ ⟨c6,ram⟩ := by
      refine detStep_of (by change (0x80000072 : Word).getLsbD 0 = false; decide)
        (by exact d2147483762) fun o => ?_
      rw [exec_opimm]
      rfl
    have s6 : DetStep B img ⟨c6,ram⟩ ⟨c7,ram⟩ := by
      refine detStep_of (by change (0x80000074 : Word).getLsbD 0 = false; decide)
        (by exact d2147483764) fun o => ?_
      rw [exec_branch]
      have ha : c6.get 14 = 4#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get]
      rw [ha]
      have hb : c6.get 15 = 3#32 := by simp [c6,c5,c4,c3,c2,c1,Core.wr_get]
      rw [hb]
      rw [ite_eq_left (by decide +kernel)]
      rw [jump_ok _ _ (by change (0x80000128 : Word).getLsbD 0 = false; decide)]
      rfl
    refine ⟨7,c7,by decide,.step s0 (.step s1 (.step s2 (.step s3 (.step s4 (.step s5 (.single s6)))))),?_,?_,?_⟩
    · simp [entry,htag,c7]
    · intro r h14 h15
      simp [c7,c6,c5,c4,c3,c2,c1,Core.wr_get_ne,h14,h15]
    · exact (Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_goto _ _).trans ((Core.sameCsr_wr _ _ _ _).trans ((Core.sameCsr_wr _ _ _ _).trans (Core.sameCsr_refl c)))))))

end E5R.Thermostat.Dispatch
