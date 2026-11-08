import Projects.thermostat.MainCloseHeaderBounds
import Projects.thermostat.MainCloseName
import Projects.thermostat.MainCloseValueLoop
import Projects.thermostat.QuietDet
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.MainCloseFieldLayout
open E5R E5R.Thermostat

/-- The actual name-length branch; validated slice bounds exclude underflow. -/
theorem name (B : Board) (c : Core) (ram : Word → BitVec 8) (raw : Word) (ns ne : Nat)
    (ordered : ns≤ne) (small : ne<2^32)
    (hp : c.pc=0x80002492#32) (h14 : c.get 14=BitVec.ofNat 32 ne)
    (h15 : c.get 15=BitVec.ofNat 32 ns) (h16 : c.get 16=raw) (h5 : c.get 5=10#32) :
    ∃ n d, n≤3 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if ne-ns=10 then 0x8000249a#32 else 0x80002474#32) ∧
      (ne-ns=10 → d.get 15=raw+BitVec.ofNat 32 ns) ∧
      (∀ r : Reg, r≠14 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 14 (BitVec.ofNat 32 (ne-ns)) 0x80002494#32
  have s : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493010) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h14,h15]
    change Observed.interp B img o (.done (c.wr 14 ((BitVec.ofNat 32 ne)-(BitVec.ofNat 32 ns)) (c.pc+2#32))) ram 0 [] []=_
    rw [BitVec.ofNat_sub_ofNat_of_le ne ns (by omega) ordered,hp];rfl
  have comparison : taken .ne (BitVec.ofNat 32 (ne-ns)) 10#32=decide (ne-ns≠10) := by
    change decide (BitVec.ofNat 32 (ne-ns)≠10#32)=_
    have equal : BitVec.ofNat 32 (ne-ns)=10#32 ↔ ne-ns=10 := by
      constructor
      · intro h
        have hn := congrArg BitVec.toNat h
        simpa only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : ne-ns<2^32)] using hn
      · intro h;rw [h]
    change decide (BitVec.ofNat 32 (ne-ns)≠10#32)=_
    simp only [ne_eq,equal]
  by_cases same : ne-ns=10
  · let b := a.goto 0x80002498#32
    let d := b.wr 15 (raw+BitVec.ofNat 32 ns) 0x8000249a#32
    have t : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
      refine Quiet.step_of (by change (0x80002494#32).getLsbD 0=false;decide) re2147493012 fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok b ram [],[]⟩
      have a14 : a.get 14=BitVec.ofNat 32 (ne-ns) := by simp [a,Core.wr_get]
      have a5 : a.get 5=10#32 := by simp [a,Core.wr_get_ne,h5]
      rw [exec_branch,a14,a5,comparison,show decide (ne-ns≠10)=false by simp [same]];rfl
    have u : Quiet.Step B img ⟨b,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x80002498#32).getLsbD 0=false;decide) re2147493016 fun o => ?_
      change Observed.interp B img o (exec b _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      have b15 : b.get 15=BitVec.ofNat 32 ns := by simp [b,a,Core.wr_get_ne,h15]
      have b16 : b.get 16=raw := by simp [b,a,Core.wr_get_ne,h16]
      rw [exec_op,b15,b16]
      change Observed.interp B img o (.done (b.wr 15 ((BitVec.ofNat 32 ns)+raw) 0x8000249a#32)) ram 0 [] []=_
      rw [BitVec.add_comm (BitVec.ofNat 32 ns) raw];rfl
    refine ⟨3,d,by decide,.step s (.step t (.single u)),by simp only [same,ite_true];rfl,?_,?_,by rfl⟩
    · intro _;simp [d,Core.wr_get]
    · intro r n14 n15;simp [d,b,a,Core.wr_get_ne,n14,n15]
  · let d := a.goto 0x80002474#32
    have t : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x80002494#32).getLsbD 0=false;decide) re2147493012 fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      have a14 : a.get 14=BitVec.ofNat 32 (ne-ns) := by simp [a,Core.wr_get]
      have a5 : a.get 5=10#32 := by simp [a,Core.wr_get_ne,h5]
      rw [exec_branch,a14,a5,comparison,show decide (ne-ns≠10)=true by simp [same]]
      rw [ite_eq_left rfl,show a.pc=0x80002494#32 from rfl,show 0x80002494#32+0xffffffe0#32=0x80002474#32 by decide +kernel]
      change Observed.interp B img o (jump a 0x80002474#32) ram 0 [] []=_
      rw [jump_ok _ _ (by decide)];rfl
    refine ⟨2,d,by decide,.step s (.single t),by simp only [same,ite_false];rfl,?_,?_,by rfl⟩
    · intro h;contradiction
    · intro r n14 _;simp [d,a,Core.wr_get_ne,n14]

/-- Exact value-slice setup after a matching name. Empty values skip scanning. -/
theorem value (B : Board) (c : Core) (ram : Word → BitVec 8) (raw : Word) (vs ve : Nat)
    (ordered : vs≤ve) (small : ve<2^32)
    (hp : c.pc=0x80002574#32) (h10 : c.get 10=BitVec.ofNat 32 vs)
    (h11 : c.get 11=BitVec.ofNat 32 ve) (h16 : c.get 16=raw) :
    ∃ n d, n≤4 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if ve-vs=0 then 0x80002474#32 else 0x80002584#32) ∧
      (ve-vs≠0 → d.get 22=raw+BitVec.ofNat 32 vs ∧
        d.get 14=BitVec.ofNat 32 (ve-vs) ∧ d.get 15=(raw+BitVec.ofNat 32 vs)+BitVec.ofNat 32 (ve-vs)) ∧
      (∀ r : Reg, r≠14 → r≠15 → r≠22 → d.get r=c.get r) ∧ d.sameCsr c := by
  let a := c.wr 14 (BitVec.ofNat 32 (ve-vs)) 0x80002578#32
  have s : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact re2147493236) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,h11,h10]
    change Observed.interp B img o (.done (c.wr 14 ((BitVec.ofNat 32 ve)-(BitVec.ofNat 32 vs)) (c.pc+4#32))) ram 0 [] []=_
    rw [BitVec.ofNat_sub_ofNat_of_le ve vs (by omega) ordered,hp];rfl
  have cmp : taken .eq (BitVec.ofNat 32 (ve-vs)) (0 : Word)=decide (ve-vs=0) :=
    MainCloseScanFinishMath.zeroTest _ (by omega)
  by_cases empty : ve-vs=0
  · let d := a.goto 0x80002474#32
    have t : Quiet.Step B img ⟨a,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x80002578#32).getLsbD 0=false;decide) re2147493240 fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      have a14 : a.get 14=BitVec.ofNat 32 (ve-vs) := by simp [a,Core.wr_get]
      rw [exec_branch,a14,Core.get_zero,cmp,show decide (ve-vs=0)=true by simp [empty]]
      rw [ite_eq_left rfl,show a.pc=0x80002578#32 from rfl,show 0x80002578#32+0xfffffefc#32=0x80002474#32 by decide +kernel]
      change Observed.interp B img o (jump a 0x80002474#32) ram 0 [] []=_
      rw [jump_ok _ _ (by decide)];rfl
    refine ⟨2,d,by decide,.step s (.single t),by simp only [empty,ite_true];rfl,?_,?_,by rfl⟩
    · intro h;contradiction
    · intro r n14 _ _;simp [d,a,Core.wr_get_ne,n14]
  · let b := a.goto 0x8000257c#32
    let e := b.wr 22 (raw+BitVec.ofNat 32 vs) 0x80002580#32
    let d := e.wr 15 (raw+BitVec.ofNat 32 ve) 0x80002584#32
    have t : Quiet.Step B img ⟨a,ram⟩ ⟨b,ram⟩ := by
      refine Quiet.step_of (by change (0x80002578#32).getLsbD 0=false;decide) re2147493240 fun o => ?_
      change Observed.interp B img o (exec a _ _) ram 0 [] []=⟨.ok b ram [],[]⟩
      have a14 : a.get 14=BitVec.ofNat 32 (ve-vs) := by simp [a,Core.wr_get]
      rw [exec_branch,a14,Core.get_zero,cmp,show decide (ve-vs=0)=false by simp [empty]];rfl
    have u : Quiet.Step B img ⟨b,ram⟩ ⟨e,ram⟩ := by
      refine Quiet.step_of (by change (0x8000257c#32).getLsbD 0=false;decide) re2147493244 fun o => ?_
      change Observed.interp B img o (exec b _ _) ram 0 [] []=⟨.ok e ram [],[]⟩
      have b10 : b.get 10=BitVec.ofNat 32 vs := by simp [b,a,Core.wr_get_ne,h10]
      have b16 : b.get 16=raw := by simp [b,a,Core.wr_get_ne,h16]
      rw [exec_op,b10,b16];rfl
    have v : Quiet.Step B img ⟨e,ram⟩ ⟨d,ram⟩ := by
      refine Quiet.step_of (by change (0x80002580#32).getLsbD 0=false;decide) re2147493248 fun o => ?_
      change Observed.interp B img o (exec e _ _) ram 0 [] []=⟨.ok d ram [],[]⟩
      have e11 : e.get 11=BitVec.ofNat 32 ve := by simp [e,b,a,Core.wr_get_ne,h11]
      have e16 : e.get 16=raw := by simp [e,b,a,Core.wr_get_ne,h16]
      rw [exec_op,e11,e16];rfl
    refine ⟨4,d,by decide,.step s (.step t (.step u (.single v))),by simp only [empty,ite_false];rfl,?_,?_,by rfl⟩
    · intro _;refine ⟨by simp [d,e,Core.wr_get_ne,Core.wr_get],by simp [d,e,b,a,Core.wr_get_ne,Core.wr_get],?_⟩
      change raw+BitVec.ofNat 32 ve=(raw+BitVec.ofNat 32 vs)+BitVec.ofNat 32 (ve-vs)
      rw [BitVec.add_assoc,←BitVec.ofNat_add]
      rw [show vs+(ve-vs)=ve by omega]
    · intro r n14 n15 n22;simp [d,e,b,a,Core.wr_get_ne,n14,n15,n22]
end E5R.Thermostat.MainCloseFieldLayout
