import Projects.thermostat.RoutePathScan
import Projects.thermostat.HeadTargetMath
set_option autoImplicit false
namespace E5R.Thermostat.RoutePathEntry
open E5R E5R.Thermostat

/-- The actual scan-entry guard handles an empty path/suffix before loading.
    Together with RoutePathScan this covers every allocated path suffix. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (i : Nat) (xs : List (BitVec 8))
    (span : Bytes.Span B ram (base+BitVec.ofNat 32 i) xs) (bound : i+xs.length≤2048)
    (hp : c.pc=0x8000288e#32) (h20 : c.get 20=base) (h10 : c.get 10=BitVec.ofNat 32 i)
    (h9 : c.get 9=BitVec.ofNat 32 (i+xs.length)) (h24 : c.get 24=47#32) :
    ∃ n d, n≤5*xs.length+3 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800028a8#32 ∧
      d.get 23=BitVec.ofNat 32 (i+RoutePathScan.length xs) ∧ RoutePathScan.Frame c d ∧ d.sameCsr c := by
  let a := c.wr 23 (BitVec.ofNat 32 i) 0x80002890#32
  have enter : Quiet.Step B img ⟨c,ram⟩ ⟨a,ram⟩ := by
    refine Quiet.step_of (by rw [hp];decide) (by rw [hp];exact rt2147494030) fun o => ?_
    change Observed.interp B img o (exec c _ _) ram 0 [] []=⟨.ok a ram [],[]⟩
    rw [exec_op,Core.get_zero,h10,hp]
    change Observed.interp B img o (.done (c.wr 23 (0#32+BitVec.ofNat 32 i) 0x80002890#32)) ram 0 [] []=_
    rw [BitVec.zero_add];rfl
  have a10 : a.get 10=BitVec.ofNat 32 i := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h10
  have a9 : a.get 9=BitVec.ofNat 32 (i+xs.length) := (Core.wr_get_ne _ _ _ _ _ (by decide)).trans h9
  have a23 : a.get 23=BitVec.ofNat 32 i := Core.wr_get_self _ _ _ _ (by decide)
  have test : taken .geu (a.get 10) (a.get 9)=decide (xs=[]) := by
    rw [a10,a9,HeadTargetMath.geu i (i+xs.length) (by omega) bound]
    cases xs with
    | nil => simp
    | cons b bs => have positive : ¬i+(b::bs).length≤i := by simp only [List.length_cons];omega
                   simp only [positive,decide_false,List.cons_ne_nil]
  obtain ⟨b,branch,pc,regs,csr⟩ := QuietBranch.contract B img a ram 0x80002890#32 4#32 24#32 .geu 10 9 (decide (xs=[]))
    rfl (by decide) (by decide) rt2147494032 test
  have kept (r : Reg) (ne : r≠23) : b.get r=c.get r := (regs r).trans (Core.wr_get_ne _ _ _ _ _ ne)
  have b23 := (regs 23).trans a23
  have bc : b.sameCsr c := csr.trans (Core.sameCsr_wr c _ _ _)
  cases xs with
  | nil =>
    have endPC : b.pc=0x800028a8#32 := by simpa only [decide_true,ite_true,show 0x80002890#32+24#32=0x800028a8#32 by decide +kernel] using pc
    exact ⟨2,b,by decide,(Quiet.Steps.single enter).trans branch,endPC,by simpa only [RoutePathScan.length,Nat.add_zero] using b23,fun r _ ne => kept r ne,bc⟩
  | cons byte rest =>
    have scanPC : b.pc=0x80002894#32 := by simpa only [List.cons_ne_nil,decide_false,Bool.false_eq_true,ite_false,show 0x80002890#32+4#32=0x80002894#32 by decide +kernel] using pc
    obtain ⟨n,d,hn,scan,dp,d23,frame,dc⟩ := RoutePathScan.contract B b ram base i (byte::rest) span (by simp) (by omega)
      scanPC ((kept 20 (by decide)).trans h20) b23 ((kept 9 (by decide)).trans h9) ((kept 24 (by decide)).trans h24)
    exact ⟨2+n,d,by omega,((Quiet.Steps.single enter).trans branch).trans scan,dp,d23,
      fun r n12 n23 => (frame r n12 n23).trans (kept r n23),dc.trans bc⟩
end E5R.Thermostat.RoutePathEntry
