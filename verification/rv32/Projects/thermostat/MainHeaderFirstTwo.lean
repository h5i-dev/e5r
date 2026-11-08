import Projects.thermostat.MainHeaderLayout
import Projects.thermostat.MainInitTwo
import Projects.thermostat.FutureSetup
import Projects.thermostat.HeadEmpty
import Projects.thermostat.ReadMore
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainHeaderFirstTwo
open E5R E5R.Thermostat

structure Ready (B : Board) (c : Core) (ram : Word → BitVec 8) : Prop where
  pc : c.pc = 0x80000ba2#32
  sp : c.get 2 = 0x80ffeb90#32
  fp : c.get 8 = 0x80fff814#32
  uart : c.get 19 = 0x10000000#32
  one : c.get 22 = 1#32
  zero : c.get 10 = 0#32
  dst : c.get 12 = 0x80ffec14#32
  stack : Memory.Block B 0x80ff0000#32 65536
  app : AppState.At ram Spec.initial
  future : FutureSetup.Layout ram
  masked : c.mie_ = false
  header : MainHeaderLayout.At ram 0

/-- The actual initial Future setup, empty header parse, Incomplete dispatch
    and receive-slice construction. No request bytes or typed command assumed. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (h : MainInit.Ready B c ram) :
    ∃ d r, DetSteps B img 118 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧
      (∀ x, (∀ i : Fin 65536, x ≠ 0x80ff0000#32+BitVec.ofNat 32 i.val) → r x = ram x) ∧ d.get 18=c.get 18 := by
  let c1 := (FutureSetup.execute c ram).core
  let r1 := FutureSetup.memory ram
  have hmain : Memory.Block B 0x80ffeb90#32 5232 :=
    Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) h.stack (by decide) (by decide)
  have hr1 := FutureSetup.contract B c ram h.pc h.sp h.fp hmain
  obtain ⟨hpc1,hret1,hout1,hrx1,hlen1,hmax1,hregs1,hcsr1⟩ := FutureSetup.fields c ram
  have hsp1 : c1.get 2 = 0x80ffeb90#32 :=
    (hregs1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.sp
  have hfp1 : c1.get 8 = 0x80fff814#32 :=
    (hregs1 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.fp
  have hU1 : c1.get 19 = 0x10000000#32 :=
    (hregs1 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.uart
  have hOne1 : c1.get 22 = 1#32 :=
    (hregs1 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.one
  have hfut1 : FutureSetup.Layout r1 := FutureSetup.layout ram h.routes.2
  let c2 := (HeadEmpty.execute c1 r1).core
  let r2 := HeadEmpty.memory c1 r1
  have hr2 := HeadEmpty.execute_contract B c1 r1 hpc1 hsp1 hret1 hout1 hlen1 hmax1 hfut1.limit h.stack
  obtain ⟨hpc2,hsp2,_,hcsr2⟩ := HeadEmpty.fields c1 r1
  have hfp2 : c2.get 8 = 0x80fff814#32 := (show c2.get 8 = c1.get 8 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c1 r1 ⟨0,by decide⟩).trans hfp1
  have hU2 : c2.get 19 = 0x10000000#32 := (show c2.get 19 = c1.get 19 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c1 r1 ⟨3,by decide⟩).trans hU1
  have hOne2 : c2.get 22 = 1#32 := (show c2.get 22 = c1.get 22 from by simpa only [HeadEmpty.reg] using HeadEmpty.saved c1 r1 ⟨6,by decide⟩).trans hOne1
  have hheadRegion (a : Word) (n : Nat) (hlo : 0x80ffeb90 ≤ a.toNat) (hhi : a.toNat+n ≤ 0x80fffd38) :
      ∀ i : Fin n, r2 (a+BitVec.ofNat 32 i.val) = r1 (a+BitVec.ofNat 32 i.val) := by
    intro i
    apply HeadEmpty.frame
    · intro j
      exact Ne.symm (WordZero.separated 0x80ffea10#32 a 384 n (by exact hlo) (by omega) j i)
    · exact WordZero.separated a 0x80fffd38#32 n 8 hhi (by decide +kernel) i
  have hfut2 : FutureSetup.Layout r2 := FutureSetup.layout_preserve r1 r2 hfut1
    (hheadRegion 0x80fff814#32 449 (by decide +kernel) (by decide +kernel))
  have hout2 := HeadEmpty.incomplete c1 r1
  let d := (ReadMore.execute c2 r2).core
  let r := ReadMore.memory r2
  have hr3 := ReadMore.execute_contract B c2 r2 hpc2 hfp2 hout2.1 hout2.2
    hfut2.filledPtr hfut2.capacity hfut2.filled hfut2.rx hfut2.uartPtr h.stack
  obtain ⟨hpc3,hzero3,hdst3,hregs3,hcsr3⟩ := ReadMore.fields c2 r2
  have hfut3 : FutureSetup.Layout r := FutureSetup.layout_preserve r2 r hfut2 (by
    intro i
    apply ReadMore.frame
    exact WordZero.separated 0x80fff814#32 0x80fff9d8#32 449 13 (by decide +kernel) (by decide +kernel) i)
  have happ1 : AppState.At r1 Spec.initial := AppState.preserve ram r1 Spec.initial h.app (by
    intro i
    apply FutureSetup.frame
    · exact WordZero.separated 0x80ffebbc#32 0x80fff814#32 25 449 (by decide +kernel) (by decide +kernel) i
    · intro j
      exact Ne.symm (WordZero.separated 0x80ffebb8#32 0x80ffebbc#32 4 25 (by decide +kernel) (by decide +kernel) j i))
  have happ2 : AppState.At r2 Spec.initial := AppState.preserve r1 r2 Spec.initial happ1
    (hheadRegion 0x80ffebbc#32 25 (by decide +kernel) (by decide +kernel))
  have happ3 : AppState.At r Spec.initial := AppState.preserve r2 r Spec.initial happ2 (by
    intro i
    apply ReadMore.frame
    exact WordZero.separated 0x80ffebbc#32 0x80fff9d8#32 25 13 (by decide +kernel) (by decide +kernel) i)
  have hcsr : d.sameCsr c := hcsr3.trans (hcsr2.trans hcsr1)
  have hmask3 : d.mie_ = false := (congrArg Prod.fst hcsr).trans h.masked
  have head1 := MainHeaderLayout.initialized ram h.routes.2
  have head2 := MainHeaderLayout.preserve head1 (hheadRegion 0x80fff814#32 449 (by decide +kernel) (by decide +kernel))
  have head3 : MainHeaderLayout.At r 0 := MainHeaderLayout.preserve head2 (by
    intro i
    apply ReadMore.frame
    exact WordZero.separated 0x80fff814#32 0x80fff9d8#32 449 13 (by decide +kernel) (by decide +kernel) i)
  have two1 : c1.get 18=c.get 18 := hregs1 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have two2 : c2.get 18=c1.get 18 := by simpa only [HeadEmpty.reg] using HeadEmpty.saved c1 r1 ⟨2,by decide⟩
  have two3 : d.get 18=c2.get 18 := hregs3 18 (by decide) (by decide) (by decide) (by decide) (by decide)
  refine ⟨d,r,(hr1.trans hr2).trans hr3,⟨hpc3,?_,?_,?_,?_,hzero3,hdst3,h.stack,happ3,hfut3,hmask3,head3⟩,?_,two3.trans (two2.trans two1)⟩
  · exact (hregs3 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hsp2
  · exact (hregs3 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hfp2
  · exact (hregs3 19 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hU2
  · exact (hregs3 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans hOne2
  · intro x hx
    change ReadMore.memory r2 x = ram x
    rw [ReadMore.frame r2 x (MainInit.sub_away x 0x80fff9d8#32 63960 13 hx (by decide +kernel) (by decide))]
    change HeadEmpty.memory c1 r1 x = ram x
    rw [HeadEmpty.frame c1 r1 x
      (MainInit.sub_away x 0x80ffea10#32 59920 384 hx (by decide +kernel) (by decide))
      (MainInit.sub_away x 0x80fffd38#32 64824 8 hx (by decide +kernel) (by decide))]
    change FutureSetup.memory ram x = ram x
    exact FutureSetup.frame ram x
      (MainInit.sub_away x 0x80fff814#32 63508 449 hx (by decide +kernel) (by decide))
      (MainInit.sub_away x 0x80ffebb8#32 60344 4 hx (by decide +kernel) (by decide))

theorem reset_contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000#32) (hmpp : c.mpp = 0 ∨ c.mpp = 3)
    (hm : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d r, DetSteps B img 2550 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧ d.get 18=2#32 := by
  obtain ⟨c0,r0,hr0,hready,two0,_⟩ := MainInitTwo.contract B c ram hp hmpp hm
  obtain ⟨d,r,hr,hpost,_,two⟩ := contract B c0 r0 hready
  exact ⟨d,r,hr0.trans hr,hpost,two.trans two0⟩

end E5R.Thermostat.MainHeaderFirstTwo
