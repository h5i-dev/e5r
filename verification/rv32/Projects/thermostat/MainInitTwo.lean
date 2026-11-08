import Projects.thermostat.MainBootTwo
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainInitTwo
open E5R E5R.Thermostat MainInit
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (hp : c.pc = 0x80000000#32) (hmpp : c.mpp = 0 ∨ c.mpp = 3)
    (hm : Memory.Block B 0x80ff0000#32 65536) :
    ∃ d r, DetSteps B img 2432 ⟨c,ram⟩ ⟨d,r⟩ ∧ Ready B d r ∧ d.get 18=2#32 ∧
      (∀ x, (∀ i : Fin 65536, x ≠ 0x80ff0000#32+BitVec.ofNat 32 i.val) → r x = ram x) := by
  have hmain : Memory.Block B 0x80ffeb90#32 5232 :=
    Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60304) (m := 5232) hm (by decide) (by decide)
  obtain ⟨c0,r0,hr0,hready0,_,hmask0,hmreg0,hframe0,hfp0,huart0,hone0,hlen0⟩ :=
    Startup.contract_full B c ram hp hmpp hmain
  let c1 := (InitRoutes.execute c0 r0).core
  let r1 := InitRoutes.memory r0
  have hr1 := InitRoutes.contract B c0 r0 hready0.pc hready0.sp hlen0 hmain
  obtain ⟨hpc1,hra1,harg1,hzero1,hlen1,hsp1,hfp1,huart1,hone1,hcsr1⟩ := InitRoutes.fields c0 r0
  have hr1len : c1.get 12 = BitVec.ofNat 32 (4*512) := hlen1.trans hlen0
  have hbuf1 : Memory.Block B 0x80ffec14#32 (4*512) :=
    Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 60436) (m := 2048) hm (by decide) (by decide)
  let r2 := WordZero.writes r1 0x80ffec14#32 512
  obtain ⟨c2,hr2,hpc2,hcsr2,hregs2,hzero2,hframe2⟩ := ZeroMemset.contract B c1 r1 0x80ffec14#32 512
    hpc1 harg1 hzero1 hr1len (by decide) (by decide +kernel) hbuf1 (by decide +kernel)
  have hpc2' : c2.pc = 0x80000942#32 := by rw [hpc2,hra1];decide +kernel
  have hsp2 : c2.get 2 = 0x80ffeb90#32 :=
    (hregs2 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hsp1.trans hready0.sp)
  let c3 := (SecondBuffer.execute c2 r2).core
  have hr3 := SecondBuffer.contract B c2 r2 hpc2' hsp2
  obtain ⟨hpc3,hra3,harg3,hzero3,hlen3,hsp3,hfp3,huart3,hone3,hcsr3⟩ := SecondBuffer.fields c2 r2
  have hbuf2 : Memory.Block B 0x80fff414#32 (4*256) :=
    Memory.sub_block (B := B) (p := 0x80ff0000#32) (n := 65536) (off := 62484) (m := 1024) hm (by decide) (by decide)
  let r4 := WordZero.writes r2 0x80fff414#32 256
  obtain ⟨c4,hr4,hpc4,hcsr4,hregs4,hzero4,hframe4⟩ := ZeroMemset.contract B c3 r2 0x80fff414#32 256
    hpc3 harg3 hzero3 hlen3 (by decide) (by decide +kernel) hbuf2 (by decide +kernel)
  have hpc4' : c4.pc = 0x80000958#32 := by rw [hpc4,hra3];decide +kernel
  have hsp4 : c4.get 2 = 0x80ffeb90#32 :=
    (hregs4 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans (hsp3.trans hsp2)
  let d := LoopEntry.setup c4
  have hr5 := LoopEntry.contract B c4 r4 hpc4' hsp4
  obtain ⟨hpc5,hfuture5,hminus5,hregs5,hcsr5⟩ := LoopEntry.fields c4
  have happ0 : AppState.At r0 Spec.initial :=
    ⟨hready0.state,hready0.available,hready0.keyPtr,hready0.keyLen,hready0.principal⟩
  have happ1 : AppState.At r1 Spec.initial := AppState.preserve r0 r1 Spec.initial happ0 (by
    intro i
    apply InitRoutes.frame
    · exact WordZero.separated 0x80ffebbc#32 0x80ffebd8#32 25 60 (by decide +kernel) (by decide +kernel) i
    · intro j
      exact Ne.symm (WordZero.separated 0x80ffeba0#32 0x80ffebbc#32 4 25 (by decide +kernel) (by decide +kernel) j i))
  have happ2 : AppState.At r2 Spec.initial := AppState.preserve r1 r2 Spec.initial happ1 (by
    intro i
    exact hframe2 _ (WordZero.separated 0x80ffebbc#32 0x80ffec14#32 25 (4*512) (by decide +kernel) (by decide +kernel) i))
  have happ4 : AppState.At r4 Spec.initial := AppState.preserve r2 r4 Spec.initial happ2 (by
    intro i
    exact hframe4 _ (WordZero.separated 0x80ffebbc#32 0x80fff414#32 25 (4*256) (by decide +kernel) (by decide +kernel) i))
  have hroute2 : InitRoutes.Layout r2 := InitRoutes.layout_preserve r1 r2 (InitRoutes.layout r0)
    (by intro i;exact hframe2 _ (WordZero.separated 0x80ffebd8#32 0x80ffec14#32 60 (4*512) (by decide +kernel) (by decide +kernel) i))
    (by intro i;exact hframe2 _ (WordZero.separated 0x80ffeba0#32 0x80ffec14#32 4 (4*512) (by decide +kernel) (by decide +kernel) i))
  have hroute4 : InitRoutes.Layout r4 := InitRoutes.layout_preserve r2 r4 hroute2
    (by intro i;exact hframe4 _ (WordZero.separated 0x80ffebd8#32 0x80fff414#32 60 (4*256) (by decide +kernel) (by decide +kernel) i))
    (by intro i;exact hframe4 _ (WordZero.separated 0x80ffeba0#32 0x80fff414#32 4 (4*256) (by decide +kernel) (by decide +kernel) i))
  have hrx : ∀ i : Fin 2048, r4 (0x80ffec14#32+BitVec.ofNat 32 i.val) = 0#8 := by
    intro i
    change WordZero.writes r2 0x80fff414#32 256 (0x80ffec14#32+BitVec.ofNat 32 i.val) = 0#8
    rw [hframe4 _ (WordZero.separated 0x80ffec14#32 0x80fff414#32 2048 (4*256) (by decide +kernel) (by decide +kernel) i)]
    exact hzero2 i
  have hregs (rr : Reg) (h12 : rr ≠ 12) (h13 : rr ≠ 13) (h14 : rr ≠ 14)
      (h15 : rr ≠ 15) (h16 : rr ≠ 16) (h21 : rr ≠ 21) (h23 : rr ≠ 23)
      (hroute : c1.get rr = c0.get rr) (hsecond : c3.get rr = c2.get rr) : d.get rr = c0.get rr :=
    (hregs5 rr h21 h23).trans ((hregs4 rr h12 h13 h14 h15 h16).trans
      (hsecond.trans ((hregs2 rr h12 h13 h14 h15 h16).trans hroute)))
  have hfp5 : d.get 8 = 0x80fff814#32 :=
    (hregs 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hfp1 hfp3).trans hfp0
  have huart5 : d.get 19 = 0x10000000#32 :=
    (hregs 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) huart1 huart3).trans huart0
  have hone5 : d.get 22 = 1#32 :=
    (hregs 22 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hone1 hone3).trans hone0
  have hcsr : d.sameCsr c0 := hcsr5.trans (hcsr4.trans (hcsr3.trans (hcsr2.trans hcsr1)))
  have hmask5 : d.mie_ = false := (congrArg Prod.fst hcsr).trans hmask0
  have hmreg5 : d.mieReg = 0#32 := (congrArg (fun t => t.2.2.2.1) hcsr).trans hmreg0
  have two1 : c1.get 18=2#32 := MainBootTwo.routes c0 r0
  have two2 : c2.get 18=2#32 := (hregs2 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans two1
  have two3 : c3.get 18=2#32 := (MainBootTwo.second c2 r2).trans two2
  have two4 : c4.get 18=2#32 := (hregs4 18 (by decide) (by decide) (by decide) (by decide) (by decide)).trans two3
  have two5 : d.get 18=2#32 := (MainBootTwo.loop c4).trans two4
  refine ⟨d,r4,((((hr0.trans hr1).trans hr2).trans hr3).trans hr4).trans hr5,
    ⟨hpc5,(hregs5 2 (by decide) (by decide)).trans hsp4,hfp5,huart5,hone5,hfuture5,hminus5,
      hm,happ4,hroute4,hrx,hzero4,hmask5,hmreg5⟩,two5,?_⟩
  intro x hx
  change WordZero.writes r2 0x80fff414#32 256 x = ram x
  rw [hframe4 x (sub_away x 0x80fff414#32 62484 (4*256) hx (by decide +kernel) (by decide))]
  change WordZero.writes r1 0x80ffec14#32 512 x = ram x
  rw [hframe2 x (sub_away x 0x80ffec14#32 60436 (4*512) hx (by decide +kernel) (by decide))]
  change InitRoutes.memory r0 x = ram x
  rw [InitRoutes.frame r0 x
    (sub_away x 0x80ffebd8#32 60376 60 hx (by decide +kernel) (by decide))
    (sub_away x 0x80ffeba0#32 60320 4 hx (by decide +kernel) (by decide))]
  exact hframe0 x (sub_away x 0x80ffeb90#32 60304 5232 hx (by decide +kernel) (by decide))

end E5R.Thermostat.MainInitTwo
