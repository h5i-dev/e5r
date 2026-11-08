import Projects.thermostat.HeadFieldsInitializedComplete
import Projects.thermostat.HeadFieldsFinish
namespace E5R.Thermostat.HeadFieldsWhole
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual initialized fields parser through the complete result and ABI return.
    Names and values are computed from the original receive-buffer bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hc : cap≤1024)
    (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp values)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 260≤n ∧ n≤649+HeadFieldsLoopComplete.budget cap 0 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadFinalResult.At after (sp+4904#32)
        (HeadFieldsFinish.result length m (m+1) te minor (fields g cap minor 1024 (j+2) Fields.empty)) ∧
      (∀ off size : Nat, 327≤off → off+size≤5312 → (off+size≤4904 ∨ 5201≤off) → ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size) ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  obtain ⟨n,a,mid,lo,hi,init,cut,scratch,tail,saved,asp,ac,_⟩ := HeadFieldsInitializedComplete.contract B c ram sp m te j minor length cap values ready hbody hj hc upper bound version stack aligned stored clOutside teOutside
  have word (off : Nat) (lower : 20≤off) (upper : off+4≤56) : ramRead mid (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    have region := HeadRegionFrame.offset scratch off 4 lower (by omega)
    simpa only [BitVec.add_zero] using ViewFrame.word region 0 (by decide)
  obtain ⟨steps,d,after,slo,shi,finish,dpc,dsp,regs,view,frames,dc⟩ := HeadFieldsFinish.contract B a mid sp length cap m (m+1) te minor
    (fields g cap minor 1024 (j+2) Fields.empty) values cut (HeadFieldsResultSpec.fields g cap minor 1024 (j+2) Fields.empty) asp version bound
    ((word 48 (by decide) (by decide)).trans ready.lengthWord) ((word 36 (by decide) (by decide)).trans ready.maxHead)
    ((word 52 (by decide) (by decide)).trans ready.output) ((word 20 (by decide) (by decide)).trans ready.methodEnd)
    ((word 24 (by decide) (by decide)).trans ready.targetStart) ((word 28 (by decide) (by decide)).trans ready.targetEnd) stack aligned saved
  refine ⟨n+steps,d,after,by omega,by omega,init.trans finish,dpc,dsp,regs,view,?_,dc.trans ac⟩
  intro off size lower upper apart
  exact HeadRegionFrame.trans (HeadRegionFrame.offset tail off size lower (by omega)) (frames off size upper apart)
end E5R.Thermostat.HeadFieldsWhole
