import Projects.thermostat.HeadFieldsStartStorage
import Projects.thermostat.HeadFieldsLoopComplete
namespace E5R.Thermostat.HeadFieldsInitializedComplete
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

/-- Actual F0E initialization and all header iterations, with empty fields
    derived from the real memset, body metadata derived from the real config
    load/stores, and original receive bytes preserved. Result cutpoints still
    precede the More/Bad/Done ABI-return implementations. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hc : cap≤1024)
    (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp values)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 239≤n ∧ n≤257+HeadFieldsLoopComplete.budget cap 0 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadFieldsLoopComplete.At d after sp length minor (fields g cap minor 1024 (j+2) Fields.empty) ∧
      ViewFrame.Region ram after (sp+20#32) 36 ∧ ViewFrame.Region ram after (sp+327#32) 4985 ∧
      HeadSaved.At after sp values ∧ d.get 2=sp ∧ d.sameCsr c ∧
      (j+2<cap → HeadFieldsMeta.At after sp length cap) := by
  let g := bytes ram (sp+516#32)
  obtain ⟨n,a,mid,lo,hi,init,next,fieldsMid,scratch,rx,app,saved,stackMid,csr,metadataMid,tail⟩ := HeadFieldsStartStorage.contract B c ram sp m te j minor length cap values ready hbody hj hc stack aligned stored
  by_cases full : cap≤j+2
  · have pc : a.pc=0x800033ea#32 := by simpa only [full,ite_true] using next
    have result : fields g cap minor 1024 (j+2) Fields.empty=.more := by rw [fields,ite_eq_right (by omega)]
    change ∃ n d after, _
    rw [show fields (bytes ram (sp+516#32)) cap minor 1024 (j+2) Fields.empty=.more from result]
    exact ⟨n,a,mid,lo,by omega,init,pc,scratch,tail,saved,stackMid,csr,fun impossible => by omega⟩
  · have inside : j+2<cap := by omega
    have regs : HeadFieldsRegs.At a sp (j+2) length minor Fields.empty := by simpa only [full,ite_false] using next
    have agree (k : Nat) (hk : k<cap) : bytes mid (sp+516#32) k=g k :=
      congrArg BitVec.toNat (rx ⟨k,by omega⟩)
    obtain ⟨steps,d,after,slo,shi,loop,result,metadataAfter,constantsAfter,frames,regFrame,csr2⟩ := HeadFieldsLoopComplete.contract B a mid sp g
      (j+2) cap length minor Fields.empty regs (metadataMid inside) fieldsMid agree inside upper bound version stack aligned clOutside teOutside
    have stackAfter : d.get 2=sp := constantsAfter.stack
    have savedAfter : HeadSaved.At after sp values := HeadSavedTail.preserve saved (frames 332 52 (by decide) (by decide))
    have scratchAfter : ViewFrame.Region ram after (sp+20#32) 36 :=
      HeadRegionFrame.trans scratch (frames 20 36 (by decide) (by decide))
    have tailAfter : ViewFrame.Region ram after (sp+327#32) 4985 :=
      HeadRegionFrame.trans tail (frames 327 4985 (by decide) (by decide))
    exact ⟨n+steps,d,after,by omega,by simpa only [Fields.empty,List.length_nil] using Nat.add_le_add hi shi,
      init.trans loop,result,scratchAfter,tailAfter,savedAfter,stackAfter,csr2.trans csr,fun _ => metadataAfter⟩
end E5R.Thermostat.HeadFieldsInitializedComplete
