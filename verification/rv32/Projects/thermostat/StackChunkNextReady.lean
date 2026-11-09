import Projects.thermostat.ChunkNextReady
import Projects.thermostat.StackBoard
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackChunkNextReady
open E5R E5R.Thermostat HttpRequestSpec ChunkNextReady
abbrev B := StackBoard.board

theorem contract {c ram input s head result served}
    (h : ChunkSuccessBody.Ready c ram input s head result served)
    (kind : head.framing=.chunked) (countBound : served<100)
    (bounds : MainHeadAcceptedBounds.At 1024 1024 head)
    (contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)) :
    ∃ d, Quiet.Steps B img 408 ⟨c,ram⟩ ⟨d,memory ram head result.written⟩ ∧
      RuntimeNext.Entry d (memory ram head result.written) (ChunkSuccessBody.buffer ram result.read) s head
        result.body.length result.read served (low ram) ∧ d.sameCsr c ∧
      ViewFrame.Region ram (memory ram head result.written) (sp+72#32) 60 ∧
      ViewFrame.Region ram (memory ram head result.written) (sp+16#32) 4 ∧ ViewFrame.Region ram (memory ram head result.written) (sp+3204#32) 84 := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block StackBoard.available (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have offset (a b : Nat) : (sp+BitVec.ofNat 32 a)+BitVec.ofNat 32 b=sp+BitVec.ofNat 32 (a+b) := by rw [BitVec.add_assoc,←BitVec.ofNat_add]
  have fpEq : sp+3204#32=fp := by decide +kernel
  obtain ⟨a,guard,apc,ar,ac⟩ := ChunkDoneBranch.contract B c ram h.doneTag h.two h.pc
  obtain ⟨b,loads,bpc,b12,b10,b11,b9,b18,b27,br,bc⟩ := ChunkNextLoads.contract B a ram sp (high0 ram) (high1 ram) (high2 ram) 2#32 (low ram)
    ((ar 2).trans h.stable.sp) (by simpa only [fpEq] using (ar 8).trans h.stable.fp) rfl rfl rfl
    (by simpa only [kind,HeadCompletedView.framingTag] using h.view.tag)
    (by simpa only [offset] using h.view.padding) rfl stack (by decide) apc
  have b2 := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 2).trans h.stable.sp)
  have b8 := (br 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 8).trans h.stable.fp)
  obtain ⟨z,stores,zpc,_,_,_,zr,zc⟩ := ChunkNextStores.contract B b ram sp _ _ _ _ (high0 ram) (high1 ram) (high2 ram)
    b2 (by simpa only [fpEq] using b8) b10 b11 b12
    (by simpa only [offset] using h.view.methodStart) (by simpa only [offset] using h.view.methodEnd)
    (by simpa only [offset] using h.view.targetStart) (by simpa only [offset] using h.view.targetEnd) stack (by decide) bpc
  have z2 := (zr 2 (by decide) (by decide) (by decide)).trans b2
  obtain ⟨v,call,vpc,v10,v12,v11,v1,vr,vc⟩ := ChunkNextCall.contract B z (stored ram head) sp z2 zpc
  have v2 := (vr 2 (by decide) (by decide) (by decide) (by decide)).trans z2
  obtain ⟨e,copy,ret,_⟩ := MainNextCopy264.contract B v (stored ram head) sp 3352 (Or.inl rfl) vpc v2 v10 v11 v12 stack (by decide)
  have epc : e.pc=0x800010ce#32 := by rw [ret.pc,v1];decide +kernel
  have copiedRegs (rr : Reg) (safe : rr∈MainSavedGpr.regs) : e.get rr=v.get rr := by
    have casesReg : rr=2 ∨ rr=8 ∨ rr=9 ∨ rr=18 ∨ rr=19 ∨ rr=20 ∨ rr=21 ∨ rr=22 ∨ rr=23 ∨ rr=24 ∨ rr=25 ∨ rr=26 ∨ rr=27 := by
      simpa only [MainSavedGpr.regs,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using safe
    rcases casesReg with he|he|he|he|he|he|he|he|he|he|he|he|he <;> subst rr
    all_goals first | exact ret.sp | exact ret.x8 | exact ret.x9 | exact ret.x18 | exact ret.x19 | exact ret.x20 | exact ret.x21 | exact ret.x22 | exact ret.x23 | exact ret.x24 | exact ret.x25 | exact ret.x26 | exact ret.x27
  have back (rr : Reg) (safe : rr∈MainSavedGpr.regs) : e.get rr=b.get rr := by
    have neq : ∀ rr : Reg, rr∈MainSavedGpr.regs → rr≠10 ∧ rr≠12 ∧ rr≠11 ∧ rr≠1 ∧ rr≠13 := by decide +kernel
    obtain ⟨n10,n12,n11,n1,n13⟩ := neq rr safe
    exact (copiedRegs rr safe).trans ((vr rr n10 n12 n11 n1).trans (zr rr n13 n11 n10))
  have firstFrame (off size : Nat) (lo : 40≤off) (hi : off+size≤4904) : ViewFrame.Region ram (copied ram head) (sp+BitVec.ofNat 32 off) size := by
    apply HeadRegionFrame.trans (ChunkNextStoreMemory.region ram sp _ _ _ _ (high0 ram) (high1 ram) (high2 ram) off size lo (by omega))
    exact MainNextCopy264.frame (stored ram head) sp 3352 off size (by omega) (Or.inl hi)
  have word (off : Nat) (lo : 40≤off) (hi : off+4≤4904) : ramRead (copied ram head) (sp+BitVec.ofNat 32 off) .w=ramRead ram (sp+BitVec.ofNat 32 off) .w := by
    simpa only [BitVec.add_zero] using ViewFrame.word (firstFrame off 4 lo hi) 0 (by decide)
  have copiedHead := MainCopyView.head (firstFrame 3320 304 (by decide) (by decide)) head h.view
  have minorByte : extend .b false (ramRead (copied ram head) (sp+3616#32) .b)=BitVec.ofNat 32 head.minor := by
    have v : copied ram head (sp+3616#32)=BitVec.ofNat 8 head.minor := by simpa only [offset] using copiedHead.version
    rw [Memory.load_byte,v,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show head.minor<2^8 by have := bounds.version;omega)]
  obtain ⟨d,tail,dpc,_,_,_,_,_,_,_,d20,d25,dr,dc⟩ := ChunkNextTail.contract B e (copied ram head) sp
    (BitVec.ofNat 32 head.len) (BitVec.ofNat 32 result.written) (BitVec.ofNat 32 head.minor)
    (pad ram head 0) (pad ram head 1) (pad ram head 2) (pad ram head 3) (pad ram head 4) (pad ram head 5) (pad ram head 6)
    (ret.sp.trans v2) (by simpa only [fpEq] using (back 8 (by decide)).trans b8) stack (by decide)
    ((word 3648 (by decide) (by decide)).trans h.consumed) ((word 3660 (by decide) (by decide)).trans h.writeWord)
    minorByte rfl rfl rfl rfl rfl rfl rfl epc
  let after := memory ram head result.written
  have tailFrame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤40 ∨ 44≤off) (padApart : off+size≤4896 ∨ 4903≤off) :
      ViewFrame.Region (copied ram head) after (sp+BitVec.ofNat 32 off) size := ChunkNextTailMemory.region _ sp _ _ _ _ _ _ _ _ _ _ off size bound apart padApart
  have frame (off size : Nat) (lo : 44≤off) (hi : off+size≤4896) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size :=
    HeadRegionFrame.trans (firstFrame off size (by omega) (by omega)) (tailFrame off size (by omega) (Or.inr lo) (Or.inl hi))
  have capacityFrame : ViewFrame.Region ram after (sp+16#32) 4 := by
    apply HeadRegionFrame.trans (ChunkNextStoreMemory.low ram sp (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2)
      (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (high0 ram) (high1 ram) (high2 ram) 16 4 (by decide))
    apply HeadRegionFrame.trans (MainNextCopy264.frame (stored ram head) sp 3352 16 4 (by decide) (Or.inl (by decide)))
    exact tailFrame 16 4 (by decide) (Or.inl (by decide)) (Or.inl (by decide))
  have keepB (rr : Reg) (safe : rr∈[2,8,9,18,19,21,22,23,24,26,27]) : d.get rr=b.get rr := by
    have neq : ∀ rr : Reg, rr∈[2,8,9,18,19,21,22,23,24,26,27] → rr∈MainSavedGpr.regs ∧ rr≠16 ∧ rr≠10 ∧ rr≠11 ∧ rr≠12 ∧ rr≠13 ∧ rr≠14 ∧ rr≠15 ∧ rr≠20 ∧ rr≠25 := by decide +kernel
    obtain ⟨member,a,b,c,f,g,i,j,k,l⟩ := neq rr safe
    exact (dr rr a b c f g i j k l).trans (back rr member)
  have keep (rr : Reg) (safe : rr∈[2,8,19,21,22,23,24,26]) : d.get rr=c.get rr := by
    have neq : ∀ rr : Reg, rr∈[2,8,19,21,22,23,24,26] → rr∈[2,8,9,18,19,21,22,23,24,26,27] ∧ rr≠12 ∧ rr≠10 ∧ rr≠11 ∧ rr≠9 ∧ rr≠18 ∧ rr≠27 := by decide +kernel
    obtain ⟨member,n12,n10,n11,n9,n18,n27⟩ := neq rr safe
    exact (keepB rr member).trans ((br rr n12 n10 n11 n9 n18 n27).trans (ar rr))
  have csr := (((((dc.trans ret.csr).trans vc).trans zc).trans bc).trans ac)
  have stable : MainTransactionStable.At d after (ChunkSuccessBody.buffer ram result.read) s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,?_,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · have v := ViewFrame.word (frame 3288 4 (by decide) (by decide)) 0 (by decide)
      simpa only [BitVec.add_zero,show sp+3288#32=fp+84#32 by decide +kernel] using v.trans h.stable.filled
    · intro i
      have region := frame 132 2048 (by decide) (by decide)
      exact (region ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩).trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (by decide)
  have sourceHead := ChunkNextStoreMemory.head ram sp (BitVec.ofNat 32 head.method.1) (BitVec.ofNat 32 head.method.2) (BitVec.ofNat 32 head.target.1) (BitVec.ofNat 32 head.target.2) (high0 ram) (high1 ram) (high2 ram) head h.view
  have array := MainNextArrayFrame.preserve (MainNextArrayView.fixed (stored ram head) sp head stack sourceHead)
    (tailFrame 4904 264 (by decide) (Or.inr (by decide)) (Or.inr (by decide)))
  have metadata (off : Nat) (bound : off+4≤40) : ramRead after (sp+BitVec.ofNat 32 off) .w=ramRead (stored ram head) (sp+BitVec.ofNat 32 off) .w := by
    have region := HeadRegionFrame.trans (MainNextCopy264.frame (stored ram head) sp 3352 off 4 (by omega) (Or.inl (by omega)))
      (tailFrame off 4 (by omega) (Or.inl bound) (Or.inl (by omega)))
    simpa only [BitVec.add_zero] using ViewFrame.word region 0 (by decide)
  refine ⟨d,((((guard.trans loads).trans stores).trans call).trans copy).trans tail,
    ⟨dpc,stable,MainGprBank.preserve (fun rr member => keep rr (by
      have sub : ∀ rr : Reg, rr∈[21,23,26] → rr∈[2,8,19,21,22,23,24,26] := by decide +kernel
      exact sub rr member)) h.bank,
      MainServeLayout.preserve (fun off safe => by
        have bound := MainServeLayout.bounds off safe
        have w := ViewFrame.word (frame (3204+off) 4 (by omega) (by omega)) 0 (by decide)
        simpa only [BitVec.add_zero,BitVec.ofNat_add,←BitVec.add_assoc,fpEq] using w) h.serve,countBound,
      (by simpa only [kind,HeadCompletedView.framingTag] using (keepB 9 (by decide)).trans b9),
      (keepB 18 (by decide)).trans b18,(keepB 27 (by decide)).trans b27,d20,(keep 24 (by decide)).trans h.usedReg,
      (by simpa only [h.bodyLength] using d25),MainCopyView.head (frame 3320 304 (by decide) (by decide)) head h.view,array,
      (metadata 28 (by decide)).trans (ChunkNextStoreMemory.methodStart ram sp _ _ _ _ _ _ _),
      (metadata 24 (by decide)).trans (ChunkNextStoreMemory.methodEnd ram sp _ _ _ _ _ _ _),
      (metadata 36 (by decide)).trans (ChunkNextStoreMemory.targetStart ram sp _ _ _ _ _ _ _),
      (metadata 32 (by decide)).trans (ChunkNextStoreMemory.targetEnd ram sp _ _ _ _ _ _ _),
      ChunkNextTailMemory.minor_word _ sp _ _ _ _ _ _ _ _ _ _,bounds,Or.inr kind,h.bodyBound,h.extent.1,
      (by simp only [ChunkSuccessBody.buffer,List.length_ofFn];exact Nat.le_refl _),contained⟩,csr,frame 72 60 (by decide) (by decide),capacityFrame,frame 3204 84 (by decide) (by decide)⟩
end E5R.Thermostat.StackChunkNextReady
