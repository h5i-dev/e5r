-- G3: preserve initialized routes across the actual general close call.
import Projects.thermostat.MainRouterRequestFrames
import Projects.thermostat.MainCloseRequest
set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.MainCloseScanned
open E5R E5R.Thermostat HttpRequestSpec
theorem contract_routes {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) (routes : MainRouterTable.At ram) (notForced : ¬(head.minor=0 ∨ 100≤served)) :
    ∃ n d after, n≤(77+86*(MainRequestSpans.raw input head amount).length)*(MainRequestInputs.entries head).length+71 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainCloseReady.At d after input s head amount served
        (MainCloseSpec.wantsClose (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)) ∧ d.sameCsr c ∧ MainRouterTable.At after := by
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  have saveBlock : Memory.Block B savedSp 48 := by
    have block := Memory.sub_block h.stable.stack (off := 60256) (m := 48) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60256#32=savedSp by decide +kernel] using block
  obtain ⟨first,a,nb,dispatch,pa,a10,a20,a21,a24,a25,a1,ar,ac⟩ := MainCloseDispatch.contract B c ram sp head.minor served h.bounds.version h.countBound h.pc h.stable.sp
    (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp) h.minorReg h.countReg stack (by decide +kernel)
    (by simpa only [show fp+44#32=sp+3248#32 by decide +kernel,show sp+3204#32=fp by decide +kernel] using h.serve.config)
    (by simpa only [show fp+8#32=sp+3212#32 by decide +kernel] using h.serve.requests)
  have ap : a.pc=0x800023f2#32 := by simpa only [MainCloseDispatch.forced,notForced,ite_false] using pa
  have arg : a.get 10=MainRequestInputs.req := by simpa only [MainCloseDispatch.forced,notForced,ite_false] using a10
  have a2 : a.get 2=savedSp+48#32 := by
    rw [(ar 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)),h.stable.sp];decide +kernel
  have aReturn : a.get 1=0x80001276#32 := a1 notForced
  have limit : (MainRequestSpans.raw input head amount).length≤2048 := by
    rw [MainRequestSpans.raw_length h];have := h.available;have := h.stable.bound;omega
  have requestSeparate : ∀ i : Fin 372, ∀ j : Fin 48, MainRequestInputs.req+BitVec.ofNat 32 i.val≠savedSp+BitVec.ofNat 32 j.val := by
    intro i j
    have disjoint := FrameOffsets.ne savedSp 3360 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [show savedSp+3360#32=MainRequestInputs.req by decide +kernel,BitVec.add_zero] using disjoint
  have rawSeparate : ∀ i : Fin (MainRequestSpans.raw input head amount).length, ∀ j : Fin 48, rx+BitVec.ofNat 32 i.val≠savedSp+BitVec.ofNat 32 j.val := by
    intro i j
    have disjoint := FrameOffsets.ne savedSp 180 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [show savedSp+180#32=rx by decide +kernel,BitVec.add_zero] using disjoint
  obtain ⟨m,b,mb,scan,pb,b10,br,bc⟩ := MainWantsClose.contract B a ram savedSp MainRequestInputs.req rx
    (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) (MainRequestInputs.headers h) limit ap a2 arg saveBlock (by decide +kernel) requestSeparate rawSeparate
  let r0 := MainCloseSave.memory ram savedSp a
  let close := MainCloseSpec.wantsClose (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head)
  let word : Word := if close then 1#32 else 0#32
  have bp : b.pc=0x80001276#32 := by rw [pb,aReturn];decide +kernel
  let e := b.goto 0x8000128c#32
  have back : Quiet.Step B img ⟨b,r0⟩ ⟨e,r0⟩ := by
    refine QuietDet.step_of (by rw [bp];decide) (by rw [bp];exact re2147488374) fun o => ?_
    rw [exec_jal,bp]
    change interp B img o (jump b 0x8000128c#32) r0 0 []=_
    rw [jump_ok _ _ (by decide)];rfl
  have scanFrame (off size : Nat) (bound : off+size≤5232) : ViewFrame.Region ram r0 (sp+BitVec.ofNat 32 off) size := by
    intro i;apply MainCloseSave.frame
    intro j
    have disjoint := FrameOffsets.ne savedSp (48+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show savedSp+48#32=sp by decide +kernel,BitVec.add_zero] using disjoint
  have capacity : ramRead r0 (sp+3272#32) .w=1024#32 :=
    (ViewFrame.word (scanFrame 3272 4 (by decide)) 0 (by decide)).trans (by simpa only [BitVec.add_zero,show sp+3272#32=fp+68#32 by decide +kernel] using h.serve.txCapacity)
  have e8 : e.get 8=sp+3204#32 := (br 8 (by decide)).trans ((ar 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans (by simpa only [show sp+3204#32=fp by decide +kernel] using h.stable.fp))
  obtain ⟨d,commit,pc,d12,d10,dr,dc⟩ := MainCloseCommit.contract B e r0 sp word e8 b10 stack (by decide +kernel) capacity rfl
  let after := MainCloseCommit.memory r0 sp word
  have frame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3304 ∨ 3305≤off) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size := by
    intro i;exact (MainCloseCommitFrame.frame r0 sp word off size bound apart i).trans (scanFrame off size bound i)
  have keep (r : Reg) (safe : r∈[2,8,9,18,19,22,23,26,27]) : d.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,9,18,19,22,23,26,27] → r≠10 ∧ r≠11 ∧ r≠12 ∧ r≠20 ∧ r≠21 ∧ r≠24 ∧ r≠25 ∧ r≠1 := by decide +kernel
    obtain ⟨a,b,e,f,g,i,j,k⟩ := ne r safe
    have member : r∈[1,2,3,4,8,9,18,19,20,21,22,23,24,25,26,27] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at safe ⊢
      rcases safe with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    exact (dr r e a).trans ((br r member).trans (ar r a b f g i j k))
  have future : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have d20 : d.get 20=5#32 := (dr 20 (by decide) (by decide)).trans ((br 20 (by decide)).trans a20)
  have d21 : d.get 21=6#32 := (dr 21 (by decide) (by decide)).trans ((br 21 (by decide)).trans a21)
  have d24 : d.get 24=sp+3740#32 := (dr 24 (by decide) (by decide)).trans ((br 24 (by decide)).trans a24)
  have d25 : d.get 25=sp+3784#32 := (dr 25 (by decide) (by decide)).trans ((br 25 (by decide)).trans a25)
  have csr := dc.trans (bc.trans ac)
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word future 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,(congrArg Prod.fst csr).trans h.stable.masked⟩
    · intro i
      have byte := frame 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
  have stored := MainRequestStored.preserve (MainRequestStored.fromReady h) (frame 3312 376 (by decide) (Or.inr (by decide)))
  have flag : after (sp+3304#32)=Encoding.boolByte close := by
    have byte := MainCloseCommitFrame.byte r0 sp word
    change MainCloseCommit.memory r0 sp word (sp+3304#32)=Encoding.boolByte close
    rw [byte]
    change byteOf (if close then 1#32 else 0#32) 0=Encoding.boolByte close
    cases close <;> decide +kernel
  have spec : close=MainCloseSpec.mustClose head.minor served (MainRequestSpans.raw input head amount) (MainRequestInputs.entries head) := by
    have minor : head.minor≠0 := fun eq => notForced (Or.inl eq)
    have room : served<100 := by have not100 : ¬100≤served := fun reached => notForced (Or.inr reached);omega
    exact (MainCloseSpec.persistent _ _ minor room _ _).symm
  refine ⟨first+m+1+4,d,after,by omega,((dispatch.trans scan).trans (.single back)).trans commit,⟨pc,stable,stored,MainServeLayout.preserve (MainServeMemoryFrames.whole future (by decide)) h.serve,h.countBound,h.positive,
    (keep 18 (by decide)).trans h.countReg,(keep 9 (by decide)).trans h.minorReg,(keep 23 (by decide)).trans h.future,
    (keep 26 (by decide)).trans h.three,(keep 27 (by decide)).trans h.low,d20,d21,d24,d25,d12,d10,
    (ViewFrame.word future 92 (by decide)).trans h.usedWord,flag,spec⟩,csr,?_⟩
  apply MainRouterTable.preserve routes
  simpa only [ViewFrame.Region,show sp+72#32=0x80ffebd8#32 by decide +kernel] using frame 72 60 (by decide) (Or.inl (by decide))
end E5R.Thermostat.MainCloseScanned

namespace E5R.Thermostat.MainCloseRequest
open E5R E5R.Thermostat HttpRequestSpec

theorem contract_routes {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) (routes : MainRouterTable.At ram) :
    ∃ n d after close,
      n≤(77+86*(MainRequestSpans.raw input head amount).length)*(MainRequestInputs.entries head).length+71 ∧
      Quiet.Steps MainRequestBuild.B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainCloseReady.At d after input s head amount served close ∧ d.sameCsr c ∧ MainRouterTable.At after := by
  by_cases force : head.minor=0 ∨ 100≤served
  · obtain ⟨n,d,nb,trace,ready,csr⟩ := MainCloseForced.contract h force
    have table : MainRouterTable.At (MainCloseCommit.memory ram MainRequestBuild.sp 1#32) := by
      apply MainRouterTable.preserve routes
      simpa only [ViewFrame.Region,show MainRequestBuild.sp+72#32=0x80ffebd8#32 by decide +kernel] using MainCloseCommitFrame.frame ram MainRequestBuild.sp 1#32 72 60 (by decide) (Or.inl (by decide))
    exact ⟨n,d,_,true,by omega,trace,ready,csr,table⟩
  · obtain ⟨n,d,after,nb,trace,ready,csr,table⟩ := MainCloseScanned.contract_routes h routes force
    exact ⟨n,d,after,_,nb,trace,ready,csr,table⟩
end E5R.Thermostat.MainCloseRequest
