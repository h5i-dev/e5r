import Projects.thermostat.HeadHeaderCommitMath
import Projects.thermostat.HeadHeaderCommitView
import Projects.thermostat.HeadHeaderCommitFrame
import Projects.thermostat.HeadHeaderValuesRaw
import Projects.thermostat.HeadHeaderNamesRaw
import Projects.thermostat.HeadHeaderFinishRaw
import Projects.thermostat.HeadHeaderTeGuard
import Projects.thermostat.HeadHeaderNextRaw
import Projects.thermostat.HeadHeaderNextBranch
import Projects.thermostat.HeadFieldsConstants
namespace E5R.Thermostat.HeadHeaderCommit
open E5R E5R.Thermostat HttpRequestSpec

/-- The complete actual common header commit: all five sequential RAM stores,
    real count/TE/name-end reloads, niche guard and actual next-loop branch.
    The TE register is derived from the RAM flag, not assumed updated early. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (entry : Field) (le length cap minor : Nat) (f : Fields)
    (hp : c.pc=0x800033b6#32) (constants : HeadFieldsConstants.At c sp length minor)
    (fields : HeadFieldsView.At ram sp f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h24 : c.get 24=BitVec.ofNat 32 entry.ns)
    (h15 : c.get 15=BitVec.ofNat 32 entry.vs) (h25 : c.get 25=BitVec.ofNat 32 entry.ve)
    (h21 : c.get 21=BitVec.ofNat 32 (le-entry.ns)) (hname : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 entry.ne)
    (room : f.headers.length<16) (lower : entry.ns≤le) (upper : le≤cap) (hcap : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) :
    let after := HeadHeaderCommitMemory.memory ram sp f.headers.length entry
    let nextFields := {f with headers := f.headers++[entry]}
    ∃ d, Quiet.Steps B img 18 ⟨c,ram⟩ ⟨d,after⟩ ∧
      (if le+2<cap then HeadFieldsRegs.At d sp (le+2) length minor nextFields else d.pc=0x800033ea#32) ∧
      HeadFieldsView.At after sp nextFields ∧ HeadFieldsMeta.At after sp length cap ∧
      d.get 9=BitVec.ofNat 32 nextFields.headers.length ∧ d.get 24=BitVec.ofNat 32 (le+2) ∧
      d.get 23=(if f.te then 1#32 else 0#32) ∧
      (∀ r : Reg, r≠9 → r≠10 → r≠23 → r≠11 → r≠21 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c := by
  let n := f.headers.length
  let p := HeadHeaderCommitMath.slot sp n
  let vRAM := HeadHeaderCommitMemory.values ram sp n entry
  let nRAM := HeadHeaderCommitMemory.names ram sp n entry
  let after := HeadHeaderCommitMemory.memory ram sp n entry
  let teWord := BitVec.ofNat 32 (HeadFieldsView.flag f.te).toNat
  let nextFields := {f with headers := f.headers++[entry]}
  have stack : Memory.Block B sp 327 := by simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 327) (by decide) (by decide)
  have pmem : Memory.Block B p 16 := HeadHeaderCommitMath.block B sp n room hm
  have palign : p.toNat%4=0 := HeadHeaderCommitMath.aligned sp n ha
  have off (k : Nat) : p+BitVec.ofNat 32 k=sp+BitVec.ofNat 32 (56+k+16*n) := by
    simpa only [show 56+16*n+k=56+k+16*n by omega] using HeadHeaderCommitMath.offset sp n k
  have slotValue : (sp+56#32)+alu .sll (BitVec.ofNat 32 n) 4#32=p := by
    rw [HeadHeaderCommitMath.shift n (by omega)]
    rfl
  obtain ⟨a,values,pcA,shift,pointerA,frameA,csrA⟩ := HeadHeaderValuesRaw.contract B c ram sp (BitVec.ofNat 32 n) p
    (BitVec.ofNat 32 entry.vs) (BitVec.ofNat 32 entry.ve) constants.stack h9 h15 h25 slotValue pmem palign hp
  have valuesEq : HeadHeaderValuesRaw.memory ram sp (BitVec.ofNat 32 n) p (BitVec.ofNat 32 entry.vs) (BitVec.ofNat 32 entry.ve)=vRAM := by
    unfold HeadHeaderValuesRaw.memory vRAM HeadHeaderCommitMemory.values
    rw [off 8,off 12]
  rw [valuesEq] at values
  have valueCount : ramRead vRAM (sp+320#32) .w=BitVec.ofNat 32 n :=
    (HeadHeaderCommitFrame.values_word ram sp n entry 320 room (by decide) (by omega)).trans fields.count
  have valueTE : vRAM (sp+326#32)=HeadFieldsView.flag f.te := by
    have b := HeadHeaderCommitFrame.values_region ram sp n entry 326 1 room (by decide) (by omega) ⟨0,by decide⟩
    have same : vRAM (sp+326#32)=ram (sp+326#32) := by simpa only [BitVec.add_zero] using b
    exact same.trans fields.te
  have flagWord : BitVec.ofNat 32 (vRAM (sp+326#32)).toNat=teWord := congrArg (fun b : BitVec 8 => BitVec.ofNat 32 b.toNat) valueTE
  obtain ⟨b,names,pcB,countB,teB,frameB,csrB⟩ := HeadHeaderNamesRaw.contract B a vRAM sp p (BitVec.ofNat 32 entry.ns) (BitVec.ofNat 32 n) teWord
    ((frameA 2 (by decide) (by decide)).trans constants.stack) pointerA ((frameA 24 (by decide) (by decide)).trans h24)
    valueCount flagWord stack ha pmem palign pcA
  have namesEq : HeadHeaderNamesRaw.memory vRAM sp p (BitVec.ofNat 32 entry.ns) (BitVec.ofNat 32 n) teWord=nRAM := by
    unfold HeadHeaderNamesRaw.memory nRAM HeadHeaderCommitMemory.names
    rw [off 0]
  rw [namesEq] at names
  have sourceB (r : Reg) (h9 : r≠9) (h10 : r≠10) (h23 : r≠23) : b.get r=c.get r :=
    (frameB r h9 h23).trans (frameA r h9 h10)
  have countNext : b.get 9=BitVec.ofNat 32 (n+1) := countB.trans (BitVec.ofNat_add n 1).symm
  have nameWord : ramRead nRAM (sp+4#32) .w=BitVec.ofNat 32 entry.ne :=
    (HeadHeaderCommitFrame.names_word ram sp n entry 4 room (by decide) (by omega)).trans hname
  obtain ⟨e,finish,pcC,nameEnd,frameC,csrC⟩ := HeadHeaderFinishRaw.contract B b nRAM sp p (BitVec.ofNat 32 entry.ne) (BitVec.ofNat 32 (n+1))
    ((sourceB 2 (by decide) (by decide) (by decide)).trans constants.stack)
    ((frameB 10 (by decide) (by decide)).trans pointerA) countNext nameWord stack ha pmem palign pcB
  have finishEq : HeadHeaderFinishRaw.memory nRAM sp p (BitVec.ofNat 32 entry.ne) (BitVec.ofNat 32 (n+1))=after := by
    unfold HeadHeaderFinishRaw.memory after HeadHeaderCommitMemory.memory
    rw [off 4]
  rw [finishEq] at finish
  have sourceC (r : Reg) (h9 : r≠9) (h10 : r≠10) (h23 : r≠23) (h11 : r≠11) : e.get r=c.get r :=
    (frameC r h11).trans (sourceB r h9 h10 h23)
  obtain ⟨g,guard,pcG,two,frameG,csrG⟩ := HeadHeaderTeGuard.contract B e after teWord
    ((frameC 23 (by decide)).trans teB) (HeadHeaderCommitMath.te_guard f.te) pcC
  have sourceG (r : Reg) (h9 : r≠9) (h10 : r≠10) (h23 : r≠23) (h11 : r≠11) : g.get r=c.get r :=
    (frameG r h10).trans (sourceC r h9 h10 h23 h11)
  have metaAfter : HeadFieldsMeta.At after sp length cap := HeadHeaderCommitFrame.metadata room metadata
  obtain ⟨i,next,pcN,lineEnd,nextIndex,limit,frameN,csrN⟩ := HeadHeaderNextRaw.contract B g after sp
    (BitVec.ofNat 32 (le-entry.ns)) (BitVec.ofNat 32 entry.ns) (BitVec.ofNat 32 cap)
    ((sourceG 2 (by decide) (by decide) (by decide) (by decide)).trans constants.stack)
    ((sourceG 21 (by decide) (by decide) (by decide) (by decide)).trans h21)
    ((sourceG 24 (by decide) (by decide) (by decide) (by decide)).trans h24) metaAfter.limit stack ha pcG
  have sum : BitVec.ofNat 32 (le-entry.ns)+BitVec.ofNat 32 entry.ns=BitVec.ofNat 32 le := HeadHeaderCommitMath.line_sum entry.ns le lower
  have position : i.get 24=BitVec.ofNat 32 (le+2) := nextIndex.trans (by rw [sum,HeadHeaderCommitMath.next])
  obtain ⟨d,branch,pcD,frameD,csrD⟩ := HeadHeaderNextBranch.contract B i after (BitVec.ofNat 32 (le+2)) (BitVec.ofNat 32 cap)
    (decide (le+2<cap)) pcN position limit (HeadHeaderCommitMath.test le cap (by omega) (by omega))
  have frame (r : Reg) (h9 : r≠9) (h10 : r≠10) (h23 : r≠23) (h11 : r≠11) (h21 : r≠21) (h24 : r≠24) : d.get r=c.get r :=
    (frameD r).trans ((frameN r h21 h24 h10).trans (sourceG r h9 h10 h23 h11))
  have finalConstants : HeadFieldsConstants.At d sp length minor := by
    apply HeadFieldsConstants.preserve constants
    intro r hr
    obtain ⟨h9,h10,h23,h11,h21,h24⟩ := HeadFieldsConstants.commit_regs r hr
    exact frame r h9 h10 h23 h11 h21 h24
  have finalCount : d.get 9=BitVec.ofNat 32 nextFields.headers.length := by
    have got : d.get 9=BitVec.ofNat 32 (n+1) :=
      (frameD 9).trans ((frameN 9 (by decide) (by decide) (by decide)).trans
        ((frameG 9 (by decide)).trans ((frameC 9 (by decide)).trans countNext)))
    simpa only [nextFields,List.length_append,List.length_cons,List.length_nil] using got
  have finalPosition : d.get 24=BitVec.ofNat 32 (le+2) := (frameD 24).trans position
  have finalTE : d.get 23=(if f.te then 1#32 else 0#32) :=
    ((frameD 23).trans ((frameN 23 (by decide) (by decide) (by decide)).trans
      ((frameG 23 (by decide)).trans ((frameC 23 (by decide)).trans teB)))).trans (HeadHeaderCommitMath.te_word f.te)
  refine ⟨d,(((((values.trans names).trans finish).trans guard).trans next).trans branch),?_,HeadHeaderCommitView.append entry fields room,
    metaAfter,finalCount,finalPosition,finalTE,frame,csrD.trans (csrN.trans (csrG.trans (csrC.trans (csrB.trans csrA))))⟩
  by_cases more : le+2<cap
  · simp only [more,ite_true]
    exact HeadFieldsConstants.loop finalConstants (by simpa only [more,decide_true,ite_true] using pcD) finalPosition finalCount finalTE
  · simpa only [more,decide_false,Bool.false_eq_true,ite_false] using pcD
end E5R.Thermostat.HeadHeaderCommit
