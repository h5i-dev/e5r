import Projects.thermostat.CopyTwoExecuteQuiet
import Projects.thermostat.StackCopyData
import Projects.thermostat.StackCopyTwoFinal
import Projects.thermostat.StackCopyTwoSetup
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StackCopyTwoExecute
open E5R E5R.Thermostat CopyTwoExecute
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (sp dst : Word)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst)
    (h11 : c.get 11=0x80005ba6#32) (h12 : c.get 12=33#32)
    (hs : Memory.Block StackBoard.board sp 16) (hsa : sp.toNat%4=0)
    (hd : Memory.Block StackBoard.board dst 33) (ha : dst.toNat%4=0) (hw : dst.toNat+33<2^32) :
    ∃ d, Quiet.Steps StackBoard.board img 137 ⟨c,ram⟩ ⟨d,memory ram sp dst⟩ ∧ FormatCursor.Returned c d ∧ d.get 10=dst := by
  obtain ⟨a,ta,pa,a2,a10,a11,a12,a13,a14,a15,a5,a6,a7,a16,a17,ar,ac⟩ := E5R.Thermostat.StackCopyTwoSetup.contract_quiet c ram sp dst hp hsp h10 h11 h12 ha hs hsa (by omega)
  obtain ⟨b,tb,pb,b6,b14,b17,br,bc⟩ := E5R.Thermostat.UnalignedCopyLoop.contract_quiet StackBoard.board a (CopyInitData.halfRam ram sp)
    (UnalignedCopyData.base true) dst (UnalignedCopyData.initial true) (UnalignedCopyData.shift true) (UnalignedCopyData.comp true) (UnalignedCopyData.nexts true)
    (by decide) pa a6 a7 a13 a14 a16 a17 (StackCopyData.aligned (UnalignedCopyData.source true)) ha
    (by change Memory.Block StackBoard.board dst 32;simpa only [BitVec.add_zero] using Memory.sub_block hd (off := 0) (m := 32) (by decide) (by decide)) (by change dst.toNat+32<2^32;omega)
  have b2 := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a2
  have b5 := (br 5 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a5
  have b11 := (br 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a11
  have b16 := (br 16 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a16
  have keepAB (r : Reg) (hr : CopyRegs.Preserved r) : b.get r=c.get r := by
    exact (br r (CopyRegs.ne_not r 6 hr (by decide)) (CopyRegs.ne_not r 14 hr (by decide)) (CopyRegs.ne_not r 17 hr (by decide)) (CopyRegs.ne_not r 28 hr (by decide)) (CopyRegs.ne_not r 29 hr (by decide))).trans (ar r hr)
  have hfinalalign : (dst+28#32).toNat%4=0 := by rw [WordZero.add_nat dst 28 (by omega)];omega
  obtain ⟨z,tz,pz,zr,zc⟩ := E5R.Thermostat.StackCopyTwoFinal.contract_quiet b (prefixMemory ram sp dst) sp (dst+28#32) pb b2 b5
    (b6.trans ((UnalignedCopyData.end_source true).trans (by decide +kernel))) b11 b14 b16 (b17.trans (by decide +kernel))
    hs (Memory.sub_block hd (off := 28) (m := 4) (by decide) (by decide)) hfinalalign
  have keepZ (r : Reg) (hr : CopyRegs.Preserved r) : z.get r=c.get r := by
    exact (zr r (CopyRegs.ne_not r 5 hr (by decide)) (CopyRegs.ne_not r 6 hr (by decide)) (CopyRegs.ne_not r 7 hr (by decide))
      (CopyRegs.ne_not r 16 hr (by decide)) (CopyRegs.ne_not r 17 hr (by decide)) (CopyRegs.ne_not r 28 hr (by decide))
      (CopyRegs.ne_not r 29 hr (by decide)) (CopyRegs.ne_not r 30 hr (by decide))).trans (keepAB r hr)
  have zrLow (r : Reg) (h : r≠5 ∧ r≠6 ∧ r≠7 ∧ r≠16 ∧ r≠17 ∧ r≠28 ∧ r≠29 ∧ r≠30) := zr r h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2
  have z2 := (zrLow 2 (by decide)).trans b2
  have z10 := (zrLow 10 (by decide)).trans ((br 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a10)
  have z11 := (zrLow 11 (by decide)).trans b11
  have z12 := (zrLow 12 (by decide)).trans ((br 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a12)
  have z13 := (zrLow 13 (by decide)).trans ((br 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a13)
  have z15 := (zrLow 15 (by decide)).trans ((br 15 (by decide) (by decide) (by decide) (by decide) (by decide)).trans a15)
  let rv := ramWrite (CopyTwoFinal.scratch (prefixMemory ram sp dst) sp) (dst+28#32) (UnalignedCopyData.lastPayload true) .w
  obtain ⟨d,td,pd,d2,d10,dr,dc⟩ := E5R.Thermostat.CopyTailDirectRun.contract_quiet StackBoard.board z rv 0x80005ba6#32 (dst+32#32) 33 32 [125#8]
    pz z11 z12 z13 z15 (by decide) (by rw [WordZero.add_nat dst 32 (by omega)];change dst.toNat+32+1<2^32;omega)
    (by have hh := StackCopyData.tail_span true rv;exact hh)
    (by intro i;have hi : i.val=0 := by have := i.isLt;change i.val<1 at this;omega
        simpa only [hi,show BitVec.ofNat 32 0=0#32 from rfl,BitVec.add_zero,show 0x80005ba6#32+32#32=(CopyErrorTailData.pointer true) from by decide +kernel] using (StackAccess.outside (CopyErrorTailData.outside true)))
    (Memory.sub_block hd (off := 32) (m := 1) (by decide) (by decide))
  refine ⟨d,?_,CopyRegs.returned ?_ ?_ (dc.trans (zc.trans (bc.trans ac))) (fun r hr => (dr r hr).trans (keepZ r hr)),d10.trans z10⟩
  · have hlen : (UnalignedCopyData.nexts true).length=7 := by decide
    simpa only [prefixMemory,memory,rv,hlen,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reduceMul] using ((ta.trans tb).trans tz).trans td
  · exact pd.trans (congrArg (fun x : Word => x &&& ~~~1) (keepZ 1 (by decide)))
  · rw [d2,z2,←hsp]

end E5R.Thermostat.StackCopyTwoExecute
