import Projects.thermostat.WriteSuccessTailQuiet
import Projects.thermostat.StackStaticViews
import Projects.thermostat.StackEncodeReply
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackWriteSuccessTail
open E5R E5R.Thermostat WriteSuccessTail
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p dst out f : Word) (cap : Nat) (s : Spec.Snapshot)
    (hp : c.pc = 0x80000736#32) (hsp : c.get 2 = p+320#32)
    (h8 : c.get 8 = f) (h9 : c.get 9 = out) (h19 : c.get 19 = dst)
    (h18 : c.get 18 = BitVec.ofNat 32 cap) (h22 : c.get 22 = 1#32)
    (hm : Memory.Block StackBoard.board p 416) (ha : p.toNat%4=0)
    (hs : Encoding.SnapshotAt ram (p+344#32) s)
    (hc : cap<2^32) (hd : Memory.Block StackBoard.board dst cap) (hw : dst.toNat+cap<2^32)
    (ho : Memory.Block StackBoard.board out 15) (hoa : out.toNat%4=0) (hf : Memory.Block StackBoard.board f 41)
    (hds : WordRegions.Disjoint dst cap p 416) (hos : WordRegions.Disjoint out 15 p 416) (hfs : WordRegions.Disjoint f 41 p 416)
    (hof : WordRegions.Disjoint out 15 f 41) (hdo : WordRegions.Disjoint dst cap out 15) (hdf : WordRegions.Disjoint dst cap f 41)
    (hfit : (ReplyJson.snapshot s).length ≤ cap) :
    ∃ d n r, n ≤ 3928 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = ramRead ram (c.get 2+92#32) .w &&& ~~~1 ∧ d.get 2 = p+416#32 ∧ d.sameCsr c ∧
      OuterReturn.Restored c d ram ∧
      BodyMemory.At r out 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32 ∧
      Bytes.Span StackBoard.board r dst (ReplyJson.snapshot s) ∧ r (f+36#32)=1#8 ∧ r (f+40#32)=1#8 ∧
      (∀ x, (∀ i : Fin 416, x ≠ p+BitVec.ofNat 32 i.val) → (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 15, x ≠ out+BitVec.ofNat 32 i.val) → (∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) → r x = ram x) := by
  obtain ⟨a,ta,apc,a10,a11,a12,a1,ar,ac⟩ := E5R.Thermostat.WriteSuccessPrepare.contract_quiet StackBoard.board c ram (p+320#32) dst (BitVec.ofNat 32 cap) hsp h19 h18 hp
  have asp : a.get 2 = p+320#32 := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans hsp
  have a10' : a.get 10 = p+344#32 := by simpa only [BitVec.add_assoc,show (320#32+24#32)=344#32 by decide +kernel] using a10
  have h320 : Memory.Block StackBoard.board p 320 := by
    simpa only [BitVec.add_zero] using Memory.sub_block hm (off := 0) (m := 320) (by decide) (by decide)
  have hds320 : WordRegions.Disjoint dst cap p 320 := by simpa only [BitVec.add_zero] using Subregion.right hds 0 320 (by decide)
  obtain ⟨z,k,r,hk,tz,hz,z10,z11,hsout,_,fr⟩ := E5R.Thermostat.StackEncodeReply.contract_quiet a ram p (p+344#32) dst cap s apc asp a10' a11 a12 h320 ha
    (Memory.sub_block hm (off := 344) (m := 10) (by decide) (by decide)) (Memory.half_aligned p 172 (by omega)) hs hc hd hw
    (by simpa only [BitVec.add_zero] using FormatSpace.offsets_disjoint p 344 10 0 320 (by decide) (by decide) (by decide))
    hds320 (WordRegions.symm (Subregion.right hds 344 10 (by decide))) hfit
  have zpc : z.pc = 0x80000744#32 := by rw [hz.pc,a1];decide +kernel
  have zsp : z.get 2 = p+320#32 := hz.sp.trans asp
  have keep (reg : Reg) (hsaved : Callee.Saved reg) : z.get reg = c.get reg := by
    exact (Callee.of_returned hz reg hsaved).trans (ar reg (Callee.ne_low reg 10 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 11 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 12 hsaved (by decide) (by decide) (by decide))
      (Callee.ne_low reg 1 hsaved (by decide) (by decide) (by decide)))
  obtain ⟨b,tb,bpc,b12,b18,b10,b20,br,bc⟩ := E5R.Thermostat.WriteSuccessReturn.contract_quiet StackBoard.board z r _ z10 z11 zpc
  have bsp : b.get 2 = p+320#32 := (br 2 (by decide) (by decide) (by decide) (by decide)).trans zsp
  have b8 : b.get 8 = f := (br 8 (by decide) (by decide) (by decide) (by decide)).trans ((keep 8 (by decide)).trans h8)
  have b9 : b.get 9 = out := (br 9 (by decide) (by decide) (by decide) (by decide)).trans ((keep 9 (by decide)).trans h9)
  have b22 : b.get 22 = 1#32 := (br 22 (by decide) (by decide) (by decide) (by decide)).trans ((keep 22 (by decide)).trans h22)
  obtain ⟨d,td,dpc,dsp,dc,dsaved,dresponse,h36,h40⟩ := E5R.Thermostat.BodyReturn.contract_quiet StackBoard.board b r out f 0x800056a8#32 16#32
    (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32 bpc b8 b9 b10 b12 b18 b20 b22 ho hoa hf
    (by rw [bsp];exact Memory.sub_block hm (off := 320) (m := 96) (by decide) (by decide))
    (by rw [bsp];exact Memory.word_aligned p 80 ha)
    (by rw [bsp];exact WordRegions.symm (Subregion.right hos 320 96 (by decide)))
    (by rw [bsp];exact WordRegions.symm (Subregion.right hfs 320 96 (by decide))) hof
  have saved : ViewFrame.Region ram r (p+320#32) 96 := by
    intro i
    apply fr
    · simpa only [BitVec.add_zero] using FormatSpace.offsets_disjoint p 320 96 0 320 (by decide) (by decide) (by decide) i
    · exact WordRegions.symm (Subregion.right hds 320 96 (by decide)) i
  have words (off : Nat) (hb : off+4≤96) : ramRead r (b.get 2+BitVec.ofNat 32 off) .w = ramRead ram (c.get 2+BitVec.ofNat 32 off) .w := by
    rw [bsp,hsp];exact ViewFrame.word saved off hb
  let final := BodyResponse.memory r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32
  have hbytes : Bytes.Span StackBoard.board final dst (ReplyJson.snapshot s) := by
    apply ViewFrame.span hsout
    intro i
    have hi : i.val < cap := Nat.lt_of_lt_of_le i.isLt hfit
    exact BodyMemory.frame r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32
      (dst+BitVec.ofNat 32 i.val) (hdo ⟨i.val,hi⟩) (hdf ⟨i.val,hi⟩)
  refine ⟨d,5+k+8+22,final,by omega,((ta.trans tz).trans tb).trans td,?_,?_,((dc.trans bc).trans hz.csr).trans ac,?_,dresponse,hbytes,h36,h40,?_⟩
  · rw [dpc,words 92 (by decide)]
  · simpa only [bsp,BitVec.add_assoc,show (320#32+96#32)=416#32 by decide +kernel] using dsp
  · constructor
    · exact dsaved.x1 |>.trans (words 92 (by decide))
    · exact dsaved.x8 |>.trans (words 88 (by decide))
    · exact dsaved.x9 |>.trans (words 84 (by decide))
    · exact dsaved.x18 |>.trans (words 80 (by decide))
    · exact dsaved.x19 |>.trans (words 76 (by decide))
    · exact dsaved.x20 |>.trans (words 72 (by decide))
    · exact dsaved.x21 |>.trans (words 68 (by decide))
    · exact dsaved.x22 |>.trans (words 64 (by decide))
    · exact dsaved.x23 |>.trans (words 60 (by decide))
    · exact dsaved.x24 |>.trans (words 56 (by decide))
    · exact dsaved.x25 |>.trans (words 52 (by decide))
    · exact dsaved.x26 |>.trans (words 48 (by decide))
    · exact dsaved.x27 |>.trans (words 44 (by decide))
  · intro x hx hdst hout hfuture
    exact (BodyMemory.frame r out f 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot s).length) 200#32 x hout hfuture).trans
      (fr x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩) hdst)

end E5R.Thermostat.StackWriteSuccessTail
