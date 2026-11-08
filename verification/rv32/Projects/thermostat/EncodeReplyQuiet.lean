-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.EncodeReply
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.EncodeReplyEndQuiet
import Projects.thermostat.EncodeReplyPrepareQuiet
import Projects.thermostat.FormatJsonQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.EncodeReply
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p reply dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (hp : c.pc = 0x80001eb8#32) (hsp : c.get 2 = p+320#32)
    (h10 : c.get 10 = reply) (h11 : c.get 11 = dst) (h12 : c.get 12 = BitVec.ofNat 32 cap)
    (hm : Memory.Block UartPlatform.board p 320) (ha : p.toNat%4=0)
    (hr : Memory.Block UartPlatform.board reply 10) (har : reply.toNat%2=0) (hs : Encoding.SnapshotAt ram reply s)
    (hc : cap<2^32) (hd : Memory.Block UartPlatform.board dst cap) (hw : dst.toNat+cap<2^32)
    (hrs : WordRegions.Disjoint reply 10 p 320) (hds : WordRegions.Disjoint dst cap p 320)
    (hrd : WordRegions.Disjoint reply 10 dst cap) (hfit : (ReplyJson.snapshot s).length ≤ cap) :
    ∃ d n r, n ≤ 3893 ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      FormatCursor.Returned c d ∧ d.get 10 = 1#32 ∧ d.get 11 = BitVec.ofNat 32 (ReplyJson.snapshot s).length ∧
      Bytes.Span UartPlatform.board r dst (ReplyJson.snapshot s) ∧ Encoding.SnapshotAt r reply s ∧
      (∀ x, (∀ i : Fin 320, x ≠ p+BitVec.ofNat 32 i.val) →
        (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let mid := EncodeReplyMemory.memory ram p reply dst cap c s
  obtain ⟨a,na,hna,ta,apc,asp,a1,a10,a11,a12,a13,ar,ac⟩ :=
    E5R.Thermostat.EncodeReplyPrepare.contract_quiet c ram p reply dst cap s hp hsp h10 h11 h12 hm ha hr hs hrs
  have hlayout := EncodeReplyMemory.layout ram p reply dst cap c s hm ha hr har hs hc hd hw hrs hds hrd
  obtain ⟨z,nz,r,hnz,tz,hz,z10,hl,hsout,fr⟩ := E5R.Thermostat.FormatJson.contract_quiet a mid p (p+232#32) (p+252#32) dst cap
    (EncodeValues.values reply (p+244#32) s) s apc asp a10 a11 a12 a13 hlayout (EncodeValues.bytes reply (p+244#32) s) hfit
  have zpc : z.pc = 0x80001f62#32 := by rw [hz.pc,a1];decide +kernel
  have zsp : z.get 2 = p+224#32 := hz.sp.trans asp
  have hlen : ramRead r ((p+224#32)+16#32) .w = BitVec.ofNat 32 (ReplyJson.snapshot s).length := by
    simpa only [BitVec.add_assoc,show (224#32+16#32)=240#32 by decide +kernel,
      show (232#32+8#32)=240#32 by decide +kernel] using hl.positionWord
  have hreg : ViewFrame.Region mid r (p+316#32) 4 := by
    intro i
    apply fr
    · simpa only [BitVec.add_zero] using FormatSpace.offsets_disjoint p 316 4 0 224 (by decide) (by decide) (by decide) i
    · exact WordRegions.symm (Subregion.right hds 316 4 (by decide)) i
    · exact FormatSpace.offsets_disjoint p 316 4 232 12 (by decide) (by decide) (by decide) i
  have hret : ramRead r ((p+224#32)+92#32) .w = c.get 1 := by
    have hh := ViewFrame.word hreg 0 (by decide)
    simp only [BitVec.add_zero] at hh
    have he : (p+224#32)+92#32 = p+316#32 := by rw [BitVec.add_assoc];rfl
    rw [←he] at hh
    exact hh.trans (EncodeReplyMemory.return_word ram p reply dst cap c s)
  obtain ⟨d,td,dpc,dsp,d1,d10,d11,dr,dc⟩ := E5R.Thermostat.EncodeReplyEnd.contract_quiet UartPlatform.board z r (p+224#32)
    (BitVec.ofNat 32 (ReplyJson.snapshot s).length) (c.get 1) zpc zsp z10
    (Memory.sub_block hm (off := 224) (m := 96) (by decide) (by decide)) (Memory.word_aligned p 56 ha) hlen hret
  have keep : Callee.Frame c d := by
    intro reg hreg
    have hn (q : Reg) (hq : q.val<18) (h8 : q ≠ 8) (h9 : q ≠ 9) := Callee.ne_low reg q hreg hq h8 h9
    exact (dr reg (hn 1 (by decide) (by decide) (by decide)) (hn 2 (by decide) (by decide) (by decide))
      (hn 10 (by decide) (by decide) (by decide)) (hn 11 (by decide) (by decide) (by decide))).trans
      ((Callee.of_returned hz reg hreg).trans (ar reg hreg))
  have fullframe : ∀ x, (∀ i : Fin 320, x ≠ p+BitVec.ofNat 32 i.val) →
      (∀ i : Fin cap, x ≠ dst+BitVec.ofNat 32 i.val) → r x = ram x := by
    intro x hx ho
    apply Eq.trans (fr x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩) ho (by
      intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨232+i.val,by have := i.isLt;omega⟩))
    exact EncodeReplyMemory.frame ram p reply dst cap c s x hx
  refine ⟨d,na+nz+5,r,by omega,(ta.trans tz).trans td,?_,d10,d11,hsout,?_,fullframe⟩
  · refine ⟨dpc,?_,(dc.trans hz.csr).trans ac,d1,keep 8 (by decide),keep 9 (by decide),
      keep 18 (by decide),keep 19 (by decide),keep 20 (by decide),keep 21 (by decide),keep 22 (by decide),
      keep 23 (by decide),keep 24 (by decide),keep 25 (by decide),keep 26 (by decide),keep 27 (by decide)⟩
    simpa only [BitVec.add_assoc,show (224#32+96#32)=320#32 by decide +kernel,←hsp] using dsp
  · intro i
    exact (fullframe _ (hrs i) (hrd i)).trans (hs i)

end E5R.Thermostat.EncodeReply
