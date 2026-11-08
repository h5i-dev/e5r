import Projects.thermostat.ReadReplyPrepare
import Projects.thermostat.ReadReplyReturn
import Projects.thermostat.ReadReplyCompletion
import Projects.thermostat.ReadReplyFlags
import Projects.thermostat.EncodeReply
import Projects.thermostat.WordZero
namespace E5R.Thermostat.ReadReplyTail
open E5R E5R.Thermostat

/-- Actual distinct Read-response path to the shared response-construction
    cutpoint. The original main frame remains allocated; this is not a RET. -/
structure Post (before after : Core) (ram : Word → BitVec 8) (dst : Word) (s : Spec.Snapshot) : Prop where
  pc : after.pc=0x80001704#32
  sp : after.get 2=0x80ffeb90#32
  fp : after.get 8=0x80fff814#32
  status : after.get 10=200#32
  mimeLength : after.get 11=16#32
  mime : after.get 12=0x800056a8#32
  used : after.get 20=BitVec.ofNat 32 (ReplyJson.snapshot s).length
  completion : after.get 22=1#32
  tag : after.get 21=6#32
  nextTag : after.get 18=2#32
  future : after.get 9=0x80fff878#32
  pending : after.get 24=0xfffffffe#32
  extra : after.get 13=0#32
  csr : after.sameCsr before
  bytes : Bytes.Span UartPlatform.board ram dst (ReplyJson.snapshot s)
  done708 : ram (0x80fff814#32+708#32)=1#8
  done748 : ram (0x80fff814#32+748#32)=1#8
  done752 : ram (0x80fff814#32+752#32)=1#8

theorem contract (c : Core) (ram : Word → BitVec 8) (dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (hp : c.pc=0x80001b5e#32) (hsp : c.get 2=0x80ffeb90#32) (hfp : c.get 8=0x80fff814#32)
    (h24 : c.get 24=dst) (h20 : c.get 20=BitVec.ofNat 32 cap) (h22 : c.get 22=1#32)
    (hm : Memory.Block UartPlatform.board 0x80ffea50#32 320)
    (hs : Memory.Block UartPlatform.board 0x80fffd38#32 10) (hstate : Encoding.SnapshotAt ram 0x80fffd38#32 s)
    (hf : Memory.Block UartPlatform.board 0x80fff814#32 753)
    (hc : cap<2^32) (hd : Memory.Block UartPlatform.board dst cap) (hw : dst.toNat+cap<2^32)
    (hds : WordRegions.Disjoint dst cap 0x80ffea50#32 320)
    (hss : WordRegions.Disjoint 0x80fffd38#32 10 dst cap)
    (hdf : WordRegions.Disjoint dst cap 0x80fff814#32 753)
    (hfit : (ReplyJson.snapshot s).length≤cap) :
    ∃ d n r, n≤3918 ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Post c d r dst s ∧
      (∀ x, (∀ i : Fin 320, x≠0x80ffea50#32+BitVec.ofNat 32 i.val) →
        (∀ i : Fin cap, x≠dst+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 753, x≠0x80fff814#32+BitVec.ofNat 32 i.val) → r x=ram x) ∧
      ViewFrame.Region ram r 0x80fff814#32 708 := by
  obtain ⟨a,ta,pa,a10,a11,a12,a1,ar,ac⟩ := ReadReplyPrepare.contract UartPlatform.board c ram 0x80ffeb90#32 dst (BitVec.ofNat 32 cap) hsp h24 h20 hp
  have asp := (ar 2 (by decide) (by decide) (by decide) (by decide)).trans hsp
  obtain ⟨z,k,r,hk,tz,hz,z10,z11,hbytes,_,fr⟩ := EncodeReply.contract a ram 0x80ffea50#32 0x80fffd38#32 dst cap s pa
    asp a10 a11 a12 hm (by decide) hs (by decide) hstate hc hd hw (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))) hds hss hfit
  have zp : z.pc=0x80001b72#32 := by rw [hz.pc,a1];decide +kernel
  have z2 : z.get 2=0x80ffeb90#32 := hz.sp.trans asp
  have z8 : z.get 8=0x80fff814#32 := hz.x8.trans ((ar 8 (by decide) (by decide) (by decide) (by decide)).trans hfp)
  have z22 : z.get 22=1#32 := hz.x22.trans ((ar 22 (by decide) (by decide) (by decide) (by decide)).trans h22)
  obtain ⟨b,tb,pb,b12,b20,b11,b10,br,bc⟩ := ReadReplyReturn.contract UartPlatform.board z r _ z10 z11 zp
  have b2 := (br 2 (by decide) (by decide) (by decide) (by decide)).trans z2
  have b8 := (br 8 (by decide) (by decide) (by decide) (by decide)).trans z8
  have b22 := (br 22 (by decide) (by decide) (by decide) (by decide)).trans z22
  obtain ⟨u,tu,pu,u21,u18,u9,u24,u13,ur,uc⟩ := ReadReplyCompletion.contract UartPlatform.board b r 0x80ffeb90#32 b2 pb
  have u8 := (ur 8 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b8
  have u22 := (ur 22 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b22
  have tf := ReadReplyFlags.contract UartPlatform.board u r 0x80fff814#32 pu u8 u22 hf
  let final := ReadReplyFlags.memory r 0x80fff814#32
  have saved (reg : Reg) (h21 : reg≠21) (h18 : reg≠18) (h9 : reg≠9) (h24 : reg≠24) (h13 : reg≠13) : u.get reg=b.get reg := ur reg h21 h18 h9 h24 h13
  have hb : Bytes.Span UartPlatform.board final dst (ReplyJson.snapshot s) := by
    apply ViewFrame.span hbytes
    intro i
    have hi : i.val<cap := Nat.lt_of_lt_of_le i.isLt hfit
    exact ReadReplyFlags.frame r _ _ (hdf ⟨i.val,hi⟩ ⟨708,by decide⟩) (hdf ⟨i.val,hi⟩ ⟨748,by decide⟩) (hdf ⟨i.val,hi⟩ ⟨752,by decide⟩)
  have ff := ReadReplyFlags.flags r 0x80fff814#32
  refine ⟨u.goto 0x80001704#32,7+k+8+6+4,final,by omega,(((ta.trans tz).trans tb).trans tu).trans tf,?_,?_,?_⟩
  · exact ⟨rfl,(saved 2 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b2,u8,
      (saved 10 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10,
      (saved 11 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b11,
      (saved 12 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b12,
      (saved 20 (by decide) (by decide) (by decide) (by decide) (by decide)).trans b20,u22,u21,u18,u9,u24,u13,
      uc.trans (bc.trans (hz.csr.trans ac)),hb,ff.1,ff.2.1,ff.2.2⟩
  · intro x hstack hout hfuture
    dsimp only [final]
    rw [ReadReplyFlags.frame r _ x (hfuture ⟨708,by decide⟩) (hfuture ⟨748,by decide⟩) (hfuture ⟨752,by decide⟩)]
    exact fr x hstack hout
  · intro i
    have hi := i.isLt
    dsimp only [final]
    rw [ReadReplyFlags.frame r _ _
      (WordZero.offset_ne 0x80fff814#32 i.val 708 (by omega) (by decide) (by omega))
      (WordZero.offset_ne 0x80fff814#32 i.val 748 (by omega) (by decide) (by omega))
      (WordZero.offset_ne 0x80fff814#32 i.val 752 (by omega) (by decide) (by omega))]
    exact fr _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.symm hdf ⟨i.val,by omega⟩)
end E5R.Thermostat.ReadReplyTail
