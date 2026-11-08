-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.I16Display
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.I16AppendExitQuiet
import Projects.thermostat.I16DigitsQuiet
import Projects.thermostat.PadNegativeCursorFlagsQuiet
import Projects.thermostat.PadPositiveCursorFlagsQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.I16Display
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p ptr fmt obj dst : Word)
    (cap pos : Nat) (v : BitVec 16) (h : I16Input.Data B ram p ptr fmt obj dst cap pos v)
    (hp : c.pc = 0x80004e5e#32) (hsp : c.get 2 = p+160#32)
    (h10 : c.get 10 = ptr) (h11 : c.get 11 = fmt) (hfit : pos+(ReplyJson.signed v).length ≤ cap)
    (hstr : B.inRam 0x80005c10#32 4 = false) (hchar : B.inRam 0x80005c14#32 4 = false)
    (hrom : ∀ i : Fin 100, ∀ unit : Bool, B.inRam (DigitTable.address i unit) 1 = false) :
    ∃ d n r, n ≤ 292 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      AppendPost.Post B c d ram r p obj dst 160 cap pos (ReplyJson.signed v) := by
  let off := I16Ready.offset v.toInt.natAbs
  let xs := ReplyJson.decimal v.toInt.natAbs
  let src := (p+144#32)+BitVec.ofNat 32 off
  have hn := ReplyJsonBounds.magnitude v
  have he : off+xs.length = 8 := I16Ready.source_end v.toInt.natAbs hn
  have ho := I16Ready.offset_bounds v.toInt.natAbs
  have hlen : xs.length ≤ 5 := ReplyJsonBounds.decimal_length 5 v.toInt.natAbs (by decide) (by omega)
  obtain ⟨a,k,r0,hk,ta,ha,hbytes,hsaved,hframe⟩ := E5R.Thermostat.I16Digits.contract_quiet B c ram (p+144#32) ptr fmt v hp
    (by simpa only [BitVec.add_assoc,show 144#32+16#32 = 160#32 by decide +kernel] using hsp) h10 h11
    (Memory.sub_block h.arena (off := 144) (m := 16) (by decide) (by decide)) (Memory.word_aligned p 36 h.arenaAligned)
    h.inputRam h.inputAligned h.inputValue (Subregion.right h.inputArena 144 16 (by decide)) hrom
  have hl := I16Input.layout h hframe hbytes
  have hc := CharInput.preserve h.toData (I16Input.object_region h hframe)
  have hf := I16Input.formatter_region h hframe
  have hw : ramRead r0 fmt .w = obj := by
    have hh := ViewFrame.word hf 0 (by decide)
    simp only [BitVec.add_zero] at hh
    exact hh.trans h.writerWord
  have hv := (ViewFrame.word hf 4 (by decide)).trans h.vtableWord
  have hflags := (ViewFrame.word hf 8 (by decide)).trans h.flagsWord
  have hwidth := (ViewFrame.half hf 12 (by decide)).trans h.widthWord
  have a15 : a.get 15 = BitVec.ofNat 32 xs.length := by
    rw [I16Ready.decimal_length v.toInt.natAbs hn]
    exact ha.x15
  have hsrcObj : WordRegions.Disjoint src xs.length obj 12 := by
    intro i j
    obtain ⟨z,hz⟩ := I16Input.source_arena he i
    rw [hz]
    exact Ne.symm (h.objectArena j z)
  have hsrcPad (base size : Nat) (hb : base+size ≤ 144) :
      WordRegions.Disjoint src xs.length (p+BitVec.ofNat 32 base) size := by
    intro i j
    have hi := i.isLt;have hj := j.isLt
    simpa only [src,BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (144+off+i.val) (base+j.val)
      (by omega) (by omega) (by omega)
  by_cases hsign : v.toNat < 32768
  · have hsig : ReplyJson.signed v = xs := SignedMagnitude.signed_positive v hsign
    have hfits : pos+xs.length ≤ cap := by rw [hsig] at hfit;exact hfit
    obtain ⟨z,j,r,hj,tz,hz⟩ := E5R.Thermostat.PadPositiveCursorFlags.contract_quiet B a r0 (p+48#32) fmt obj src dst 0x60000020#32 cap pos xs ha.pc
      (by simpa only [BitVec.add_assoc,show 48#32+96#32 = 144#32 by decide +kernel] using ha.spReg)
      ha.x10 (by simpa only [SignedMagnitude.positive,ite_eq_left hsign] using ha.x11) ha.x13 ha.x14 a15
      (Memory.sub_block h.arena (off := 48) (m := 96) (by decide) (by decide)) (Memory.word_aligned p 12 h.arenaAligned)
      h.formatter h.formatterAligned hw hv hflags PadFlags.default hwidth (Subregion.right h.formatterArena 48 96 (by decide)) hstr
      (by simpa only [src,xs,off,BitVec.add_assoc,show 48#32+64#32 = 112#32 by decide +kernel] using hl)
      (Subregion.right h.objectArena 48 96 (by decide)) (hsrcPad 48 96 (by decide))
    obtain ⟨d,td,hd⟩ := E5R.Thermostat.I16AppendExit.contract_quiet B c a z ram r0 r p ptr fmt obj dst cap pos off (I16Ready.length v.toInt.natAbs) 48 96 v xs
      h ha hz hsp (by decide) hfits hframe hsaved
    refine ⟨d,k+j+4,r,by omega,(ta.trans tz).trans td,?_⟩
    rw [hsig];exact hd
  · have hsig : ReplyJson.signed v = 45#8::xs := SignedMagnitude.signed_negative v hsign
    have hfits : pos+1+xs.length ≤ cap := by
      rw [hsig] at hfit
      simp only [List.length_cons] at hfit
      omega
    obtain ⟨z,j,r,hj,tz,hz⟩ := E5R.Thermostat.PadNegativeCursorFlags.contract_quiet B a r0 (p+16#32) fmt obj src dst 0x60000020#32 cap pos xs ha.pc
      (by simpa only [BitVec.add_assoc,show 16#32+128#32 = 144#32 by decide +kernel] using ha.spReg)
      ha.x10 (by simpa only [SignedMagnitude.positive,ite_eq_right hsign] using ha.x11) ha.x13 ha.x14 a15
      (Memory.sub_block h.arena (off := 16) (m := 128) (by decide) (by decide)) (Memory.word_aligned p 4 h.arenaAligned)
      h.formatter h.formatterAligned hw hv hflags PadFlags.default hwidth (Subregion.right h.formatterArena 16 128 (by decide)) hstr
      (by simpa only [src,xs,off,BitVec.add_assoc,show 16#32+96#32 = 112#32 by decide +kernel] using hl)
      hc (Subregion.right h.objectArena 16 128 (by decide)) (hsrcPad 16 128 (by decide))
      (Subregion.right h.outputArena 16 128 (by decide)) hsrcObj hfits hchar
    obtain ⟨d,td,hd⟩ := E5R.Thermostat.I16AppendExit.contract_quiet B c a z ram r0 r p ptr fmt obj dst cap pos off (I16Ready.length v.toInt.natAbs) 16 128 v (45#8::xs)
      h ha hz hsp (by decide) (by simpa only [hsig] using hfit) hframe hsaved
    refine ⟨d,k+j+4,r,by omega,(ta.trans tz).trans td,?_⟩
    rw [hsig];exact hd

end E5R.Thermostat.I16Display
