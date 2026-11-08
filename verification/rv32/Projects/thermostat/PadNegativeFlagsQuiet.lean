-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.PadNegativeFlags
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.IntegralCallQuiet
import Projects.thermostat.IntegralDigitsQuiet
import Projects.thermostat.IntegralExitQuiet
import Projects.thermostat.IntegralNegativeFlagsQuiet
import Projects.thermostat.IntegralSaveQuiet
import Projects.thermostat.IntegralSetupQuiet
import Projects.thermostat.IntegralWidthQuiet
import Projects.thermostat.PrefixMinusQuiet
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
open E5R E5R.Thermostat
namespace E5R.Thermostat.PadNegativeFlags
theorem contract_quiet (B : Board) (c : Core) (ram : Word → BitVec 8) (p fmt writer src len dst flags : Word) (cap pos : Nat)
    (hp : c.pc = 0x80004514#32) (hsp : c.get 2 = p+128#32)
    (h10 : c.get 10 = fmt) (h11 : c.get 11 = 0#32) (h13 : c.get 13 = 0#32)
    (h14 : c.get 14 = src) (h15 : c.get 15 = len)
    (hst : Memory.Block B p 128) (hsa : p.toNat%4 = 0)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hw : ramRead ram fmt .w = writer) (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32)
    (hf : ramRead ram (fmt+8#32) .w = flags) (hvalid : PadFlags.Valid flags) (hz : ramRead ram (fmt+12#32) .h = 0#32)
    (hsep : WordRegions.Disjoint fmt 14 p 128) (hrom : B.inRam 0x80005c10#32 4 = false)
    (hd : CharInput.Data B ram p writer dst cap pos) (hfit : pos+1 ≤ cap)
    (hobj : WordRegions.Disjoint writer 12 p 128) (hout : WordRegions.Disjoint dst cap p 128)
    (hromChar : B.inRam 0x80005c14#32 4 = false) :
    ∃ d n r, n ≤ 140 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ IntegralReady.Ready c d writer src len ∧
      ramRead r writer .w = dst ∧ ramRead r (writer+4#32) .w = BitVec.ofNat 32 cap ∧
      ramRead r (writer+8#32) .w = BitVec.ofNat 32 (pos+1) ∧ Bytes.Span B r (dst+BitVec.ofNat 32 pos) [45#8] ∧
      (∀ x, (∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 1, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x ≠ (writer+8#32)+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let sp := p+64#32
  let q := p+32#32
  let r0 := IntegralSave.memory ram sp c
  have hst0 : Memory.Block B sp 64 := Memory.sub_block hst (off := 64) (m := 64) (by decide) (by decide)
  have hsa0 : sp.toNat%4 = 0 := Memory.word_aligned p 16 hsa
  have hsp0 : c.get 2 = sp+64#32 := by simpa only [sp,BitVec.add_assoc,show 64#32+64#32 = 128#32 by decide +kernel] using hsp
  have ho : ViewFrame.Region ram r0 fmt 14 := by
    intro i
    apply IntegralSave.frame
    intro j
    simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using hsep i ⟨64+j.val,by have := j.isLt;omega⟩
  have hw0 : ramRead r0 fmt .w = writer := by
    have hh := ViewFrame.word ho 0 (by decide)
    simp only [BitVec.add_zero] at hh;exact hh.trans hw
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := E5R.Thermostat.IntegralSave.contract_quiet B c ram sp hp hsp0 hst0 hsa0
  obtain ⟨b,tb,bpc,b8,b9,b18,b20,b21,b19,br,bc⟩ := E5R.Thermostat.IntegralSetup.contract_quiet B a r0 sp fmt src len (c.get 12) 0#32
    asp ((ar 10 (by decide)).trans h10) (ar 12 (by decide))
    ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14) ((ar 15 (by decide)).trans h15) apc
  have bsp : b.get 2 = sp := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
  have b11 : b.get 11 = 0#32 := (br 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 11 (by decide)).trans h11)
  obtain ⟨u,tu,upc,u23,u25,u22,u10,ur,uc⟩ := E5R.Thermostat.IntegralNegativeFlags.contract_quiet B b r0 fmt len flags b19 b9 hm ha
    ((ViewFrame.word ho 8 (by decide)).trans hf) hvalid b11 bpc
  have usp : u.get 2 = sp := (ur 2 (by decide) (by decide) (by decide) (by decide)).trans bsp
  have u19 : u.get 19 = fmt := (ur 19 (by decide) (by decide) (by decide) (by decide)).trans b19
  obtain ⟨v,tv,vpc,v21,v27,vr,vc⟩ := E5R.Thermostat.IntegralWidth.contract_quiet B u r0 fmt u19 hm ha
    ((ViewFrame.half ho 12 (by decide)).trans hz) upc
  have vsp : v.get 2 = sp := (vr 2 (by decide) (by decide)).trans usp
  have v19 : v.get 19 = fmt := (vr 19 (by decide) (by decide)).trans u19
  have v22 : v.get 22 = 45#32 := (vr 22 (by decide) (by decide)).trans u22
  have v20 : v.get 20 = 0#32 := (vr 20 (by decide) (by decide)).trans ((ur 20 (by decide) (by decide) (by decide) (by decide)).trans b20)
  have v9 : v.get 9 = len := (vr 9 (by decide) (by decide)).trans ((ur 9 (by decide) (by decide) (by decide) (by decide)).trans b9)
  have v18 : v.get 18 = src := (vr 18 (by decide) (by decide)).trans ((ur 18 (by decide) (by decide) (by decide) (by decide)).trans b18)
  obtain ⟨w,tw,wpc,w23,w19,w10,w11,w12,w13,w14,w1,wr,wc⟩ := E5R.Thermostat.IntegralCall.contract_quiet B v r0 fmt writer 45#32 0#32 0#32
    v19 v22 v21 v20 hm ha hw0 ((ViewFrame.word ho 4 (by decide)).trans hv) vpc
  have wsp : w.get 2 = sp := (wr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans vsp
  have w9 : w.get 9 = len := (wr 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v9
  have w18 : w.get 18 = src := (wr 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans v18
  let rs := PrefixSave.memory r0 q w
  have ho0 : ViewFrame.Region ram r0 writer 12 := by
    intro i
    apply IntegralSave.frame
    intro j
    simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using hobj i ⟨64+j.val,by have := j.isLt;omega⟩
  have ho1 : ViewFrame.Region r0 rs writer 12 := by
    intro i
    apply PrefixSave.frame
    intro j
    simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using hobj i ⟨32+j.val,by have := j.isLt;omega⟩
  have hchar : CharInput.Data B rs p writer dst cap pos := CharInput.preserve (CharInput.preserve hd ho0) ho1
  have hq : Memory.Block B q 32 := Memory.sub_block hst (off := 32) (m := 32) (by decide) (by decide)
  have hqa : q.toNat%4 = 0 := Memory.word_aligned p 8 hsa
  have hqc : WordRegions.Disjoint q 32 p 32 := by
    intro i j
    simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (32+i.val) j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
  have hqo : WordRegions.Disjoint q 32 writer 12 := by
    intro i j
    simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (hobj j ⟨32+i.val,by have := i.isLt;omega⟩)
  have hqd : WordRegions.Disjoint q 32 dst cap := by
    intro i j
    simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (hout j ⟨32+i.val,by have := i.isLt;omega⟩)
  obtain ⟨z,k,r1,hk,tz,zret,z20,zu,z10,zptr,zcap,zpos,zbytes,zframe⟩ := E5R.Thermostat.PrefixMinus.contract_quiet B w r0 q p writer dst cap pos
    wpc (by simpa only [q,sp,BitVec.add_assoc,show 32#32+32#32 = 64#32 by decide +kernel] using wsp) rfl w10 w11 w12 w13 w14 hq hqa hchar hfit hromChar hqc hqo hqd
  have zpc : z.pc = 0x800045ea#32 := by rw [zret.pc,w1];decide +kernel
  have zsp : z.get 2 = sp := zret.sp.trans wsp
  obtain ⟨y,ty,ypc,y6,y10,y11,y12,yr,yc⟩ := E5R.Thermostat.IntegralDigits.contract_quiet B z r1 writer src len
    (zret.x19.trans w19) ((zu 23 (by decide)).trans w23) (zret.x18.trans w18) (zret.x9.trans w9) z10 hrom zpc
  have ysp : y.get 2 = sp := (yr 2 (by decide) (by decide) (by decide) (by decide)).trans zsp
  have hsaved : ViewFrame.Region r0 r1 sp 64 := by
    intro i
    apply zframe
    · intro j
      simpa only [sp,q,BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (64+i.val) (32+j.val) (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
    · intro j
      simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne p (64+i.val) j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;omega)
    · intro j
      have hj := j.isLt
      have hpos : pos+j.val < cap := by omega
      simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (hout ⟨pos+j.val,hpos⟩ ⟨64+i.val,by have := i.isLt;omega⟩)
    · intro j
      simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (hobj ⟨8+j.val,by have := j.isLt;omega⟩ ⟨64+i.val,by have := i.isLt;omega⟩)
  obtain ⟨d,td,hready⟩ := E5R.Thermostat.IntegralExit.contract_quiet B c y ram r1 sp writer src len ypc ysp hsp0 hst0 hsa0
    (((((yc.trans zret.csr).trans wc).trans vc).trans uc).trans bc |>.trans ac) hsaved y6 y10 y11 y12
  refine ⟨d,14+6+6+3+9+k+5+15,r1,by omega,((((((ta.trans tb).trans tu).trans tv).trans tw).trans tz).trans ty).trans td,hready,zptr,zcap,zpos,zbytes,?_⟩
  intro x hx ho hj
  exact (zframe x (by
      intro i
      simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨32+i.val,by have := i.isLt;omega⟩)
      (fun i => hx ⟨i.val,by have := i.isLt;omega⟩) ho hj).trans
    (IntegralSave.frame ram sp c x (by
      intro i
      simpa only [sp,BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨64+i.val,by have := i.isLt;omega⟩))

end E5R.Thermostat.PadNegativeFlags
