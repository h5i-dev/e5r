import Projects.thermostat.PrefixSave
import Projects.thermostat.PrefixSetup
import Projects.thermostat.PrefixMinusBranch
import Projects.thermostat.PrefixCharCall
import Projects.thermostat.PrefixCharReturn
import Projects.thermostat.PrefixEmpty
import Projects.thermostat.PrefixExit
import Projects.thermostat.WriteAsciiChar
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PrefixMinus
open E5R E5R.Thermostat

/-- Default negative decimal emits exactly '-' through the actual vtable call. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp lo obj dst : Word) (cap pos : Nat)
    (hp : c.pc = 0x80004e00#32) (hsp : c.get 2 = sp+32#32) (hlo : lo+32#32 = sp)
    (h10 : c.get 10 = obj) (h11 : c.get 11 = 0x80005c04#32)
    (h12 : c.get 12 = 45#32) (h13 : c.get 13 = 0#32) (h14 : c.get 14 = 0#32)
    (hm : Memory.Block B sp 32) (ha : sp.toNat%4 = 0)
    (hd : CharInput.Data B (PrefixSave.memory ram sp c) lo obj dst cap pos)
    (hfit : pos+1 ≤ cap) (hrom : B.inRam 0x80005c14#32 4 = false)
    (hsc : WordRegions.Disjoint sp 32 lo 32) (hso : WordRegions.Disjoint sp 32 obj 12)
    (hsd : WordRegions.Disjoint sp 32 dst cap) :
    ∃ d n r, n ≤ 82 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ CursorExit.Returned c d ∧
      d.get 20 = c.get 20 ∧ (∀ reg : Reg, 21 ≤ reg.val → d.get reg = c.get reg) ∧ d.get 10 = 0#32 ∧
      ramRead r obj .w = dst ∧ ramRead r (obj+4#32) .w = BitVec.ofNat 32 cap ∧
      ramRead r (obj+8#32) .w = BitVec.ofNat 32 (pos+1) ∧ Bytes.Span B r (dst+BitVec.ofNat 32 pos) [45#8] ∧
      (∀ x, (∀ i : Fin 32, x ≠ sp+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 32, x ≠ lo+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 1, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x ≠ (obj+8#32)+BitVec.ofNat 32 i.val) → r x = ram x) := by
  let rr := PrefixSave.memory ram sp c
  obtain ⟨a,ta,apc,asp,ar,ac⟩ := PrefixSave.contract B c ram sp hp hsp hm ha
  obtain ⟨b,tb,bpc,b8,b9,b18,b19,b11,b20,br,bc⟩ := PrefixSetup.contract B a rr sp obj 0x80005c04#32 0#32 0#32
    asp ((ar 10 (by decide)).trans h10) ((ar 11 (by decide)).trans h11)
    ((ar 13 (by decide)).trans h13) ((ar 14 (by decide)).trans h14) apc
  have b12 : b.get 12 = 45#32 := (br 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans ((ar 12 (by decide)).trans h12)
  have bsp : b.get 2 = sp := (br 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans asp
  obtain ⟨u,tu,upc,ur,uc⟩ := PrefixMinusBranch.contract B b rr b12 b11 bpc
  obtain ⟨v,tv,vpc,v13,v10,v11,v1,vr,vc⟩ := PrefixCharCall.contract B u rr obj 45#32
    ((ur 19).trans b19) ((ur 20).trans b20) ((ur 12).trans b12) hrom upc
  have vsp : v.get 2 = lo+32#32 := by
    rw [hlo];exact (vr 2 (by decide) (by decide) (by decide) (by decide)).trans ((ur 2).trans bsp)
  obtain ⟨z,k,r,hk,tz,hz,zh⟩ := WriteAsciiChar.contract B v rr lo obj dst cap pos 45#8 hd vpc vsp v10 v11 (by decide)
  have zpc : z.pc = 0x80004e28#32 := by rw [hz.returned.pc,v1];decide +kernel
  have z10 : z.get 10 = 0#32 := by simpa only [Cursor.resultWord,List.length_cons,List.length_nil,ite_eq_left hfit] using hz.result
  have zsp : z.get 2 = sp := by rw [hz.returned.sp,vsp,hlo]
  have z18 : z.get 18 = 0#32 := hz.returned.x18.trans
    ((vr 18 (by decide) (by decide) (by decide) (by decide)).trans ((ur 18).trans b18))
  obtain ⟨w,tw,wpc,wr,wc⟩ := PrefixCharReturn.contract B z r z10 zpc
  obtain ⟨y,ty,ypc,y10,yr,yc⟩ := PrefixEmpty.contract B w r ((wr 18).trans z18) wpc
  have ysp : y.get 2 = sp := (yr 2 (by decide)).trans ((wr 2).trans zsp)
  have ys : ViewFrame.Region rr r sp 32 := by
    intro i
    apply hz.frame _ (hsc i)
    · intro j
      have hj : j.val < 1 := by exact j.isLt
      have hpj : pos+j.val < cap := by omega
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hsd i ⟨pos+j.val,hpj⟩
    · intro j
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hso i ⟨8+j.val,by have := j.isLt;omega⟩
  have yu : ∀ reg : Reg, 21 ≤ reg.val → y.get reg = c.get reg := by
    intro reg hr
    have hn (q : Reg) (hq : q.val < 21) : reg ≠ q := by intro he;have hv := congrArg Fin.val he;omega
    exact (yr reg (hn 10 (by decide))).trans ((wr reg).trans ((zh reg (by omega)).trans
      ((vr reg (hn 13 (by decide)) (hn 10 (by decide)) (hn 11 (by decide)) (hn 1 (by decide))).trans ((ur reg).trans
        ((br reg (hn 8 (by decide)) (hn 9 (by decide)) (hn 18 (by decide)) (hn 19 (by decide))
          (hn 11 (by decide)) (hn 20 (by decide))).trans (ar reg (hn 2 (by decide))))))))
  obtain ⟨d,td,hret,d20,du,d10⟩ := PrefixExit.contract B c y ram r sp ypc ysp hsp hm ha
    (((yc.trans wc).trans hz.returned.csr).trans (((vc.trans uc).trans bc).trans ac)) ys yu
  refine ⟨d,7+6+1+4+k+1+2+8,r,by omega,((((((ta.trans tb).trans tu).trans tv).trans tz).trans tw).trans ty).trans td,
    hret,d20,du,d10.trans y10,hz.pointer,hz.capacity,?_,hz.written hfit,?_⟩
  · simpa only [Cursor.nextPosition,List.length_cons,List.length_nil,ite_eq_left hfit] using hz.position
  · intro x hs hc ho hj
    exact (hz.frame x hc ho hj).trans (PrefixSave.frame ram sp c x hs)
end E5R.Thermostat.PrefixMinus
