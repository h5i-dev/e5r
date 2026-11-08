import Projects.thermostat.PadNegativeFlags
import Projects.thermostat.CursorLayoutPreserve
import Projects.thermostat.IntegralReturned
import Projects.thermostat.AppendPost
import Projects.thermostat.BytesCons
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.PadNegativeCursorFlags
open E5R E5R.Thermostat

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p fmt obj src dst flags : Word)
    (cap pos : Nat) (xs : List (BitVec 8))
    (hp : c.pc = 0x80004514#32) (hsp : c.get 2 = p+128#32)
    (h10 : c.get 10 = fmt) (h11 : c.get 11 = 0#32) (h13 : c.get 13 = 0#32)
    (h14 : c.get 14 = src) (h15 : c.get 15 = BitVec.ofNat 32 xs.length)
    (hst : Memory.Block B p 128) (hsa : p.toNat%4 = 0)
    (hm : Memory.Block B fmt 14) (ha : fmt.toNat%4 = 0)
    (hw : ramRead ram fmt .w = obj) (hv : ramRead ram (fmt+4#32) .w = 0x80005c04#32)
    (hf : ramRead ram (fmt+8#32) .w = flags) (hvalid : PadFlags.Valid flags) (hz : ramRead ram (fmt+12#32) .h = 0#32)
    (hsep : WordRegions.Disjoint fmt 14 p 128) (hrom : B.inRam 0x80005c10#32 4 = false)
    (h : CursorInput.Layout B ram (p+96#32) obj src dst cap pos xs)
    (hd : CharInput.Data B ram p obj dst cap pos)
    (ho : WordRegions.Disjoint obj 12 p 128) (hs : WordRegions.Disjoint src xs.length p 128)
    (hout : WordRegions.Disjoint dst cap p 128) (hsrcObj : WordRegions.Disjoint src xs.length obj 12)
    (hfit : pos+1+xs.length ≤ cap) (hromChar : B.inRam 0x80005c14#32 4 = false) :
    ∃ d n r, n ≤ 6*xs.length+181 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      AppendPost.Post B c d ram r p obj dst 128 cap pos (45#8::xs) := by
  have hc := h.capacity
  have hf1 : pos+1 ≤ cap := by omega
  obtain ⟨a,k,r0,hk,ta,hr,aptr,acap,apos,abytes,aframe⟩ := PadNegativeFlags.contract B c ram p fmt obj src (BitVec.ofNat 32 xs.length) dst flags cap pos
    hp hsp h10 h11 h13 h14 h15 hst hsa hm ha hw hv hf hvalid hz hsep hrom hd hf1 ho hout hromChar
  have hsource : ReadBytes.Span B img r0 src xs := ReadFrame.span h.source (by
    intro i
    apply aframe _ (hs i)
    · intro j
      have hj := j.isLt
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using h.sourceOutput i ⟨pos+j.val,by omega⟩
    · intro j
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hsrcObj i ⟨8+j.val,by have := j.isLt;omega⟩)
  have hl : CursorInput.Layout B r0 (p+96#32) obj src dst cap (pos+1) xs :=
    ⟨h.stack,h.stackAligned,h.object,h.objectAligned,h.capacity,hf1,aptr,acap,apos,hsource,h.short,h.output,h.nowrap,
      h.objectStack,h.sourceStack,h.outputStack,h.sourceOutput,h.objectOutput⟩
  have hpre := CursorInput.pre_of_layout hl hr.pc (by
    rw [hr.sp,hsp,BitVec.add_assoc];rfl) hr.writer hr.source hr.length
  obtain ⟨d,j,r,hj,td,hpost,hh⟩ := Cursor.contract_full B a r0 (p+96#32) obj src dst cap (pos+1) xs hpre
  have hsub (x : Word) (hx : ∀ i : Fin 128, x ≠ p+BitVec.ofNat 32 i.val) :
      ∀ i : Fin 32, x ≠ (p+96#32)+BitVec.ofNat 32 i.val := by
    intro i
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hx ⟨96+i.val,by have := i.isLt;omega⟩
  have hminus : r (dst+BitVec.ofNat 32 pos) = 45#8 := by
    have hb := abytes.bytes ⟨0,by decide⟩
    change r0 ((dst+BitVec.ofNat 32 pos)+0#32) = 45#8 at hb
    rw [BitVec.add_zero] at hb
    apply Eq.trans _ hb
    apply hpost.frame
    · intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using hout ⟨pos,by omega⟩ ⟨96+i.val,by have := i.isLt;omega⟩
    · intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Bytes.offset_ne dst pos (pos+1+i.val)
        (by omega) (by have := i.isLt;omega) (by omega)
    · intro i
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using Ne.symm (h.objectOutput ⟨8+i.val,by have := i.isLt;omega⟩ ⟨pos,by omega⟩)
  have hb : Bytes.Span B r (dst+BitVec.ofNat 32 pos) (45#8::xs) :=
    Bytes.cons_of_block h.output hc hfit hminus (hpost.written hfit)
  have hwhole : pos+(45#8::xs).length ≤ cap := by simp only [List.length_cons];omega
  refine ⟨d,k+j,r,by omega,ta.trans td,IntegralReady.returned hr hpost.returned hh,?_,hpost.pointer,hpost.capacity,?_,fun _ => hb,?_,?_⟩
  · simpa only [Cursor.resultWord,ite_eq_left hfit,ite_eq_left hwhole] using hpost.result
  · have he : (pos+1)+xs.length = pos+(45#8::xs).length := by simp only [List.length_cons];omega
    simpa only [Cursor.nextPosition,ite_eq_left hfit,ite_eq_left hwhole,he] using hpost.position
  · intro hn;exact False.elim (hn hwhole)
  · intro x hx hbytes hobj
    have htail : ∀ i : Fin xs.length, x ≠ (dst+BitVec.ofNat 32 (pos+1))+BitVec.ofNat 32 i.val := by
      intro i
      have hn := hbytes ⟨1+i.val,by have := i.isLt;simp only [List.length_cons];omega⟩
      simpa only [BitVec.add_assoc,←BitVec.ofNat_add,Nat.add_assoc] using hn
    have hhead : ∀ i : Fin 1, x ≠ (dst+BitVec.ofNat 32 pos)+BitVec.ofNat 32 i.val := by
      intro i
      exact hbytes ⟨i.val,by have := i.isLt;simp only [List.length_cons];omega⟩
    exact (hpost.frame x (hsub x hx) htail hobj).trans (aframe x hx hhead hobj)
end E5R.Thermostat.PadNegativeCursorFlags
