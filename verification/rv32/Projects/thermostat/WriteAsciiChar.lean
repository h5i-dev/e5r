import Projects.thermostat.CharInput
import Projects.thermostat.CharGuard
import Projects.thermostat.CharWritten
import Projects.thermostat.CharExit
import Projects.thermostat.Cursor
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteAsciiChar
open E5R E5R.Thermostat

/-- Complete actual ASCII arm of Cursor::write_char. The internally encoded
    source is the real SP8 scratch byte; capacity refusal writes no output. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp obj dst : Word) (cap pos : Nat) (b : BitVec 8)
    (h : CharInput.Data B ram sp obj dst cap pos) (hp : c.pc = 0x80002302#32) (hsp : c.get 2 = sp+32#32)
    (h10 : c.get 10 = obj) (h11 : c.get 11 = BitVec.ofNat 32 b.toNat) (hb : b.toNat < 128) :
    ∃ d n r, n ≤ 53 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧ Cursor.Post B c d ram r sp obj dst cap pos [b] ∧ HighFrame.Frame c d := by
  let r0 := CharSave.memory ram sp c
  let r1 := CharInput.memory ram sp c b
  obtain ⟨a,ta,apc,asp,aframe,acsr⟩ := CharSave.contract B c ram sp hp hsp h.stack h.stackAligned
  have a11 : a.get 11 = BitVec.ofNat 32 b.toNat := (aframe 11 (by decide)).trans h11
  obtain ⟨u,tu,upc,u8,uframe,ucsr⟩ := CharAscii.contract B a r0 sp b apc asp a11 h.stack h.stackAligned hb
  have usp : u.get 2 = sp := (uframe 2 (by decide) (by decide)).trans asp
  have u10 : u.get 10 = obj := (uframe 10 (by decide) (by decide)).trans ((aframe 10 (by decide)).trans h10)
  have hd := CharInput.data_frame h c b
  obtain ⟨v,tv,vpc,v12,v11,v18,vframe,vcsr⟩ := CharGuard.contract B u r1 obj cap pos upc u10 u8 h.object h.objectAligned
    hd.capacityWord hd.positionWord h.capacity h.position
  have vsp : v.get 2 = sp := (vframe 2 (by decide) (by decide) (by decide)).trans usp
  have v10 : v.get 10 = obj := (vframe 10 (by decide) (by decide) (by decide)).trans u10
  have v8 : v.get 8 = 1#32 := (vframe 8 (by decide) (by decide) (by decide)).trans u8
  have vcs : v.sameCsr c := (vcsr.trans ucsr).trans acsr
  have vh : HighFrame.Frame c v := by
    intro reg hr
    have hn (k : Reg) (hk : k.val < 20) : reg ≠ k := HighFrame.ne reg k hr hk
    exact (vframe reg (hn 11 (by decide)) (hn 12 (by decide)) (hn 18 (by decide))).trans
      ((uframe reg (hn 8 (by decide)) (hn 12 (by decide))).trans (aframe reg (hn 2 (by decide))))
  by_cases hf : 1 ≤ cap-pos
  · have hspec : pos+1 ≤ cap := by have := h.position;omega
    have vpc' : v.pc = 0x80002394#32 := by simpa only [ite_eq_left hf] using vpc
    obtain ⟨z,k,hk,tz,zpc,zsp,z8,z18,zcsr,zh⟩ := CharWritten.contract B v r1 sp obj dst cap pos b hd vpc' vsp v10 v8 v12 v11 (CharInput.scratch h c b) hf
    let r2 := CharMemory.memory r1 obj dst pos [b]
    have hsaved : ViewFrame.Region r0 r2 (sp+12#32) 20 := by
      intro i
      have hi := i.isLt
      have hh := CharMemory.stack (b := b) hd hf ⟨12+i.val,by omega⟩
      have he : r2 ((sp+12#32)+BitVec.ofNat 32 i.val) = r1 ((sp+12#32)+BitVec.ofNat 32 i.val) := by
        simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hh
      exact he.trans (CharInput.saved ram sp c b i)
    obtain ⟨d,td,hret,d10,dhigh⟩ := CharExit.contract B c z ram r2 sp (cap-pos) zpc zsp hsp (z18.trans v18) z8
      (by have := h.capacity;omega) h.stack h.stackAligned (zcsr.trans vcs) hsaved (HighFrame.trans vh zh)
    refine ⟨d,6+6+4+k+8,r2,by omega,(((ta.trans tu).trans tv).trans tz).trans td,?_,dhigh⟩
    refine ⟨hret,?_,CharMemory.pointer (b := b) hd hf,CharMemory.capacity (b := b) hd hf,?_,?_,?_,?_⟩
    · simpa only [List.length_cons,List.length_nil,CharFinish.flagWord,ite_eq_left hf,Cursor.resultWord,ite_eq_left hspec] using d10
    · simpa only [List.length_cons,List.length_nil,Cursor.nextPosition,ite_eq_left hspec] using CharMemory.position r1 obj dst pos b
    · intro _;exact CharMemory.copied (b := b) hd hf
    · intro hn;exact False.elim (hn hspec)
    · intro x hst hout hobj
      exact (CharMemory.frame r1 obj dst x pos [b] hout hobj).trans (CharInput.frame ram sp c b x hst)
  · have hspec : ¬pos+1 ≤ cap := by have := h.position;omega
    have vpc' : v.pc = 0x800023b8#32 := by simpa only [ite_eq_right hf] using vpc
    obtain ⟨d,td,hret,d10,dhigh⟩ := CharExit.contract B c v ram r1 sp (cap-pos) vpc' vsp hsp v18 v8
      (by have := h.capacity;omega) h.stack h.stackAligned vcs (CharInput.saved ram sp c b) vh
    refine ⟨d,24,r1,by decide,((ta.trans tu).trans tv).trans td,?_,dhigh⟩
    refine ⟨hret,?_,hd.pointerWord,hd.capacityWord,?_,?_,?_,?_⟩
    · simpa only [List.length_cons,List.length_nil,CharFinish.flagWord,ite_eq_right hf,Cursor.resultWord,ite_eq_right hspec] using d10
    · simpa only [List.length_cons,List.length_nil,Cursor.nextPosition,ite_eq_right hspec] using hd.positionWord
    · intro hn;exact False.elim (hspec hn)
    · intro _ x hx;exact CharInput.frame ram sp c b x hx
    · intro x hx _ _;exact CharInput.frame ram sp c b x hx
end E5R.Thermostat.WriteAsciiChar
