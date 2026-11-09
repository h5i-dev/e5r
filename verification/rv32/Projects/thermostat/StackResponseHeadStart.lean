import Projects.thermostat.ResponseHeadStart
import Projects.thermostat.StackAccess
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackResponseHeadStart
open E5R E5R.Thermostat ResponseHeadStart
abbrev B := StackBoard.board
structure Post (c d : Core) (before after : Word → BitVec 8) (frame dst ctptr : Word)
    (status body : Nat) (ct : List (BitVec 8)) (close : Bool) : Prop where
  pc : d.pc=0x80003584#32
  csr : d.sameCsr c
  saved : ResponseHeadSaved.At after frame c
  written : Bytes.Span B after dst (ResponseHeadPrefixSpec.bytes status)
  source : ReadBytes.Span B img after ctptr ct
  memoryFrame : ∀ x, (∀ i : Fin 96, x≠frame+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 192, x≠dst+BitVec.ofNat 32 i.val) → after x=before x
  cap : ramRead after (frame+40#32) .w=192#32
  cachedStatus : ramRead after (frame+36#32) .w=BitVec.ofNat 32 status
  cachedBody : ramRead after (frame+28#32) .w=BitVec.ofNat 32 body
  cachedClose : ramRead after (frame+32#32) .w=ResponseHeadBodyMath.boolWord close
  x2 : d.get 2=frame+16#32
  x8 : d.get 8=ResponseHeadSources.connection close
  x9 : d.get 9=ResponseHeadSources.clName status
  x18 : d.get 18=ResponseHeadSources.ctEnd ct
  x19 : d.get 19=ResponseHeadSources.clEnd status
  x20 : d.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length
  x21 : d.get 21=ResponseHeadSources.ctName ct
  x23 : d.get 23=dst
  x24 : d.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length
  x25 : d.get 25=ResponseHeadBodyMath.boolWord (ResponseHeadSpec.hasBody status)
  x26 : d.get 26=BitVec.ofNat 32 ct.length
  x27 : d.get 27=ctptr
  x1 : d.get 1=0x80003ffa#32
  x10 : d.get 10=dst
  x11 : d.get 11=192#32
  x12 : d.get 12=13#32
  x13 : d.get 13=BitVec.ofNat 32 status

theorem contract (c : Core) (ram : Word → BitVec 8) (frame dst ctptr : Word)
    (status body : Nat) (ct : List (BitVec 8)) (close : Bool)
    (hlo : 100≤status) (hhi : status≤599) (hbody : body≤832) (hct : ct.length≤16) (hfield : ResponseHeadSpec.Field ct)
    (hm : Memory.Block B frame 96) (ha : frame.toNat%4=0) (hd : Memory.Block B dst 192)
    (hsep : WordRegions.Disjoint frame 96 dst 192)
    (hsrc : ReadBytes.Span B img ram ctptr ct) (hsstack : WordRegions.Disjoint ctptr ct.length frame 96)
    (hsout : WordRegions.Disjoint ctptr ct.length dst 192)
    (h2 : c.get 2=frame+96#32) (h10 : c.get 10=dst) (h11 : c.get 11=192#32) (h12 : c.get 12=BitVec.ofNat 32 status) (h13 : c.get 13=ctptr) (h14 : c.get 14=BitVec.ofNat 32 ct.length) (h15 : c.get 15=BitVec.ofNat 32 body) (h16 : c.get 16=ResponseHeadBodyMath.boolWord close) (hp : c.pc=0x80003e4e#32) :
    ∃ d n after, n≤227 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ Post c d ram after frame dst ctptr status body ct close := by
  obtain ⟨a,ta,pa,a17,a5,fa,ka⟩ := ResponseHeadGuard.contract B c ram status (by omega) h12 ⟨hlo,hhi⟩ hp
  have a2 : a.get 2=frame+96#32 := (fa 2 (by decide) (by decide)).trans h2
  have a10 : a.get 10=dst := (fa 10 (by decide) (by decide)).trans h10
  have a11 : a.get 11=192#32 := (fa 11 (by decide) (by decide)).trans h11
  have a12 : a.get 12=BitVec.ofNat 32 status := (fa 12 (by decide) (by decide)).trans h12
  have a13 : a.get 13=ctptr := (fa 13 (by decide) (by decide)).trans h13
  have a14 : a.get 14=BitVec.ofNat 32 ct.length := (fa 14 (by decide) (by decide)).trans h14
  have a15 : a.get 15=BitVec.ofNat 32 body := (fa 15 (by decide) (by decide)).trans h15
  have a16 : a.get 16=ResponseHeadBodyMath.boolWord close := (fa 16 (by decide) (by decide)).trans h16
  obtain ⟨b,tb,pb,b2,fb,kb⟩ := ResponseHeadSave.contract B a ram frame a2 hm ha pa
  let saved := ResponseHeadSave.memory ram frame a
  have sourceb : ReadBytes.Span B img saved ctptr ct := ReadFrame.span hsrc (by
    intro i
    exact ResponseHeadSaveData.frame ram frame _ a (hsstack i))
  have savedb : ResponseHeadSaved.At saved frame c := ResponseHeadSaved.core (ResponseHeadSaved.save ram frame a) (by
    intro r hr
    apply fa r
    · exact CopyRegs.ne_low r 17 hr (by decide) (by decide) (by decide) (by decide)
    · exact CopyRegs.ne_low r 5 hr (by decide) (by decide) (by decide) (by decide))
  have b10 : b.get 10=dst := (fb 10 (by decide)).trans a10
  have b11 : b.get 11=192#32 := (fb 11 (by decide)).trans a11
  have b12 : b.get 12=BitVec.ofNat 32 status := (fb 12 (by decide)).trans a12
  have b13 : b.get 13=ctptr := (fb 13 (by decide)).trans a13
  have b14 : b.get 14=BitVec.ofNat 32 ct.length := (fb 14 (by decide)).trans a14
  have b15 : b.get 15=BitVec.ofNat 32 body := (fb 15 (by decide)).trans a15
  have b16 : b.get 16=ResponseHeadBodyMath.boolWord close := (fb 16 (by decide)).trans a16
  obtain ⟨f,nf,bnf,tf,pf,f9,f8,f18,f21,f20,f24,ff,kf⟩ := ResponseHeadField.contract B b saved ctptr ct close hct b13 b14 b16 sourceb hfield pb
  have f2 : f.get 2=frame+16#32 := (ff 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b2
  have f10 : f.get 10=dst := (ff 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b10
  have f11 : f.get 11=192#32 := (ff 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b11
  have f12 : f.get 12=BitVec.ofNat 32 status := (ff 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b12
  have f13 : f.get 13=ctptr := (ff 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b13
  have f14 : f.get 14=BitVec.ofNat 32 ct.length := (ff 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b14
  have f15 : f.get 15=BitVec.ofNat 32 body := (ff 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b15
  have f16 : f.get 16=ResponseHeadBodyMath.boolWord close := (ff 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans b16
  obtain ⟨g,ng,bng,tg,pg,g9,g19,g25,g17,fg,kg⟩ := ResponseHeadBody.contract B f saved status hhi f12 f9 f11 pf
  have g2 : g.get 2=frame+16#32 := (fg 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f2
  have g10 : g.get 10=dst := (fg 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f10
  have g11 : g.get 11=192#32 := (fg 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f11
  have g12 : g.get 12=BitVec.ofNat 32 status := (fg 12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f12
  have g13 : g.get 13=ctptr := (fg 13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f13
  have g14 : g.get 14=BitVec.ofNat 32 ct.length := (fg 14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f14
  have g15 : g.get 15=BitVec.ofNat 32 body := (fg 15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f15
  have g16 : g.get 16=ResponseHeadBodyMath.boolWord close := (fg 16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f16
  have g8 : g.get 8=ResponseHeadSources.connection close := (fg 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f8
  have g18 : g.get 18=ResponseHeadSources.ctEnd ct := (fg 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f18
  have g21 : g.get 21=ResponseHeadSources.ctName ct := (fg 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f21
  have g20 : g.get 20=BitVec.ofNat 32 (ResponseHeadPlan.ctEnd ct).length := (fg 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f20
  have g24 : g.get 24=BitVec.ofNat 32 (ResponseHeadPlan.ctName ct).length := (fg 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans f24
  obtain ⟨d,td,pd,d5,d6,d7,d28,d17,d27,d26,d13,d12,d23,d1,fd,kd⟩ := ResponseHeadPrefix.contract B g saved frame dst ctptr (BitVec.ofNat 32 body) (ResponseHeadBodyMath.boolWord close)
    status ct.length hlo hhi hct g2 g10 g11 g12 g13 g14 g15 g16 g17 hm ha hd pg
  let after := ResponseHeadPrefix.memory saved frame dst ctptr (BitVec.ofNat 32 body) (ResponseHeadBodyMath.boolWord close) status ct.length
  have hbytes : Bytes.Span B after dst (ResponseHeadPrefixSpec.bytes status) := Bytes.of_block B after dst _
    (by rw [ResponseHeadPrefixSpec.length status hlo hhi];simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) hd (by decide : 0<13) (by decide : 0+13≤192))
    (by rw [ResponseHeadPrefixSpec.length status hlo hhi];decide)
    (ResponseHeadPrefixData.written _ _ _ _ _ _ _ _ hlo hhi hsep)
  have frameAll (x : Word) (hs : ∀ i : Fin 96, x≠frame+BitVec.ofNat 32 i.val) (ho : ∀ i : Fin 192, x≠dst+BitVec.ofNat 32 i.val) : after x=ram x :=
    (ResponseHeadPrefixMemory.frame _ _ _ _ _ _ _ _ x hs (fun i => ho ⟨i.val,by have := i.isLt;omega⟩)).trans
      (ResponseHeadSaveData.frame ram frame x a hs)
  have sourceAfter : ReadBytes.Span B img after ctptr ct := ReadFrame.span hsrc (fun i => frameAll _ (hsstack i) (hsout i))
  refine ⟨d,6+14+nf+ng+62,after,by omega,(((ta.trans tb).trans tf).trans tg).trans td,?_,kd.trans (kg.trans (kf.trans (kb.trans ka))),
    ResponseHeadSaved.after_prefix savedb hsep,hbytes,sourceAfter,frameAll,
    ResponseHeadPrefixMemory.cap_word _ _ _ _ _ _ _ _ hsep,ResponseHeadPrefixMemory.status_word _ _ _ _ _ _ _ _ hsep,
    ResponseHeadPrefixMemory.body_word _ _ _ _ _ _ _ _ hsep,ResponseHeadPrefixMemory.close_word _ _ _ _ _ _ _ _ hsep,
    (fd 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g2,
    (fd 8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g8,
    (fd 9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g9,
    (fd 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g18,
    (fd 19 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g19,
    (fd 20 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g20,
    (fd 21 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g21,
    d23,
    (fd 24 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g24,
    (fd 25 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g25,
    d26,
    d27,
    d1,
    (fd 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g10,
    (fd 11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans g11,
    d12,
    d13⟩
  exact pd
end E5R.Thermostat.StackResponseHeadStart
