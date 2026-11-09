import Projects.thermostat.MainSend
namespace E5R.Thermostat.LoopMainSend
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
/-- Existing actual sender composition additionally preserves the exact G6
    filled/used/config/count words, receive capacity and initialized routes. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (io ctptr : Word) (status : Nat) (ct payload : List (BitVec 8))
    (close head : Bool) (state : Spec.Snapshot) (hi : Spec.Inv state) (happ : AppState.At ram state)
    (hp : c.pc=0x80001772#32) (h2 : c.get 2=0x80ffeb90#32) (h9 : c.get 9=0x80fff878#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (hbody : payload.length≤832)
    (hlo : 200≤status) (hhi : status≤599) (hct : ct.length≤16) (hf : ResponseHeadSpec.Field ct)
    (hv : SharedResponseView.Descriptor ram 0x80fff878#32 0x80fff414#32 io ctptr payload.length status ct close head)
    (hbytes : Bytes.Span B ram 0x80fff4d4#32 payload) (hcbytes : ReadBytes.Span B img ram ctptr ct)
    (hcstack : WordRegions.Disjoint ctptr ct.length 0x80ffeb00#32 144)
    (hcobject : WordRegions.Disjoint ctptr ct.length 0x80fff878#32 89)
    (hctx : WordRegions.Disjoint ctptr ct.length 0x80fff414#32 1024)
    (hs bs : List UartTxLoop.Slot) (hhs : hs.length=(ResponseHeadSpec.bytes status ct payload.length close).length)
    (hbs : bs.length=(ResponseHeadSpec.body status head payload).length) :
    ∃ d n after, n≤2406+UartWriteAll.time (ResponseHeadSpec.bytes status ct payload.length close) hs+
        UartWriteAll.time (ResponseHeadSpec.body status head payload) bs ∧
      Observed.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ (UartTxLoop.reads hs++UartTxLoop.reads bs)
        (UartTxLoop.events (ResponseHeadSpec.bytes status ct payload.length close)++UartTxLoop.events (ResponseHeadSpec.body status head payload)) ∧
      d.pc=0x80001784#32 ∧ ResponseHeadCallee.Keep c d [] ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      ramRead after 0x80fffd38#32 .w=0xffffffff#32 ∧ ramRead after 0x80fffd3c#32 .w=ResponseHeadBodyMath.boolWord close ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 ∧
      ViewFrame.Region ram after 0x80fff814#32 96 ∧
      ViewFrame.Region ram after 0x80ffeba0#32 4 ∧
      ViewFrame.Region ram after 0x80ffebd8#32 60 := by
  obtain ⟨a,ta,pa,a10,a11,a1,fa,ka⟩ := SendCaller.contract B c ram 0x80ffeb90#32 0x80fff878#32 h2 h9 hp
  have a2 := (fa 2 (by decide) (by decide) (by decide)).trans h2
  have ar : a.get 10=0x80fffd38#32 := by rw [a10];decide +kernel
  have pre := MainSend.input a ram io ctptr status ct payload close head pa a2 ar a11 hm hbody hlo hhi hct hf hv hbytes hcbytes hcstack hcobject hctx
  obtain ⟨d,n,after,hn,td,hr,hresult,hclose,_,_,hframe⟩ := Send.contract a ram 0x80ffeb00#32 0x80fff878#32 0x80fffd38#32 0x80fff414#32
    io ctptr payload.length status ct payload close head pre hs bs hhs hbs
  have appRegion : ViewFrame.Region ram after 0x80ffebbc#32 25 := by
    intro i
    exact hframe _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
  have appAfter := AppState.preserve ram after state happ appRegion
  refine ⟨d,6+n,after,by omega,?_,?_,?_,hr.csr.trans ka,appAfter,⟨state,appAfter.state,hi⟩,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.nil_append] using ta.observed.trans td
  · rw [hr.pc,a1];decide +kernel
  · intro r hreg _
    apply (ResponseHeadCallee.returned hr r hreg).trans
    apply fa r
    all_goals intro he;subst r;simp [ResponseHeadCallee.Registers] at hreg
  · simpa only [BitVec.add_zero] using hresult
  · exact hclose
  · intro i
    exact hframe _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
  · intro i
    exact hframe _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
  · intro i
    exact hframe _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
  · intro i
    exact hframe _ (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.before _ _ _ _ (by decide) (by decide) i)
end E5R.Thermostat.LoopMainSend
