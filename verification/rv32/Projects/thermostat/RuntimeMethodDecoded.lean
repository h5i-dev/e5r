import Projects.thermostat.RuntimeReadViews
import Projects.thermostat.MainReadDecoded
import Projects.thermostat.MainReadRouteInput
import Projects.thermostat.MainReadWireReturn
import Projects.thermostat.ReadRoundExact
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.RuntimeMethodDecoded
open MainReadDecoded
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := MainReadRouteInput.B
abbrev sp := MainReadRouteInput.sp
abbrev fp := MainReadRouteInput.fp
abbrev rx := MainReadRouteInput.rx

theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat} {close isHead : Bool}
    (h : RuntimeReadViews.RouteReady c ram input s head amount served close isHead) :
    ∃ d n after, n≤18*(MainRequestSpans.body input head amount).length+312 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ RuntimeReadViews.DecodedReady d after input s served close isHead ∧ d.sameCsr c ∧ ViewFrame.Region ram after sp 3304 ∧ d.get 23=c.get 23 ∧ d.get 26=c.get 26 := by
  obtain ⟨a,n,bound,decoded,post⟩ := Wire.contract_quiet B c ram _ _ _ _ _ _ _ h.wire
  let saved := DecodeSave.memory ram MainReadRouteInput.decodeSp c
  have pa : a.pc=0x800019e8#32 := by
    rw [post.pc,h.ret]
    decide +kernel
  have value : WireSpec.CommandWord (a.get 10) .read := by
    have result := post.result
    rw [WireSpec.read_body_independent] at result
    exact result
  have tag : byteOf (a.get 10) 0=4#8 := value ⟨0,by decide⟩ 4#8 rfl
  have stack : Memory.Block B sp 5232 := by
    have block := Memory.sub_block h.stable.stack (off := 60304) (m := 5232) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60304#32=sp by decide +kernel] using block
  obtain ⟨d,stores,pd,d11,d12,d10,d13,dr,dc⟩ := MainReadWireReturn.contract B a saved (a.get 10) (post.s0.trans h.stable.fp) rfl tag stack pa
  let after := MainReadWireReturn.memory saved (a.get 10)
  have frame (off size : Nat) (bound : off+size≤5232) (apart : off+size≤3968 ∨ 3972≤off) : ViewFrame.Region ram after (sp+BitVec.ofNat 32 off) size := by
    intro i
    dsimp only [after]
    rw [MainReadWireReturn.memory_eq,WireCallerBytes.frame _ _ _ _ (by
      intro j
      change (sp+BitVec.ofNat 32 off)+BitVec.ofNat 32 i.val≠(sp+3968#32)+BitVec.ofNat 32 j.val
      exact FrameOffsets.ne sp off 3968 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := i.isLt;have := j.isLt;rcases apart with h|h <;>omega))]
    dsimp only [saved]
    apply DecodeSave.frame
    intro j
    have ne := FrameOffsets.ne MainReadRouteInput.decodeSp (16+off) 0 i.val j.val (by have := i.isLt;omega) (by have := j.isLt;omega) (by have := j.isLt;omega)
    simpa only [BitVec.ofNat_add,←BitVec.add_assoc,show MainReadRouteInput.decodeSp+16#32=sp by decide +kernel,BitVec.add_zero] using ne
  have keep (r : Reg) (member : r∈[2,8,9,19,20,22,24]) : d.get r=c.get r := by
    have ne : ∀ r : Reg, r∈[2,8,9,19,20,22,24] → r≠11 ∧ r≠12 ∧ r≠10 ∧ r≠13 := by decide +kernel
    obtain ⟨n11,n12,n10,n13⟩ := ne r member
    have first := dr r n11 n12 n10 n13
    have abi : a.get r=c.get r := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact post.sp
      · exact post.s0
      · exact post.s1
      · exact post.frame 19 (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
      · exact post.frame 20 (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
      · exact post.frame 22 (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
      · exact post.frame 24 (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))
    exact first.trans abi
  have csr : d.sameCsr c := dc.trans post.csr
  have liveFuture : ViewFrame.Region ram after fp 96 := by
    simpa only [show sp+3204#32=fp by decide +kernel] using frame 3204 96 (by decide) (Or.inl (by decide))
  have stable : MainTransactionStable.At d after input s := by
    refine ⟨(keep 2 (by decide)).trans h.stable.sp,(keep 8 (by decide)).trans h.stable.fp,
      (keep 19 (by decide)).trans h.stable.uart,(keep 22 (by decide)).trans h.stable.one,h.stable.bound,
      (ViewFrame.word liveFuture 84 (by decide)).trans h.stable.filled,?_,?_,h.stable.invariant,h.stable.stack,?_⟩
    · intro i
      have byte := frame 132 2048 (by decide) (Or.inl (by decide)) ⟨i.val,by have := i.isLt;have := h.stable.bound;omega⟩
      have atByte : after (rx+BitVec.ofNat 32 i.val)=ram (rx+BitVec.ofNat 32 i.val) := by simpa only [show sp+132#32=rx by decide +kernel] using byte
      exact atByte.trans (h.stable.bytes i)
    · apply AppState.preserve ram after s h.stable.app
      simpa only [ViewFrame.Region,show sp+44#32=0x80ffebbc#32 by decide +kernel] using frame 44 25 (by decide) (Or.inl (by decide))
    · exact (congrArg Prod.fst csr).trans h.stable.masked
  have actor : after 0x80fffe68#32=0#8 := by
    have byte := frame 4824 1 (by decide) (Or.inr (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+4824#32=0x80fffe68#32 by decide +kernel] using byte.trans h.actor
  have command : Encoding.CommandAt after 0x80fffb10#32 .read := by
    dsimp only [after]
    rw [MainReadWireReturn.memory_eq]
    exact WireCallerBytes.command saved 0x80fffb06#32 (a.get 10) .read value
  have memory : Memory.Block B 0x80ffeb40#32 5312 := by
    have block := Memory.sub_block stable.stack (off := 60224) (m := 5312) (by decide) (by decide)
    simpa only [show 0x80ff0000#32+60224#32=0x80ffeb40#32 by decide +kernel] using block
  have pre : ReadAcquire.Pre B d after s :=
    ⟨pd,stable.sp,(keep 9 (by decide)).trans h.engine,stable.fp,memory,stable.app.state,actor,command,stable.app.available⟩
  have flag : after 0x80fff878#32=Encoding.boolByte close := by
    have byte := frame 3304 1 (by decide) (Or.inl (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3304#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have cap : ramRead after 0x80fff9fc#32 .w=832#32 := by
    have kept := ViewFrame.word (frame 3692 4 (by decide) (Or.inl (by decide))) 0 (by decide)
    simpa only [BitVec.add_zero,show sp+3692#32=0x80fff9fc#32 by decide +kernel] using kept.trans h.replyCapacity
  have methodAfter : after 0x80fff9f4#32=Encoding.boolByte isHead := by
    have kept := frame 3684 1 (by decide) (Or.inl (by decide)) ⟨0,by decide⟩
    simpa only [BitVec.add_zero,show sp+3684#32=0x80fff9f4#32 by decide +kernel] using kept.trans h.method
  refine ⟨d,n+9,after,by omega,decoded.trans stores,⟨pre,stable,MainServeLayout.preserve (MainServeMemoryFrames.whole liveFuture (by decide)) h.serve,
    flag,(keep 20 (by decide)).trans h.capacity,(keep 24 (by decide)).trans h.payload,cap,methodAfter⟩,csr,?_,?_,?_⟩
  · simpa only [BitVec.add_zero] using frame 0 3304 (by decide) (Or.inl (by decide))
  · exact (dr 23 (by decide) (by decide) (by decide) (by decide)).trans (post.frame 23 (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
  · exact (dr 26 (by decide) (by decide) (by decide) (by decide)).trans (post.frame 26 (Or.inr (Or.inr (Or.inr (Or.inr (by decide))))))
end E5R.Thermostat.RuntimeMethodDecoded
