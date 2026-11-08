-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.MainWriteResponse
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.SharedWriteResponseQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.MainWriteExtracted
abbrev B := UartPlatform.board

/-- Common actual renderer after one of the four real write-call return paths. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (state : Spec.Snapshot) (io : Word)
    (payload : List (BitVec 8)) (status : Nat) (close : Bool)
    (hp : c.pc=0x80001710#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h22 : c.get 22=1#32) (hm : Memory.Block B 0x80ff0000#32 65536)
    (happ : AppState.At ram state) (hi : Spec.Inv state) (hbody : payload.length≤832) (hst : status≤599)
    (h12 : c.get 12=0x800056a8#32) (h11 : c.get 11=16#32)
    (h20 : c.get 20=BitVec.ofNat 32 payload.length) (h10 : c.get 10=BitVec.ofNat 32 status)
    (h13 : c.get 13=0#32) (h9 : c.get 9=0x80fff878#32) (h24 : c.get 24=0xfffffffe#32)
    (hb : Bytes.Span B ram 0x80fff4d4#32 payload)
    (hcap : ramRead ram 0x80fff9fc#32 .w=832#32)
    (htx : ramRead ram (0x80fff814#32+64#32) .w=0x80fff414#32)
    (htxc : ramRead ram (0x80fff814#32+68#32) .w=1024#32)
    (hio : ramRead ram (0x80fff814#32+72#32) .w=io)
    (hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8)) :
    ∃ d after, Quiet.Steps B img 23 ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=0x80001772#32 ∧
      d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧ d.get 9=0x80fff878#32 ∧ d.get 24=0xfffffffe#32 ∧ d.sameCsr c ∧
      AppState.At after state ∧ Engine.InvariantAt after 0x80ffebbc#32 ∧
      Bytes.Span B after 0x80fff4d4#32 payload ∧
      SharedResponseView.Descriptor after 0x80fff878#32 0x80fff414#32 io 0x800056a8#32 payload.length status
        (WireSpec.ascii "application/json") close (MainMethod.head (ram 0x80fff9f4#32)) ∧
      ViewFrame.Region ram after 0x80ffec14#32 2048 := by
  have block (a : Word) (off n : Nat) (hn : 0<n) (he : 0x80ff0000#32+BitVec.ofNat 32 off=a) (hf : off+n≤65536) : Memory.Block B a n := by
    rw [←he];exact Memory.sub_block hm hn hf
  have fpblock := block 0x80fff814#32 63508 1332 (by decide) (by decide +kernel) (by decide)
  have fp753 : Memory.Block B 0x80fff814#32 753 := by
    simpa only [BitVec.add_zero] using Memory.sub_block fpblock (off := 0) (m := 753) (by decide) (by decide)
  have hs := block 0x80ffeb90#32 60304 24 (by decide) (by decide +kernel) (by decide)
  have hpayload : payload.length<2^32 := by omega
  have hstatus : (BitVec.ofNat 32 status).toNat<65536 := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : status<2^32)];omega
  let a := c
  have ta : Quiet.Steps B img 0 ⟨c,ram⟩ ⟨a,ram⟩ := .refl _
  have pa : a.pc=0x80001710#32 := hp
  have a12 := h12
  have a11 := h11
  have a20 := h20
  have a10 := h10
  have a13 := h13
  have a9 := h9
  have a24 := h24
  have ka : a.sameCsr c := rfl
  have fa (r : Reg) (_ : r≠12) (_ : r≠11) (_ : r≠20) (_ : r≠10) (_ : r≠6) (_ : r≠9) (_ : r≠24) (_ : r≠13) : a.get r=c.get r := rfl
  have preserved (r : Reg) (hr : r≠12 ∧ r≠11 ∧ r≠20 ∧ r≠10 ∧ r≠6 ∧ r≠9 ∧ r≠24 ∧ r≠13) : a.get r=c.get r :=
    fa r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2
  have a2 := (preserved 2 (by decide)).trans h2
  have a8 := (preserved 8 (by decide)).trans h8
  have a22 := (preserved 22 (by decide)).trans h22
  obtain ⟨d,after,td,pd,kd,stored,fd,fr⟩ := E5R.Thermostat.SharedWriteResponse.contract_quiet B a ram 0x80fff814#32 0x80ffeb90#32 832#32
    (BitVec.ofNat 32 payload.length) (BitVec.ofNat 32 status) 16#32 0x800056a8#32 0#32
    pa a8 a2 a22 a20 a10 a11 a12 a13 fp753 (by decide) hs (by decide) hcap
    (by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hpayload];exact hbody)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  have appframe : ViewFrame.Region ram after 0x80ffebbc#32 25 := by
    intro i
    exact fr _ (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)
  have appAfter := AppState.preserve ram after state happ appframe
  have ioword (off : Nat) (ho : off+4≤532) :
      SharedWriteResponse.ioWord (MainWriteFlags.memory ram 0x80fff814#32) 0x80fff814#32 off=
        ramRead ram (0x80fff814#32+BitVec.ofNat 32 off) .w := by
    exact ViewFrame.word (MainWriteFlags.low ram 0x80fff814#32) off ho
  have closeWord : 0#32 ||| SharedWriteResponse.byteWord (MainWriteFlags.memory ram 0x80fff814#32) 0x80fff814#32 100=ResponseHeadBodyMath.boolWord close := by
    rw [BitVec.zero_or]
    unfold SharedWriteResponse.byteWord
    rw [Memory.load_byte,MainWriteFlags.low ram 0x80fff814#32 ⟨100,by decide⟩,show 0x80fff814#32+BitVec.ofNat 32 (100 : Nat)=0x80fff878#32 by decide +kernel,hclose]
    cases close <;> rfl
  have methodWord : SharedWriteResponse.byteWord (MainWriteFlags.memory ram 0x80fff814#32) 0x80fff814#32 480=
      BitVec.ofNat 32 (ram 0x80fff9f4#32).toNat := by
    unfold SharedWriteResponse.byteWord
    rw [Memory.load_byte,MainWriteFlags.low ram 0x80fff814#32 ⟨480,by decide⟩]
    rfl
  rw [(ioword 64 (by decide)).trans htx,(ioword 68 (by decide)).trans htxc,(ioword 72 (by decide)).trans hio,closeWord,methodWord] at stored
  have desc := SharedResponseView.descriptor payload.length status (WireSpec.ascii "application/json") close
    (MainMethod.head (ram 0x80fff9f4#32)) hst (MainMethod.head_value _) stored
  have keep (r : Reg) (hr : r≠5 ∧ r≠12 ∧ r≠13 ∧ r≠14 ∧ r≠15 ∧ r≠16 ∧ r≠17) : d.get r=a.get r :=
    fd r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2
  refine ⟨d,after,ta.det_quiet.trans td,pd,(keep 2 (by decide)).trans a2,(keep 8 (by decide)).trans a8,?_,
    (keep 24 (by decide)).trans a24,kd.trans ka,appAfter,⟨state,appAfter.state,hi⟩,?_,desc,?_⟩
  · exact (keep 9 (by decide)).trans h9
  · apply ViewFrame.span hb
    intro i
    exact fr _ (WordRegions.before _ _ 832 753 (by decide) (by decide) ⟨i.val,by have := i.isLt;omega⟩)
      (WordRegions.symm (WordRegions.before _ _ 24 832 (by decide) (by decide)) ⟨i.val,by have := i.isLt;omega⟩)
  · intro i
    exact fr _ (WordRegions.before _ _ _ _ (by decide) (by decide) i)
      (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)) i)

end E5R.Thermostat.MainWriteExtracted
