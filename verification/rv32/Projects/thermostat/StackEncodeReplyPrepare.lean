import Projects.thermostat.EncodeReplyPrepareQuiet
import Projects.thermostat.StackAccess
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackEncodeReplyPrepare
open E5R E5R.Thermostat EncodeReplyPrepare
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (p reply dst : Word) (cap : Nat) (s : Spec.Snapshot)
    (hp : c.pc = 0x80001eb8#32) (hsp : c.get 2 = p+320#32)
    (h10 : c.get 10 = reply) (h11 : c.get 11 = dst) (h12 : c.get 12 = BitVec.ofNat 32 cap)
    (hm : Memory.Block StackBoard.board p 320) (ha : p.toNat%4=0)
    (hr : Memory.Block StackBoard.board reply 10) (hs : Encoding.SnapshotAt ram reply s)
    (hrs : WordRegions.Disjoint reply 10 p 320) :
    ∃ d n, n ≤ 52 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,EncodeReplyMemory.memory ram p reply dst cap c s⟩ ∧
      d.pc = 0x80004976#32 ∧ d.get 2 = p+224#32 ∧ d.get 1 = 0x80001f62#32 ∧
      d.get 10 = p+232#32 ∧ d.get 11 = 0x80005c04#32 ∧ d.get 12 = 0x8000574b#32 ∧ d.get 13 = p+252#32 ∧
      Callee.Frame c d ∧ d.sameCsr c := by
  let q := p+224#32
  have hm96 := Memory.sub_block hm (off := 224) (m := 96) (by decide) (by decide)
  have hal := Memory.word_aligned p 56 ha
  have hsnap : Encoding.SnapshotAt (EncodeReplyStart.saved ram q c) reply s := by
    intro i
    unfold EncodeReplyStart.saved
    rw [ramWrite_w_other _ _ _ _ (by
      intro j hj
      have hh := hrs i ⟨224+92+j,by omega⟩
      simpa only [q,BitVec.add_assoc,←BitVec.ofNat_add] using hh)]
    exact hs i
  have hmode := Fields.mode _ reply s hsnap
  have hsp' : c.get 2 = q+96#32 := by
    simpa only [q,BitVec.add_assoc,show (224#32+96#32)=320#32 by decide +kernel] using hsp
  obtain ⟨a,ta,apc,asp,a13,ar,ac⟩ := E5R.Thermostat.EncodeReplyStart.contract_quiet StackBoard.board c ram q reply dst (BitVec.ofNat 32 cap)
    (Fields.modeWord s.mode) hp hsp' h10 h11 h12 hm96 hal hr hmode
  let initial := EncodeReplyStart.memory ram q dst (BitVec.ofNat 32 cap) c
  obtain ⟨b,nb,hnb,tb,bpc,b11,b12,br,bc⟩ := E5R.Thermostat.EncodeMode.contract_quiet StackBoard.board a initial s.mode apc a13
  have bsp : b.get 2 = q := (br 2 (by decide) (by decide)).trans asp
  have b10 : b.get 10 = reply := (br 10 (by decide) (by decide)).trans ((ar 10 (by decide) (by decide)).trans h10)
  obtain ⟨d,td,dpc,d11,d12,d13,_,_,_,_,d10,d1,dr,dc⟩ := E5R.Thermostat.EncodeReplyConstruct.contract_quiet StackBoard.board b initial q reply
    (ModeLiterals.pointer s.mode) (BitVec.ofNat 32 (ReplyJson.mode s.mode).length) bpc bsp b10 b11 b12 hm96 hal
  have dsp : d.get 2 = q := (dr 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans bsp
  refine ⟨d,6+nb+39,by omega,(ta.trans tb).trans td,dpc,dsp,d1,?_,d11,d12,?_,?_,(dc.trans bc).trans ac⟩
  · simpa only [q,BitVec.add_assoc,show (224#32+8#32)=232#32 by decide +kernel] using d10
  · simpa only [q,BitVec.add_assoc,show (224#32+28#32)=252#32 by decide +kernel] using d13
  · intro reg hreg
    have hn (r : Reg) (hr : r.val<18) (h8 : r ≠ 8) (h9 : r ≠ 9) := Callee.ne_low reg r hreg hr h8 h9
    exact (dr reg (hn 11 (by decide) (by decide) (by decide)) (hn 12 (by decide) (by decide) (by decide))
      (hn 13 (by decide) (by decide) (by decide)) (hn 14 (by decide) (by decide) (by decide))
      (hn 15 (by decide) (by decide) (by decide)) (hn 16 (by decide) (by decide) (by decide))
      (hn 17 (by decide) (by decide) (by decide)) (hn 10 (by decide) (by decide) (by decide)) (hn 1 (by decide) (by decide) (by decide))).trans
      ((br reg (hn 11 (by decide) (by decide) (by decide)) (hn 12 (by decide) (by decide) (by decide))).trans
        (ar reg (hn 2 (by decide) (by decide) (by decide)) (hn 13 (by decide) (by decide) (by decide))))

end E5R.Thermostat.StackEncodeReplyPrepare
