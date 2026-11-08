import Projects.thermostat.WriteInput
import Projects.thermostat.RequestTight
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteBody
open E5R E5R.Thermostat

structure Post (c d : Core) (ram r : Word → BitVec 8) (p f eng : Word)
    (s : Spec.Snapshot) (res : Except Spec.Error Spec.Success) : Prop where
  pc : d.pc = Engine.endPc res
  sp : d.get 2 = p+80#32
  csr : d.sameCsr c
  state : Encoding.SnapshotAt r (eng+4#32) (Spec.commit s res)
  released : ramRead r eng .w = 0#32
  reply : Engine.ReplyAt r p res
  saved : ViewFrame.Region (OuterSave.memory ram (p+80#32) c) r ((p+80#32)+44#32) 52
  frame : ∀ x, (∀ i : Fin 176, x ≠ p+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 41, x ≠ f+BitVec.ofNat 32 i.val) →
    (∀ i : Fin 14, x ≠ eng+BitVec.ofNat 32 i.val) → r x = ram x

/-- Actual fresh write-handler entry to completed transaction boundary. -/
theorem contract_inv (B : Board) (c : Core) (ram : Word → BitVec 8) (p f response req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : WriteInput.Pre B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s)
    (hq' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hp' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hk' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b7c#32 (WireSpec.ascii "dev-key")) :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+667 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Post c d ram r p f eng s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r eng := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,_,_,_,_,acsr⟩ := WriteInput.establishes h
  obtain ⟨n,d,r,hn,td,hd,hinv,htop⟩ := RequestTight.contract_inv B a r0 p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s cmd
    ha hq' hp' hk' hallow hdecode hi
  have he : a.get 23 = eng := ha.engine
  refine ⟨31+n,d,r,by omega,ta.trans td,?_,by simpa only [he] using hinv⟩
  refine ⟨hd.pc,hd.sp.trans ha.sp,hd.csr.trans acsr,by simpa only [he] using hd.state,
    by simpa only [he] using hd.released,hd.reply,?_,?_⟩
  · intro i
    have hi := i.isLt
    have heq : ((p+80#32)+44#32)+BitVec.ofNat 32 i.val = p+BitVec.ofNat 32 (124+i.val) := by
      have hp : (p+80#32)+44#32 = p+124#32 := by rw [BitVec.add_assoc];rfl
      rw [hp,BitVec.add_assoc,←BitVec.ofNat_add]
    have hsame : r (p+BitVec.ofNat 32 (124+i.val)) = r0 (p+BitVec.ofNat 32 (124+i.val)) := by
      by_cases hk : i.val < 4
      · exact htop ⟨i.val,hk⟩
      · apply hd.frame
        · intro j
          have hj := j.isLt
          exact ShellCall.offset_ne p (124+i.val) j.val (by omega) (by omega) (by omega)
        · intro j
          rw [he]
          have hj := j.isLt
          have hh := h.appAvoid.1 ⟨j.val,by omega⟩ ⟨44+i.val,by omega⟩
          have hptr : (p+80#32)+BitVec.ofNat 32 (44+i.val) = p+BitVec.ofNat 32 (124+i.val) := by
            have hp : (p+80#32)+44#32 = p+124#32 := by rw [BitVec.add_assoc];rfl
            rw [BitVec.ofNat_add,←BitVec.add_assoc,hp,BitVec.add_assoc,←BitVec.ofNat_add]
          rw [hptr] at hh
          exact Ne.symm hh
    rw [heq,hsame,←heq]
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using WriteStart.saved_region ram (p+80#32) f c h.futureSeparate ⟨44+i.val,by omega⟩
  · intro x hx hf heng
    rw [hd.frame x (fun i => hx ⟨i.val,by have := i.isLt;omega⟩) (by simpa only [he] using heng)]
    apply WriteStart.frame
    · intro i
      have hi := i.isLt
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using hx ⟨80+i.val,by omega⟩
    · intro i
      exact hf ⟨20+i.val,by have := i.isLt;omega⟩
end E5R.Thermostat.WriteBody
