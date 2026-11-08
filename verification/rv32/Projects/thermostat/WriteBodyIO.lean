import Projects.thermostat.WriteBody
import Projects.thermostat.RequestIO
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteBody
open E5R E5R.Thermostat

theorem contract_io (B : Board) (c : Core) (ram : Word → BitVec 8) (p f response req eng rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (admin : Bool) (s : Spec.Snapshot) (cmd : Spec.Command)
    (h : WriteInput.Pre B c ram p f response req eng rawPtr pathPtr bodyPtr raw path body entries first admin s)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key") = true)
    (hdecode : WireSpec.decode path body first = .ok cmd) (hi : Spec.Inv s)
    (hq' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b68#32 (WireSpec.ascii "authorization"))
    (hp' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b75#32 (WireSpec.ascii "Bearer "))
    (hk' : ReadBytes.Span B img (WriteStart.memory ram (p+80#32) f c) 0x80005b7c#32 (WireSpec.ascii "dev-key")) :
    ∃ n d r, n ≤ 212*entries.length+18*body.length+667 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      Post c d ram r p f eng s (Spec.transition admin s cmd) ∧ Engine.InvariantAt r eng ∧
      d.get 8 = f ∧ d.get 9 = response ∧ d.get 19 = ramRead ram (f+12#32) .w ∧
      d.get 18 = ramRead ram (f+16#32) .w ∧ d.get 22 = 1#32 ∧
      (∀ err, Spec.transition admin s cmd = .error err → d.get 10 = BitVec.ofNat 32 (Errors.code err).toNat) := by
  let r0 := WriteStart.memory ram (p+80#32) f c
  obtain ⟨a,ta,ha,a8,a9,a19,a18,acsr⟩ := WriteInput.establishes h
  obtain ⟨n,d,r,hn,td,hd,hinv,htop,hready,herr⟩ := RequestTight.contract_io B a r0 p req eng rawPtr pathPtr bodyPtr raw path body entries first admin s cmd
    ha hq' hp' hk' hallow hdecode hi
  have he : a.get 23 = eng := ha.engine
  refine ⟨31+n,d,r,by omega,ta.trans td,?_,by simpa only [he] using hinv,hready.future.trans a8,hready.response.trans a9,
    hready.pointer.trans a19,hready.capacity.trans a18,hready.completion,herr⟩
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
