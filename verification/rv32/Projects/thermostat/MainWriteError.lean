import Projects.thermostat.MainWriteInput
import Projects.thermostat.WriteErrorFrame
import Projects.thermostat.MainWritePost
namespace E5R.Thermostat.MainWriteError
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- Actual main call, authorized raw command processing and kernel refusal,
    exact error JSON Response and real return to the main result dispatcher. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (req rawPtr pathPtr bodyPtr : Word)
    (raw path body : List (BitVec 8)) (entries : List HeaderSpec.Entry) (first : Option (List (BitVec 8)))
    (state : Spec.Snapshot) (cmd : Spec.Command) (err : Spec.Error)
    (hp : c.pc=0x8000195a#32) (h2 : c.get 2=0x80ffeb90#32) (h8 : c.get 8=0x80fff814#32)
    (h18 : c.get 18=1#32) (h22 : c.get 22=1#32) (h24 : c.get 24=0x80fffa2c#32)
    (hm : Memory.Block B 0x80ff0000#32 65536) (happ : AppState.At ram state) (hi : Spec.Inv state)
    (h : MainWriteInput.Ready ram req rawPtr pathPtr bodyPtr raw path body entries first state)
    (hallow : AuthSpec.authorized (HeaderSpec.lookup raw (WireSpec.ascii "authorization") entries) (WireSpec.ascii "dev-key")=true)
    (hdecode : WireSpec.decode path body first=.ok cmd) (hres : Spec.transition true state cmd=.error err) :
    ∃ d n after, n≤212*entries.length+18*body.length+871 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainWritePost.At c d ram after (Spec.commit state (.error err)) (ReplyJson.errorBody err) (ErrorLiterals.status err).toNat := by
  obtain ⟨a,ta,a1,fa,ka,pre⟩ := MainWriteInput.establishes c ram req rawPtr pathPtr bodyPtr raw path body entries first state hp h2 h24 hm h
  have pre' : WriteInput.Pre B a ram (0x80ffe9f0#32+240#32) 0x80fffa2c#32 0x80fffd38#32 req 0x80ffebbc#32 rawPtr pathPtr bodyPtr
      raw path body entries first true state := by
    rw [show 0x80ffe9f0#32+240#32=0x80ffeae0#32 by decide +kernel];exact pre
  have block (a : Word) (off n : Nat) (hn : 0<n) (he : 0x80ff0000#32+BitVec.ofNat 32 off=a) (hf : off+n≤65536) : Memory.Block B a n := by
    rw [←he];exact Memory.sub_block hm hn hf
  obtain ⟨d,n,after,bn,td,ret,response,bytes,stateAfter,borrow,_,_,_,_,frame⟩ := WriteErrorFrame.contract_inv a ram
    0x80ffe9f0#32 0x80fffa2c#32 0x80fffd38#32 req 0x80ffebbc#32 rawPtr pathPtr bodyPtr 0x80fff4d4#32
    raw path body entries first 832 true state cmd err pre' hallow hdecode hres hi
    (block _ 59888 416 (by decide) (by decide +kernel) (by decide)) (by decide) h.capacity h.pointer (by decide) (by decide)
    (block _ 62676 832 (by decide) (by decide +kernel) (by decide)) (by decide) (by decide)
    (block _ 64824 15 (by decide) (by decide +kernel) (by decide)) (by decide)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have invNext : Spec.Inv (Spec.commit state (.error err)) := by
    simpa only [hres] using Spec.commit_inv true state cmd hi
  have nextApp := MainWritePost.app frame happ _ (by simpa only [show 0x80ffebbc#32+4#32=0x80ffebc0#32 by decide +kernel] using stateAfter) borrow
  refine ⟨d,6+n,after,by omega,ta.det.trans td,?_,?_,?_,?_,?_,ret.csr.trans ka,nextApp,invNext,?_,bytes,
    MainWritePost.metadata frame,MainWritePost.rx frame⟩
  · rw [ret.pc,a1];decide +kernel
  · exact ret.sp.trans ((fa 2 (by decide) (by decide) (by decide)).trans h2)
  · exact ret.x8.trans ((fa 8 (by decide) (by decide) (by decide)).trans h8)
  · exact ret.x18.trans ((fa 18 (by decide) (by decide) (by decide)).trans h18)
  · exact ret.x22.trans ((fa 22 (by decide) (by decide) (by decide)).trans h22)
  · cases err <;> exact response
end E5R.Thermostat.MainWriteError
