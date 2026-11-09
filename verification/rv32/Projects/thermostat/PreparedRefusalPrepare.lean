import Projects.thermostat.NormalResponsePrepare
import Projects.thermostat.RuntimePreparedRefusalNext
set_option autoImplicit false
namespace E5R.Thermostat.PreparedRefusalPrepare
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

theorem contract {c ram input s served used close} (status : Nat)
    (h : MainTransactionStable.At c ram input s) (metadata : LoopTransactionMemory.At ram used)
    (serve : MainServeLayout.At ram served) (pc : c.pc=0x80001728#32)
    (hlo : 200≤status) (hhi : status≤599)
    (prepared10 : c.get 10=BitVec.ofNat 32 status) (prepared11 : c.get 11=0#32) (prepared20 : c.get 20=0#32)
    (prepared13 : c.get 13=0#32) (prepared12 : c.get 12=1#32) (prepared9 : c.get 9=0x80fff878#32) (prepared24 : c.get 24=0xfffffffe#32)
    (future : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (two : c.get 18=2#32)
    (replyCapacity : ramRead ram 0x80fff9fc#32 .w=832#32)
    (closeByte : ram 0x80fff878#32=Encoding.boolByte close) (room : close=false → served<100) :
    ∃ d after,Quiet.Steps B img 26 ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after ⟨s,status,[],[]⟩ served used false close (MainMethod.head (ram 0x80fff9f4#32)) := by
  have ready : NormalResponsePrepare.Ready c ram ⟨s,status,[],[]⟩ served used false close (MainMethod.head (ram 0x80fff9f4#32)) :=
    ⟨pc,h.sp,h.fp,h.uart,h.one,two,future,three,h.masked,h.stack,h.app,h.invariant,serve,room,metadata,
      rfl,(by change (0 : Nat)≤832;decide),hlo,hhi,prepared12,prepared11,prepared20,prepared10,prepared13,prepared9,prepared24,
      Bytes.empty B ram _,replyCapacity,(by cases close <;> exact closeByte),rfl⟩
  exact NormalResponsePrepare.prepare ready
end E5R.Thermostat.PreparedRefusalPrepare
