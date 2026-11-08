import Projects.thermostat.ReadResponse
import Projects.thermostat.ReadPathWitness
namespace E5R.Thermostat.ReadResponseWitness
open E5R E5R.Thermostat

def ram (a : Word) : BitVec 8 := if a=0x80fff9fd#32 then 4#8 else ReadWitness.freeRam a

theorem pre : ReadAcquire.Pre UartPlatform.board ReadPathWitness.core ram Spec.initial := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,?_,?_⟩
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · change ∀ i : Fin 10, ram (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i
    decide +kernel
  · change ∀ i : Fin 4, ∀ b, Encoding.commandByte .read i=some b → ram (0x80fffb10#32+BitVec.ofNat 32 i.val)=b
    decide +kernel
  · decide +kernel

theorem execution : ∃ d n r, n≤4138 ∧ Trace.Closed UartPlatform.board img n ⟨ReadPathWitness.core,ram⟩ ⟨d,r⟩ ∧
    d.pc=0x80001772#32 ∧ d.get 2=0x80ffeb90#32 ∧ d.get 8=0x80fff814#32 ∧
    SharedResponsePayload.At r 0x80fff814#32 0x800056a8#32 16#32 (BitVec.ofNat 32 (ReplyJson.snapshot Spec.initial).length) 200#32 0#32 ∧
    Bytes.Span UartPlatform.board r 0x80070000#32 (ReplyJson.snapshot Spec.initial) ∧
    Encoding.SnapshotAt r 0x80ffebc0#32 Spec.initial ∧ ramRead r 0x80ffebbc#32 .w=0#32 ∧ Engine.InvariantAt r 0x80ffebbc#32 := by
  obtain ⟨d,n,r,hn,td,hpc,hsp,hfp,_,hp,hbytes,hs,hb,hi⟩ := ReadResponse.contract_inv ReadPathWitness.core ram 0x80070000#32 1024 Spec.initial pre Spec.initial_inv
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    rfl rfl rfl (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide) (by decide +kernel)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  exact ⟨d,n,r,hn,Interrupt.close td rfl,hpc,hsp,hfp,hp,hbytes,hs,hb,hi⟩
end E5R.Thermostat.ReadResponseWitness
