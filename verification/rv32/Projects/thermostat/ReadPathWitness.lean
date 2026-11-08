import Projects.thermostat.ReadPath
import Projects.thermostat.ReadWitness
import Projects.thermostat.Interrupt
namespace E5R.Thermostat.ReadPathWitness
open E5R E5R.Thermostat

def core : Core := ((ReadWitness.freeCore.set 20 1024#32).set 24 0x80070000#32).set 22 1#32

theorem pre : ReadAcquire.Pre UartPlatform.board core ReadWitness.freeRam Spec.initial := by
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,rfl,?_,?_⟩
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · change ∀ i : Fin 10, ReadWitness.freeRam (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i
    decide +kernel
  · change ∀ i : Fin 4, ∀ b, Encoding.commandByte .read i=some b → ReadWitness.freeRam (0x80fffb10#32+BitVec.ofNat 32 i.val)=b
    decide +kernel
  · decide +kernel

theorem execution : ∃ d n r, n≤4112 ∧ Trace.Closed UartPlatform.board img n ⟨core,ReadWitness.freeRam⟩ ⟨d,r⟩ ∧
    ReadReplyTail.Post core d r 0x80070000#32 Spec.initial ∧ d.pc=0x80001704#32 ∧
    Bytes.Span UartPlatform.board r 0x80070000#32 (ReplyJson.snapshot Spec.initial) ∧
    Encoding.SnapshotAt r 0x80ffebc0#32 Spec.initial ∧ ramRead r 0x80ffebbc#32 .w=0#32 ∧
    Engine.InvariantAt r 0x80ffebbc#32 := by
  obtain ⟨d,n,r,hn,td,hp,hs,hb,hi,_⟩ := ReadPath.contract_inv core ReadWitness.freeRam 0x80070000#32 1024 Spec.initial pre Spec.initial_inv
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    rfl rfl rfl (by decide) (by decide)
    (by unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
  exact ⟨d,n,r,hn,Interrupt.close td rfl,hp,hp.pc,hp.bytes,hs,hb,hi⟩
end E5R.Thermostat.ReadPathWitness
