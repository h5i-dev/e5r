import Projects.thermostat.BearerAuth
import Projects.thermostat.AuthWitness
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.BearerWitness
open E5R E5R.Thermostat

def core : Core :=
  ⟨0x80000542#32,(fun r => if r = 2 then 0x80fff800#32 else if r = 10 then 0x80010000#32
    else if r = 11 then 14#32 else if r = 23 then 0x80020000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

theorem header_bytes (last : BitVec 8) : Bytes.At (AuthWitness.ram last) 0x80010000#32 (AuthWitness.header last) := by
  intro i
  have hi : i.val < 14 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨
      i.val = 7 ∨ i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 := by omega
  change AuthWitness.ram last (0x80010000#32+BitVec.ofNat 32 i.val) = (AuthWitness.header last)[i.val]
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals simp [AuthWitness.ram,AuthWitness.header,WireSpec.ascii,h]

theorem header_span (last : BitVec 8) : Bytes.Span UartPlatform.board (AuthWitness.ram last)
    0x80010000#32 (AuthWitness.header last) := by
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase]
    simp only [AuthWitness.header,List.length_append,List.length_cons,List.length_nil];decide +kernel
  · simp only [AuthWitness.header,List.length_append,List.length_cons,List.length_nil];decide +kernel
  · exact header_bytes last

theorem checked_header (last : BitVec 8) :
    ∃ d n, n ≤ 126 ∧ DetSteps UartPlatform.board img n ⟨core,AuthWitness.ram last⟩
      ⟨d,BearerAuth.memory (AuthWitness.ram last) 0x80fff800#32 (AuthWitness.header last)⟩ ∧
      d.pc = (if last = 121#8 then 0x800005e2#32 else 0x800005a2#32) ∧ d.get 20 = 401#32 := by
  have hm : Memory.Block UartPlatform.board 0x80020000#32 24 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  have hs : Memory.Block UartPlatform.board 0x80fff800#32 25 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  obtain ⟨d,n,hn,ht,hpc,h20,h22,hframe,hcsr⟩ := BearerAuth.contract UartPlatform.board core (AuthWitness.ram last)
    0x80020000#32 0x80fff800#32 0x80010000#32 (AuthWitness.header last) (header_span last) (by decide)
    (AuthLiterals.bearer _) (AuthLiterals.key _) rfl rfl rfl rfl rfl hm (by decide) hs (AuthWitness.length last) (AuthWitness.pointer last)
  have he : AuthWitness.header last = WireSpec.ascii "Bearer "++WireSpec.ascii "dev-key" ↔ last = 121#8 := by
    change WireSpec.ascii "Bearer dev-ke"++[last] = WireSpec.ascii "Bearer dev-ke"++[121#8] ↔ _
    simp
  exact ⟨d,n,hn,ht,by simpa only [he] using hpc,h20⟩

theorem accepted :
    ∃ d n, n ≤ 126 ∧ DetSteps UartPlatform.board img n ⟨core,AuthWitness.ram 121#8⟩
      ⟨d,BearerAuth.memory (AuthWitness.ram 121#8) 0x80fff800#32 (AuthWitness.header 121#8)⟩ ∧
      d.pc = 0x800005e2#32 := by
  obtain ⟨d,n,hn,ht,hpc,_⟩ := checked_header 121#8
  exact ⟨d,n,hn,ht,by simpa only [ite_true] using hpc⟩

theorem rejected_key :
    ∃ d n, n ≤ 126 ∧ DetSteps UartPlatform.board img n ⟨core,AuthWitness.ram 120#8⟩
      ⟨d,BearerAuth.memory (AuthWitness.ram 120#8) 0x80fff800#32 (AuthWitness.header 120#8)⟩ ∧
      d.pc = 0x800005a2#32 ∧ d.get 20 = 401#32 := by
  obtain ⟨d,n,hn,ht,hpc,h20⟩ := checked_header 120#8
  exact ⟨d,n,hn,ht,by simpa only [show (120#8 = 121#8) = False by decide,ite_false] using hpc,h20⟩
end E5R.Thermostat.BearerWitness
