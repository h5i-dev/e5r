import Projects.thermostat.AuthCheck
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.AuthWitness
open E5R E5R.Thermostat

def header (last : BitVec 8) := WireSpec.ascii "Bearer dev-ke"++[last]
def token (last : BitVec 8) := WireSpec.ascii "dev-ke"++[last]
def ram (last : BitVec 8) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020010 then 124#8
  else if a.toNat = 0x80020011 then 91#8
  else if a.toNat = 0x80020013 then 128#8
  else if a.toNat = 0x80020014 then 7#8
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x80020018 then 0#8
  else (header last).getD (a.toNat-0x80010000) 255#8

def core : Core :=
  ⟨0x80000568#32,(fun r => if r = 2 then 0x80fff800#32 else if r = 20 then 401#32
    else if r = 23 then 0x80020000#32 else if r = 24 then 0x80010000#32
    else if r = 25 then 14#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

theorem pointer : ∀ last : BitVec 8, ramRead (ram last) 0x80020010#32 .w = 0x80005b7c#32 := by decide +kernel
theorem length : ∀ last : BitVec 8, ramRead (ram last) 0x80020014#32 .w = 7#32 := by decide +kernel

theorem bytes (last : BitVec 8) : Bytes.At (ram last) (0x80010000#32+7#32) (token last) := by
  intro i
  have hi : i.val < 7 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 := by omega
  change ram last ((0x80010000#32+7#32)+BitVec.ofNat 32 i.val) = (token last)[i.val]
  rcases hc with h|h|h|h|h|h|h
  all_goals simp [ram,header,token,WireSpec.ascii,h]

theorem span (last : BitVec 8) : ReadBytes.Span UartPlatform.board img (ram last)
    (0x80010000#32+7#32) (token last) := by
  apply ReadBytes.of_ram
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase]
    simp only [token,List.length_append,List.length_cons,List.length_nil]
    decide +kernel
  · simp only [token,List.length_append,List.length_cons,List.length_nil];decide +kernel
  · exact bytes last

theorem compare (last : BitVec 8) :
    ∃ d n, n ≤ 61 ∧ DetSteps UartPlatform.board img n ⟨core,ram last⟩
      ⟨d,AuthCheck.memory (ram last) 0x80fff800#32 (token last) (WireSpec.ascii "dev-key")⟩ ∧
      d.pc = (if last = 121#8 then 0x800005e2#32 else 0x800005a2#32) ∧ d.get 20 = 401#32 := by
  have hm : Memory.Block UartPlatform.board 0x80020000#32 24 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  have hs : Memory.Block UartPlatform.board 0x80fff800#32 25 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  obtain ⟨d,n,hn,ht,hpc,hframe,hcsr⟩ := AuthCheck.contract UartPlatform.board core (ram last)
    0x80020000#32 0x80fff800#32 0x80010000#32 0x80005b7c#32 (token last) (WireSpec.ascii "dev-key")
    rfl (by change 14 < 2^32;decide) (span last) (AuthLiterals.key _) rfl rfl rfl rfl rfl hm (by decide) hs (length last) (pointer last)
  have he : token last = WireSpec.ascii "dev-key" ↔ last = 121#8 := by
    change [100#8,101#8,118#8,45#8,107#8,101#8]++[last] = [100#8,101#8,118#8,45#8,107#8,101#8,121#8] ↔ _
    simp
  exact ⟨d,n,hn,ht,by simpa only [he] using hpc,hframe 20 (by decide)⟩

theorem accepted :
    ∃ d n, n ≤ 61 ∧ DetSteps UartPlatform.board img n ⟨core,ram 121#8⟩
      ⟨d,AuthCheck.memory (ram 121#8) 0x80fff800#32 (token 121#8) (WireSpec.ascii "dev-key")⟩ ∧
      d.pc = 0x800005e2#32 := by
  obtain ⟨d,n,hn,ht,hpc,_⟩ := compare 121#8
  exact ⟨d,n,hn,ht,by simpa only [ite_true] using hpc⟩

theorem rejected_last_byte :
    ∃ d n, n ≤ 61 ∧ DetSteps UartPlatform.board img n ⟨core,ram 120#8⟩
      ⟨d,AuthCheck.memory (ram 120#8) 0x80fff800#32 (token 120#8) (WireSpec.ascii "dev-key")⟩ ∧
      d.pc = 0x800005a2#32 ∧ d.get 20 = 401#32 := by
  obtain ⟨d,n,hn,ht,hpc,hstatus⟩ := compare 120#8
  exact ⟨d,n,hn,ht,by simpa only [show (120#8 = 121#8) = False by decide,ite_false] using hpc,hstatus⟩
end E5R.Thermostat.AuthWitness
