import Projects.thermostat.Param
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 3000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.ParamWitness
open E5R E5R.Thermostat

def path (last : BitVec 8) := WireSpec.ascii "/relay/429496729"++[last]
def base (last : BitVec 8) (a : Word) : BitVec 8 := (path last).getD (a.toNat-0x80010000) 255#8
def ram (last : BitVec 8) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020132 then 1#8
  else if a.toNat = 0x80020133 then 128#8
  else if a.toNat = 0x80020134 then 17#8
  else if a.toNat = 0x80020150 then 7#8
  else if a.toNat = 0x80020154 then 17#8
  else if a.toNat = 0x80020170 then 1#8
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x80020174 then 0#8
  else base last a

def core : Core :=
  ⟨0x8000278a#32,(fun r => if r = 1 then 0x8000219e#32 else if r = 2 then 0x80fff800#32
    else if r = 10 then 0x80020000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩


theorem read_count : ∀ last : BitVec 8, ramRead (ram last) 0x80020170#32 .w = 1#32 := by decide +kernel

theorem read_pointer : ∀ last : BitVec 8, ramRead (ram last) 0x80020130#32 .w = 0x80010000#32 := by decide +kernel

theorem read_length : ∀ last : BitVec 8, ramRead (ram last) 0x80020134#32 .w = 17#32 := by decide +kernel

theorem read_start : ∀ last : BitVec 8, ramRead (ram last) 0x80020150#32 .w = 7#32 := by decide +kernel

theorem read_finish : ∀ last : BitVec 8, ramRead (ram last) 0x80020154#32 .w = 17#32 := by decide +kernel

theorem source_bytes (last : BitVec 8) : Bytes.At (ram last) 0x80010000#32 (path last) := by
  intro i
  have hi : i.val < 17 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 ∨
      i.val = 8 ∨ i.val = 9 ∨ i.val = 10 ∨ i.val = 11 ∨ i.val = 12 ∨ i.val = 13 ∨ i.val = 14 ∨ i.val = 15 ∨ i.val = 16 := by omega
  change ram last (0x80010000#32+BitVec.ofNat 32 i.val) = (path last)[i.val]
  rcases hc with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  all_goals simp [ram,base,path,WireSpec.ascii,h]

theorem capture (last : BitVec 8) :
    ParamInput.Capture UartPlatform.board (ram last) 0x80020000#32 0x80010000#32 (path last) 7 17 1 := by
  refine ⟨?_,by decide,?_,by decide,?_,?_,?_,?_,by decide,?_,?_⟩
  · unfold Memory.Block UartPlatform.board
    rw [ThermostatImage.image_rwBase]
    decide +kernel
  · exact read_count last
  · exact read_pointer last
  · exact read_length last
  · exact read_start last
  · exact read_finish last
  · change 17 ≤ 17;omega
  · apply Bytes.of_block
    · unfold Memory.Block UartPlatform.board
      rw [ThermostatImage.image_rwBase]
      change 2147507992 ≤ (0x80010000#32).toNat ∧ _
      simp only [path,List.length_append,List.length_cons,List.length_nil,WireSpec.ascii,List.length_map]
      decide +kernel
    · change (17 : Nat) < 2^32;decide
    · exact source_bytes last

theorem accepts_max :
    ∃ d n, n ≤ 203 ∧ DetSteps UartPlatform.board img n ⟨core,ram 53#8⟩ ⟨d,ram 53#8⟩ ∧
      d.pc = 0x8000219e#32 ∧ d.get 10 = 1#32 ∧ d.get 11 = 0xffffffff#32 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Param.contract UartPlatform.board core (ram 53#8) 0x80020000#32
    (some (ParamInput.captured (path 53#8) 7 17)) (.present (capture _)) rfl rfl rfl
  have hp : ((some (ParamInput.captured (path 53#8) 7 17)).bind WireSpec.parseU32) = some (0xffffffff#32) := by decide +kernel
  rw [hp] at hresult
  exact ⟨d,n,hn,ht,hpc,hresult.1,hresult.2,hframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

theorem rejects_overflow :
    ∃ d n, n ≤ 203 ∧ DetSteps UartPlatform.board img n ⟨core,ram 54#8⟩ ⟨d,ram 54#8⟩ ∧
      d.pc = 0x8000219e#32 ∧ d.get 10 = 0#32 ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Param.contract UartPlatform.board core (ram 54#8) 0x80020000#32
    (some (ParamInput.captured (path 54#8) 7 17)) (.present (capture _)) rfl rfl rfl
  have hp : ((some (ParamInput.captured (path 54#8) 7 17)).bind WireSpec.parseU32) = none := by decide +kernel
  rw [hp] at hresult
  exact ⟨d,n,hn,ht,hpc,hresult,hframe 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩
end E5R.Thermostat.ParamWitness
