import Projects.thermostat.Wire
import Projects.thermostat.UartPlatform
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WireWitness
open E5R E5R.Thermostat

def body (last : BitVec 8) : List (BitVec 8) := [97#8,117#8,116#8,last]
def path : List (BitVec 8) := WireSpec.ascii "/mode"
def ram (last : BitVec 8) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020132 then 1#8
  else if a.toNat = 0x80020133 then 128#8
  else if a.toNat = 0x80020134 then 5#8
  else if a.toNat = 0x80020141 then 16#8
  else if a.toNat = 0x80020142 then 1#8
  else if a.toNat = 0x80020143 then 128#8
  else if a.toNat = 0x80020144 then 4#8
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x80020174 then 0#8
  else if 0x80010000 ≤ a.toNat ∧ a.toNat < 0x80010005 then path.getD (a.toNat-0x80010000) 255#8
  else (body last).getD (a.toNat-0x80011000) 255#8

def core : Core :=
  ⟨0x80001f6e#32,(fun r => if r = 1 then 0x80000600#32 else if r = 2 then 0x80fff810#32
    else if r = 8 then 0xdeadbeef#32 else if r = 9 then 0xcafebabe#32
    else if r = 10 then 0x80020000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

theorem path_pointer : ∀ last : BitVec 8, ramRead (ram last) 0x80020130#32 .w = 0x80010000#32 := by decide +kernel
theorem path_length : ∀ last : BitVec 8, ramRead (ram last) 0x80020134#32 .w = 5#32 := by decide +kernel
theorem body_pointer : ∀ last : BitVec 8, ramRead (ram last) 0x80020140#32 .w = 0x80011000#32 := by decide +kernel
theorem body_length : ∀ last : BitVec 8, ramRead (ram last) 0x80020144#32 .w = 4#32 := by decide +kernel
theorem count : ∀ last : BitVec 8, ramRead (ram last) 0x80020170#32 .w = 0#32 := by decide +kernel

theorem path_bytes (last : BitVec 8) : Bytes.At (ram last) 0x80010000#32 path := by
  intro i
  have hi : i.val < 5 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 := by omega
  change ram last (0x80010000#32+BitVec.ofNat 32 i.val) = path[i.val]
  rcases hc with h|h|h|h|h
  all_goals simp [ram,path,WireSpec.ascii,h]

theorem body_bytes (last : BitVec 8) : Bytes.At (ram last) 0x80011000#32 (body last) := by
  intro i
  have hi : i.val < 4 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  change ram last (0x80011000#32+BitVec.ofNat 32 i.val) = (body last)[i.val]
  rcases hc with h|h|h|h
  all_goals simp [ram,body,h]

theorem pre (last : BitVec 8) :
    Wire.Pre UartPlatform.board core (ram last) 0x80fff800#32 0x80020000#32 0x80010000#32 0x80011000#32 path (body last) none := by
  have hm : Memory.Block UartPlatform.board 0x80020000#32 372 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  have hp : Bytes.Span UartPlatform.board (ram last) 0x80010000#32 path := by
    apply Bytes.of_block
    · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    · decide +kernel
    · exact path_bytes last
  have hb : Bytes.Span UartPlatform.board (ram last) 0x80011000#32 (body last) := by
    apply Bytes.of_block
    · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];simp only [body,List.length_cons,List.length_nil];decide +kernel
    · change 4 < 2^32;decide
    · exact body_bytes last
  refine ⟨rfl,rfl,rfl,?_,by decide,?_,?_,?_,?_,?_,?_⟩
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 328) hm (by decide) (by decide)),by decide,body_pointer last,body_length last,hb⟩
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 312) hm (by decide) (by decide)),by decide,path_pointer last,path_length last,hp⟩
  · exact .missing hm (by decide) (count last)
  · unfold WireInput.Separate;decide +kernel
  · change ∀ i : Fin 4, ∀ j : Fin 16, 0x80011000#32+BitVec.ofNat 32 i.val ≠ 0x80fff800#32+BitVec.ofNat 32 j.val
    decide +kernel
  · decide +kernel

/-- Full real function call on a satisfiable Request preserves nonzero s0/s1. -/
theorem accepts_auto :
    ∃ d n, n ≤ 375 ∧ DetSteps UartPlatform.board img n ⟨core,ram 111#8⟩
      ⟨d,DecodeSave.memory (ram 111#8) 0x80fff800#32 core⟩ ∧ d.pc = 0x80000600#32 ∧
      WireSpec.CommandWord (d.get 10) (.mode .auto) ∧ d.get 8 = 0xdeadbeef#32 ∧ d.get 9 = 0xcafebabe#32 := by
  obtain ⟨d,n,hn,ht,hpost⟩ := Wire.contract UartPlatform.board core (ram 111#8) 0x80fff800#32
    0x80020000#32 0x80010000#32 0x80011000#32 path (body 111#8) none (pre _)
  have hs : WireSpec.decode path (body 111#8) none = .ok (.mode .auto) := by decide +kernel
  refine ⟨d,n,hn,ht,?_,?_,hpost.s0,hpost.s1⟩
  · exact hpost.pc.trans (by decide +kernel)
  · have hv := hpost.result;rw [hs] at hv;exact hv

theorem rejects_bad_auto :
    ∃ d n, n ≤ 375 ∧ DetSteps UartPlatform.board img n ⟨core,ram 112#8⟩
      ⟨d,DecodeSave.memory (ram 112#8) 0x80fff800#32 core⟩ ∧
      WireSpec.ResultWord (d.get 10) (.error 400) ∧ d.get 2 = core.get 2 := by
  obtain ⟨d,n,hn,ht,hpost⟩ := Wire.contract UartPlatform.board core (ram 112#8) 0x80fff800#32
    0x80020000#32 0x80010000#32 0x80011000#32 path (body 112#8) none (pre _)
  have hs : WireSpec.decode path (body 112#8) none = .error 400 := by decide +kernel
  refine ⟨d,n,hn,ht,?_,hpost.sp⟩
  have hv := hpost.result;rw [hs] at hv;exact hv
end E5R.Thermostat.WireWitness
