import Projects.thermostat.Header
import Projects.thermostat.AuthLiterals
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HeaderWitness
open E5R E5R.Thermostat

def raw := WireSpec.ascii "AuThOrIzAtIoNBearer dev-keyauthorizationBAD"
def first (empty : Bool) : HeaderSpec.Entry := ⟨0,13,13,if empty then 13 else 27⟩
def second : HeaderSpec.Entry := ⟨27,40,40,43⟩
def entries (empty : Bool) := [first empty,second]
def ram (empty : Bool) (a : Word) : BitVec 8 :=
  if a.toNat = 0x80020024 then 13#8
  else if a.toNat = 0x80020028 then 13#8
  else if a.toNat = 0x8002002c then if empty then 13#8 else 27#8
  else if a.toNat = 0x80020030 then 27#8
  else if a.toNat = 0x80020034 then 40#8
  else if a.toNat = 0x80020038 then 40#8
  else if a.toNat = 0x8002003c then 43#8
  else if a.toNat = 0x80020120 then 2#8
  else if a.toNat = 0x8002014a then 1#8
  else if a.toNat = 0x8002014b then 128#8
  else if a.toNat = 0x8002014c then 43#8
  else if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x80020150 then 0#8
  else raw.getD (a.toNat-0x80010000) 255#8

def core : Core :=
  ⟨0x800026c0#32,(fun r => if r = 1 then 0x80000542#32 else if r = 2 then 0x80fff800#32
    else if r = 10 then 0x80020000#32 else if r = 11 then 0x80005b68#32
    else if r = 12 then 13#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

theorem raw_span (empty : Bool) : Bytes.Span UartPlatform.board (ram empty) 0x80010000#32 raw := by
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · decide +kernel
  · have hf : ∀ e : Bool, ∀ i : Fin raw.length, ram e (0x80010000#32+BitVec.ofNat 32 i.val) = raw[i] := by decide +kernel
    exact hf empty

theorem table (empty : Bool) : HeaderInput.Table UartPlatform.board (ram empty) (0x80020000#32+32#32) raw.length (entries empty) := by
  refine ⟨by change 2 ≤ 16;decide,?_⟩
  intro i
  have hi : i.val < 2 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  change HeaderInput.Cell UartPlatform.board (ram empty) ((0x80020000#32+32#32)+BitVec.ofNat 32 (16*i.val)) raw.length ((entries empty)[i.val])
  cases empty <;> rcases hc with he|he
  all_goals simp only [entries,he,List.getElem_cons_zero,List.getElem_cons_succ]
  all_goals constructor
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (unfold HeaderSpec.Bounds;decide +kernel)
    | decide +kernel

theorem pre (empty : Bool) : Header.Pre UartPlatform.board (ram empty) 0x80020000#32 0x80010000#32 raw (entries empty) := by
  have hm : Memory.Block UartPlatform.board 0x80020000#32 336 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  cases empty <;> exact ⟨hm,by decide,by decide +kernel,by decide +kernel,by decide +kernel,raw_span _,by decide,by decide,table _⟩

theorem first_value (empty : Bool) :
    ∃ d n, n ≤ 437 ∧ DetSteps UartPlatform.board img n ⟨core,ram empty⟩ ⟨d,ram empty⟩ ∧
      d.pc = 0x80000542#32 ∧ d.get 10 = 0x8001000d#32 ∧
      d.get 11 = (if empty then 0#32 else 14#32) ∧ d.get 10 ≠ 0#32 := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Header.contract UartPlatform.board core (ram empty)
    0x80020000#32 0x80010000#32 0x80005b68#32 raw (WireSpec.ascii "authorization") (entries empty)
    (pre empty) (AuthLiterals.header _) rfl rfl rfl rfl rfl
  have hf : HeaderSpec.find raw (WireSpec.ascii "authorization") (entries empty) = some (first empty) := by
    cases empty <;> decide +kernel
  rw [hf] at hresult
  refine ⟨d,n,hn,ht,hpc,?_,?_,hresult.2.2.2⟩
  · exact hresult.1.trans (by rfl)
  · rw [hresult.2.1]
    cases empty <;> decide +kernel

theorem empty_is_some :
    ∃ d n, n ≤ 437 ∧ DetSteps UartPlatform.board img n ⟨core,ram true⟩ ⟨d,ram true⟩ ∧
      d.get 10 = 0x8001000d#32 ∧ d.get 11 = 0#32 ∧ d.get 10 ≠ 0#32 := by
  obtain ⟨d,n,hn,ht,_,hp,hl,hne⟩ := first_value true
  exact ⟨d,n,hn,ht,hp,hl,hne⟩

theorem duplicate_first_wins :
    ∃ d n, n ≤ 437 ∧ DetSteps UartPlatform.board img n ⟨core,ram false⟩ ⟨d,ram false⟩ ∧
      Bytes.Span UartPlatform.board (ram false) (d.get 10) (WireSpec.ascii "Bearer dev-key") := by
  obtain ⟨d,n,hn,ht,hpc,hresult,hframe,hcsr⟩ := Header.bytes_contract UartPlatform.board core (ram false)
    0x80020000#32 0x80010000#32 0x80005b68#32 raw (WireSpec.ascii "authorization") (entries false)
    (pre false) (AuthLiterals.header _) rfl rfl rfl rfl rfl
  have hf : HeaderSpec.lookup raw (WireSpec.ascii "authorization") (entries false) = some (WireSpec.ascii "Bearer dev-key") := by decide +kernel
  rw [hf] at hresult
  exact ⟨d,n,hn,ht,hresult.2.2⟩
end E5R.Thermostat.HeaderWitness
