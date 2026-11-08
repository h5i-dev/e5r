import Projects.thermostat.Observed
set_option maxRecDepth 10000
namespace E5R.Thermostat.ObservedWitness
open E5R E5R.Thermostat

def board : Board := ⟨0x80000000,0x10000,[⟨0x10000000,"uart0",true,true,1⟩]⟩
def core : Core := ⟨0,(fun _ => 0),false,false,3,0,0,0,0,0,false⟩
def oracle (i : Nat) : Word := 0x1ab#32+BitVec.ofNat 32 i

def effect : Eff := .pick fun _ => .load .b 0x10000000#32 false fun v => .done (core.wr 10 v 4#32)

/-- pick consumes index0; the UART read at index1 is masked to a byte. -/
theorem masked_indexed_read :
    ((Observed.interp board [] oracle effect (fun _ => 0) 0 [] []).reads.map
      (fun r => (r.value,r.oracleIndex))) = [(0xac#32,1)] := by decide +kernel

theorem actual_value :
    (match (Observed.interp board [] oracle effect (fun _ => 0) 0 [] []).value with
    | .ok c _ _ => c.get 10 | .fault _ => 0#32) = 0xac#32 := by decide +kernel

/-- Wrong-width and misaligned device accesses retain the old faults. -/
theorem wrong_width :
    (Observed.interp board [] oracle (.load .w 0x10000000#32 false (fun _ => .done core)) (fun _ => 0) 0 [] []).value =
      .fault (.unsupported "device read") := rfl

theorem misaligned :
    (Observed.interp board [] oracle (.load .w 0x10000001#32 false (fun _ => .done core)) (fun _ => 0) 0 [] []).value =
      .fault .misaligned := rfl

theorem faithful : (Observed.interp board [] oracle effect (fun _ => 0) 0 [] []).value =
    E5R.interp board [] oracle effect (fun _ => 0) 0 [] := Observed.erase _ _ _ _ _ _ _ _
end E5R.Thermostat.ObservedWitness
