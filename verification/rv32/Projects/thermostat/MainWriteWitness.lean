import Projects.thermostat.MainWriteInput
import Projects.thermostat.MainWriteSuccess
import Projects.thermostat.MainWriteError
import Projects.thermostat.MainWriteRound
import Projects.thermostat.RequestWitness
import Projects.thermostat.WriteSuccessWitness
import Projects.thermostat.UartWriteWitness
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.MainWriteWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def raw := WireSpec.ascii "POST /mode HTTP/1.1\r\nHost: x\r\nAuthorization: Bearer dev-key\r\nContent-Length: 4\r\n\r\nauto"
def path := WireSpec.ascii "/mode"
def body := WireSpec.ascii "auto"
def entries : List HeaderSpec.Entry := [⟨21,25,27,28⟩,⟨30,43,45,59⟩,⟨61,75,77,78⟩]

def requestByte : Nat → BitVec 8
  | 32 => 21#8
  | 36 => 25#8
  | 40 => 27#8
  | 44 => 28#8
  | 48 => 30#8
  | 52 => 43#8
  | 56 => 45#8
  | 60 => 59#8
  | 64 => 61#8
  | 68 => 75#8
  | 72 => 77#8
  | 76 => 78#8
  | 288 => 3#8
  | 304 => 25#8
  | 305 => 236#8
  | 306 => 255#8
  | 307 => 128#8
  | 308 => 5#8
  | 320 => 102#8
  | 321 => 236#8
  | 322 => 255#8
  | 323 => 128#8
  | 324 => 4#8
  | 328 => 20#8
  | 329 => 236#8
  | 330 => 255#8
  | 331 => 128#8
  | 332 => 86#8
  | _ => 0#8

def futureByte : Nat → BitVec 8
  | 4 => 128#8
  | 5 => 248#8
  | 6 => 255#8
  | 7 => 128#8
  | 8 => 188#8
  | 9 => 235#8
  | 10 => 255#8
  | 11 => 128#8
  | 12 => 212#8
  | 13 => 244#8
  | 14 => 255#8
  | 15 => 128#8
  | 16 => 64#8
  | 17 => 3#8
  | _ => 0#8

def ram (close : Bool) (a : Word) : BitVec 8 :=
  if 0x80fff880≤a.toNat ∧ a.toNat<0x80fff9f4 then requestByte (a.toNat-0x80fff880)
  else if 0x80fffa2c≤a.toNat ∧ a.toNat<0x80fffa55 then futureByte (a.toNat-0x80fffa2c)
  else if 0x80ffebbc≤a.toNat ∧ a.toNat<0x80ffebd5 then RequestWitness.appByte (a.toNat-0x80ffebbc)
  else if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec6a then raw.getD (a.toNat-0x80ffec14) 255#8
  else if a=0x80fff854#32 then 20#8 else if a=0x80fff855#32 then 244#8 else if a=0x80fff856#32 then 255#8
  else if a=0x80fff857#32 then 128#8 else if a=0x80fff858#32 then 0#8 else if a=0x80fff859#32 then 4#8
  else if a=0x80fff85a#32 then 0#8 else if a=0x80fff85b#32 then 0#8
  else if a=0x80fff878#32 then if close then 1#8 else 0#8
  else if a=0x80fff9f4#32 then 2#8
  else if a=0x80fff9fc#32 then 64#8 else if a=0x80fff9fd#32 then 3#8
  else if a=0x80fff9fe#32 then 0#8 else if a=0x80fff9ff#32 then 0#8 else 255#8

def core : Core := ⟨0x8000195a#32,(fun r =>
  if r=2 then 0x80ffeb90#32 else if r=8 then 0x80fff814#32 else if r=18 then 1#32 else if r=22 then 1#32
  else if r=24 then 0x80fffa2c#32 else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem stack : Memory.Block B 0x80ff0000#32 65536 := by
  unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem app (close : Bool) : AppState.At (ram close) Spec.initial := by
  cases close <;> refine ⟨?_,?_,?_,?_,?_⟩
  all_goals first
    | (change ∀ i : Fin 10, ram _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem raw_span (close : Bool) : Bytes.Span B (ram close) 0x80ffec14#32 raw := by
  apply Bytes.of_block
  · unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel)
  · (cases close <;> decide +kernel)
  · have hf : ∀ i : Fin raw.length, (ram close) (0x80ffec14#32+BitVec.ofNat 32 i.val) = raw[i] := by (cases close <;> decide +kernel)
    exact hf

theorem path_span (close : Bool) : Bytes.Span B (ram close) 0x80ffec19#32 path := by
  exact Bytes.subspan (raw_span close) 5 10 (by decide)

theorem body_span (close : Bool) : Bytes.Span B (ram close) 0x80ffec66#32 body := by
  exact Bytes.subspan (raw_span close) 82 86 (by decide)

theorem table (close : Bool) : HeaderInput.Table B (ram close) (0x80fff880#32+32#32) raw.length entries := by
  refine ⟨by decide,?_⟩
  intro i
  have hi : i.val < 3 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
  change HeaderInput.Cell B (ram close) ((0x80fff880#32+32#32)+BitVec.ofNat 32 (16*i.val)) raw.length (entries[i.val])
  rcases hc with he|he|he
  all_goals simp only [entries,he,List.getElem_cons_zero,List.getElem_cons_succ]
  all_goals constructor
  all_goals first
    | (unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel))
    | (unfold HeaderSpec.Bounds;(cases close <;> decide +kernel))
    | (cases close <;> decide +kernel)

theorem header_pre (close : Bool) : Header.Pre B (ram close) 0x80fff880#32 0x80ffec14#32 raw entries := by
  refine ⟨?_,by decide,by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),raw_span close,by decide,by decide,table close⟩
  unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel)

theorem initial_state (close : Bool) : Encoding.SnapshotAt (ram close) (0x80ffebbc#32+4#32) Spec.initial := by
  have hh : ∀ i : Fin 10, (ram close) ((0x80ffebbc#32+4#32)+BitVec.ofNat 32 i.val) = Encoding.snapshotByte Spec.initial i := by (cases close <;> decide +kernel)
  exact hh

theorem layout (close : Bool) : WriteInput.Layout B (ram close) 0x80ffeae0#32 0x80fff880#32 0x80ffebbc#32
    0x80ffec14#32 0x80ffec19#32 0x80ffec66#32 raw path body entries none true Spec.initial := by
  have hm : Memory.Block B 0x80fff880#32 372 := by
    unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel)
  refine ⟨?_,by decide,?_,by decide,?_,initial_state close,by (cases close <;> decide +kernel),
    by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),header_pre close,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel)
  · unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];(cases close <;> decide +kernel)
  · exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 328) hm (by decide) (by decide)),by decide,by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),body_span close⟩
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 312) hm (by decide) (by decide)),by decide,by (cases close <;> decide +kernel),by (cases close <;> decide +kernel),path_span close⟩
  · exact .missing hm (by decide) (by (cases close <;> decide +kernel))
  all_goals exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))


theorem ready (close : Bool) : MainWriteInput.Ready (ram close) 0x80fff880#32 0x80ffec14#32 0x80ffec19#32 0x80ffec66#32
    raw path body entries none Spec.initial := by
  refine ⟨layout close,by cases close <;> decide +kernel,by cases close <;> decide +kernel,
    by cases close <;> decide +kernel,by cases close <;> decide +kernel,by cases close <;> decide +kernel,
    ?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals first
    | exact WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
    | exact WordRegions.before _ _ _ _ (by decide) (by decide)
end E5R.Thermostat.MainWriteWitness
