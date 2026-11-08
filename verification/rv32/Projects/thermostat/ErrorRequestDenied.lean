import Projects.thermostat.RequestBoard
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.ErrorRequestDenied
open E5R E5R.Thermostat

def raw := WireSpec.ascii "POST /mode HTTP/1.1\r\nAuthorization: Bearer dev-key\r\nContent-Length: 4\r\n\r\nauto"
def path := WireSpec.ascii "/mode"
def body := WireSpec.ascii "auto"
def entries : List HeaderSpec.Entry := [⟨21,34,36,50⟩,⟨52,66,68,69⟩]

def requestByte : Nat → BitVec 8
  | 32 => 21#8
  | 36 => 34#8
  | 40 => 36#8
  | 44 => 50#8
  | 48 => 52#8
  | 52 => 66#8
  | 56 => 68#8
  | 60 => 69#8
  | 288 => 2#8
  | 304 => 5#8
  | 306 => 4#8
  | 307 => 128#8
  | 308 => 5#8
  | 320 => 73#8
  | 322 => 4#8
  | 323 => 128#8
  | 324 => 4#8
  | 330 => 4#8
  | 331 => 128#8
  | 332 => 77#8
  | _ => 0#8

def appByte : Nat → BitVec 8
  | 8 => 200#8
  | 10 => 200#8
  | 16 => 124#8
  | 17 => 91#8
  | 19 => 128#8
  | 20 => 7#8
  | _ => 0#8

def ram (a : Word) : BitVec 8 :=
  if 0x80020000 ≤ a.toNat ∧ a.toNat < 0x80020174 then requestByte (a.toNat-0x80020000)
  else if 0x80010000 ≤ a.toNat ∧ a.toNat < 0x80010019 then appByte (a.toNat-0x80010000)
  else if 0x80040000 ≤ a.toNat ∧ a.toNat < 0x8004004d then raw.getD (a.toNat-0x80040000) 255#8
  else 255#8

def core : Core :=
  ⟨0x8000052e#32,(fun r => if r = 2 then 0x80050050#32 else if r = 21 then 0x80020000#32
    else if r = 23 then 0x80010000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

theorem raw_span : Bytes.Span UartPlatform.board ram 0x80040000#32 raw := by
  apply Bytes.of_block
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · decide +kernel
  · have hf : ∀ i : Fin raw.length, ram (0x80040000#32+BitVec.ofNat 32 i.val) = raw[i] := by decide +kernel
    exact hf

theorem path_span : Bytes.Span UartPlatform.board ram 0x80040005#32 path := by
  exact Bytes.subspan raw_span 5 10 (by decide)

theorem body_span : Bytes.Span UartPlatform.board ram 0x80040049#32 body := by
  exact Bytes.subspan raw_span 73 77 (by decide)

theorem table : HeaderInput.Table UartPlatform.board ram (0x80020000#32+32#32) raw.length entries := by
  refine ⟨by decide,?_⟩
  intro i
  have hi : i.val < 2 := i.isLt
  have hc : i.val = 0 ∨ i.val = 1 := by omega
  change HeaderInput.Cell UartPlatform.board ram ((0x80020000#32+32#32)+BitVec.ofNat 32 (16*i.val)) raw.length (entries[i.val])
  rcases hc with he|he
  all_goals simp only [entries,he,List.getElem_cons_zero,List.getElem_cons_succ]
  all_goals constructor
  all_goals first
    | (unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (unfold HeaderSpec.Bounds;decide +kernel)
    | decide +kernel

theorem header_pre : Header.Pre UartPlatform.board ram 0x80020000#32 0x80040000#32 raw entries := by
  refine ⟨?_,by decide,by decide +kernel,by decide +kernel,by decide +kernel,raw_span,by decide,by decide,table⟩
  unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel

theorem initial_state : Encoding.SnapshotAt ram (0x80010000#32+4#32) Spec.initial := by
  have hh : ∀ i : Fin 10, ram ((0x80010000#32+4#32)+BitVec.ofNat 32 i.val) = Encoding.snapshotByte Spec.initial i := by decide +kernel
  exact hh

theorem pre : TxnInput.Pre UartPlatform.board core ram 0x80050000#32 0x80020000#32 0x80010000#32
    0x80040000#32 0x80040005#32 0x80040049#32 raw path body entries none false Spec.initial := by
  have hm : Memory.Block UartPlatform.board 0x80020000#32 372 := by
    unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  refine ⟨rfl,rfl,rfl,rfl,?_,by decide,?_,by decide,?_,initial_state,by decide +kernel,
    by decide +kernel,by decide +kernel,by decide +kernel,header_pre,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · exact TxnScratch.separate_of_before _ _ _ (by decide) (by decide)
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 328) hm (by decide) (by decide)),by decide,by decide +kernel,by decide +kernel,body_span⟩
  · exact ⟨(by simpa only [BitVec.add_zero] using Memory.sub_block (off := 0) (m := 312) hm (by decide) (by decide)),by decide,by decide +kernel,by decide +kernel,path_span⟩
  · exact .missing hm (by decide) (by decide +kernel)
  all_goals exact TxnScratch.separate_of_before _ _ _ (by decide) (by decide)

end E5R.Thermostat.ErrorRequestDenied
