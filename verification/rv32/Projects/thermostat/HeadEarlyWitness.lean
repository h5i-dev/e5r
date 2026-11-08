import Projects.thermostat.HeadEarlyInput
import Projects.thermostat.ReadSendWitness
set_option maxRecDepth 5000
namespace E5R.Thermostat.HeadEarlyWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board
abbrev Kind := HeadEarlyFinish.Kind

def sp : Word := 0x80ffea10#32

def input : Kind → List (BitVec 8)
  | .incomplete => WireSpec.ascii "POST /mode HTTP/1.1"
  | .bad => WireSpec.ascii "POST /mode HTTP/1.1\n"
  | .tooLong => List.replicate 1024 65#8

def core (kind : Kind) : Core :=
  ⟨0x80002c46#32,(fun r => if r=1 then 0x80000a26#32 else if r=2 then 0x80ffeb90#32
    else if r=8 then 0x80fff814#32 else if r=10 then 0x80fffd38#32 else if r=11 then 0x80ffec14#32
    else if r=12 then BitVec.ofNat 32 (input kind).length else if r=13 then 0x80fff860#32
    else if r=19 then 0x10000000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (kind : Kind) (a : Word) : BitVec 8 :=
  if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec14+(input kind).length then
    if kind=.tooLong then 65#8 else (input kind)[a.toNat-0x80ffec14]?.getD 0#8
  else if a=0x80fff861#32 then 4#8
  else if a=0x80fff860#32 ∨ a=0x80fff862#32 ∨ a=0x80fff863#32 then 0#8
  else ReadSendWitness.ram false false a

theorem stack : Memory.Block B sp 5312 := by
  unfold Memory.Block B UartPlatform.board sp
  rw [ThermostatImage.image_rwBase]
  decide +kernel

theorem max_head (kind : Kind) : ramRead (ram kind) (sp+3664#32) .w=1024#32 := by
  cases kind <;> decide +kernel

theorem app (kind : Kind) : AppState.At (ram kind) Spec.initial := by
  cases kind <;> constructor
  all_goals first
    | (change ∀ i : Fin 10, ram _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem bytes (kind : Kind) : Bytes.At (ram kind) (sp+516#32) (input kind) := by
  cases kind with
  | incomplete => unfold Bytes.At;decide +kernel
  | bad => unfold Bytes.At;decide +kernel
  | tooLong =>
    intro i
    have hi : i.val<1024 := by simpa only [input,List.length_replicate] using i.isLt
    have base : sp+516#32=0x80ffec14#32 := by decide +kernel
    rw [base]
    change ram .tooLong (0x80ffec14#32+BitVec.ofNat 32 i.val)=(List.replicate 1024 65#8)[i.val]
    have bitnat : (BitVec.ofNat 32 i.val).toNat=i.val := by
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    have addr : (0x80ffec14#32+BitVec.ofNat 32 i.val).toNat=0x80ffec14+i.val := by
      rw [BitVec.toNat_add,bitnat]
      change (0x80ffec14+i.val)%4294967296=0x80ffec14+i.val
      rw [Nat.mod_eq_of_lt (by omega)]
    simp only [ram,input,List.length_replicate,addr,
      show 0x80ffec14≤0x80ffec14+i.val ∧ 0x80ffec14+i.val<0x80ffec14+1024 by omega,
      true_and,ite_true,List.getElem_replicate]

theorem term_incomplete : HeadByteInput.term (input .incomplete)=1 := by decide +kernel
theorem term_bad : HeadByteInput.term (input .bad)=2 := by decide +kernel

theorem term_long : HeadByteInput.term (input .tooLong)=1 := by
  let g := window (HttpRequestBytes.bytes (input .tooLong)) 1024
  have bound : ∀ k, k<1024 → g k=65 := by
    intro k hk
    simp only [g,window,hk,ite_true,HttpRequestBytes.bytes,input,List.map_replicate,
      show (65#8).toNat=65 by decide +kernel]
    simp only [List.getD_eq_getElem?_getD,List.getElem?_replicate,hk,ite_true,Option.getD_some]
  have line : lineEnd g 0 1024=1024 :=
    HeadLineScanSpec.scan_all notEol g 0 1024 (by decide) (by
      intro k lo hi
      rw [bound k hi]
      decide +kernel)
  change lineTerm g (lineEnd g 0 1024) 1024=1
  rw [line]
  simp only [lineTerm,Nat.le_refl,ite_true]

theorem early (kind : Kind) : HeadByteInput.term (input kind)=1 ∨ HeadByteInput.term (input kind)=2 := by
  cases kind with
  | incomplete => exact Or.inl term_incomplete
  | bad => exact Or.inr term_bad
  | tooLong => exact Or.inl term_long

theorem expected (kind : Kind) : HttpRequestBytes.parse (input kind) 1024 1024=HeadEarlyFinish.out kind := by
  rw [HeadByteInput.classification _ (early kind)]
  cases kind with
  | incomplete => rw [term_incomplete];rfl
  | bad => rw [term_bad];rfl
  | tooLong => rw [term_long];rfl

/-- Three satisfiable actual caller layouts exercise incomplete, malformed-LF
    and the 1024-byte first-line limit; every run really returns to main. -/
theorem execution (kind : Kind) : ∃ n d after, n≤7217 ∧
    Trace.Closed B img n ⟨core kind,ram kind⟩ ⟨d,after⟩ ∧ d.pc=0x80000a26#32 ∧ d.get 2=0x80ffeb90#32 ∧
    HeadSaved.CoreAt d (core kind).get ∧ HeadResultView.At after (sp+4904#32) (HeadEarlyFinish.out kind) ∧
    AppState.At after Spec.initial := by
  have len : (input kind).length≤2048 := by cases kind <;> decide +kernel
  obtain ⟨n,d,hlo,hn,trace,pc,stack,abi,result,rx,appFrame,csr⟩ := HeadEarlyInput.contract B (core kind) (ram kind) sp (input kind)
    rfl (by rfl) (by rfl) (by rfl) rfl (by rfl) HeadEarlyWitness.stack (by decide +kernel) len (max_head kind) (bytes kind) (early kind)
  rw [expected kind] at result
  have cap : min (input kind).length 1024≤1024 := Nat.min_le_right _ _
  have pc' : d.pc=0x80000a26#32 := by simpa only [show (core kind).get 1=0x80000a26#32 from rfl,
    show 0x80000a26#32 &&& ~~~1=0x80000a26#32 by decide +kernel] using pc
  exact ⟨n,d,_,by omega,Interrupt.close trace.det rfl,pc',stack,abi,result,appFrame rfl Spec.initial (app kind)⟩
end E5R.Thermostat.HeadEarlyWitness
