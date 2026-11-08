import Projects.thermostat.MainChunkBuffered
import Projects.thermostat.MainChunkRefill
import Projects.thermostat.HttpRequestBytes
import Projects.thermostat.ReadSendWitness
namespace E5R.Thermostat.MainChunkBufferedWitness
open E5R E5R.Thermostat HttpRequestSpec
abbrev B := UartPlatform.board

def sp : Word := 0x80ffeb90#32
def raw := WireSpec.ascii "POST /mode HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\nAuthorization: Bearer dev-key\r\n\r\n4\r\nauto\r\n0\r\n\r\n"
def wire (i : Nat) : BitVec 8 := raw[i]?.getD 0#8
def filled (short : Bool) : Nat := if short then 91 else 105

def core : Core :=
  ⟨0x80000e9a#32,(fun r => if r=2 then sp else if r=8 then 0x80fff814#32
    else if r=23 then 0x80fff9f0#32 else if r=24 then 91#32 else if r=22 then 1#32
    else if r=19 then 0x10000000#32 else 0#32),false,false,3,0,0,0,0,0,false⟩

def ram (short : Bool) (a : Word) : BitVec 8 :=
  if 0x80ffec14≤a.toNat ∧ a.toNat<0x80ffec14+105 then wire (a.toNat-0x80ffec14)
  else if 0x80fff9f0≤a.toNat ∧ a.toNat<0x80fffa10 then 0#8
  else if a=0x80fff868#32 then BitVec.ofNat 8 (filled short)
  else if a=0x80fff869#32 ∨ a=0x80fff86a#32 ∨ a=0x80fff86b#32 then 0#8
  else if a=0x80fff864#32 then 0#8
  else if a=0x80fff865#32 then 4#8
  else if a=0x80fff866#32 then 0#8
  else if a=0x80fff867#32 then 0#8
  else if a=0x80fff880#32 then 20#8
  else if a=0x80fff881#32 then 236#8
  else if a=0x80fff882#32 then 255#8
  else if a=0x80fff883#32 then 128#8
  else if a=0x80fff884#32 then 0#8
  else if a=0x80fff885#32 then 8#8
  else if a=0x80fff886#32 then 0#8
  else if a=0x80fff887#32 then 0#8
  else if a=0x80fff9c4#32 then 96#8
  else if a=0x80fff9c5#32 then 248#8
  else if a=0x80fff9c6#32 then 255#8
  else if a=0x80fff9c7#32 then 128#8
  else if a=0x80fff9c8#32 then 104#8
  else if a=0x80fff9c9#32 then 248#8
  else if a=0x80fff9ca#32 then 255#8
  else if a=0x80fff9cb#32 then 128#8
  else if a=0x80fff9d8#32 then 91#8
  else if a=0x80fff9d9#32 then 0#8
  else if a=0x80fff9da#32 then 0#8
  else if a=0x80fff9db#32 then 0#8
  else if a=0x80fff9dc#32 then 91#8
  else if a=0x80fff9dd#32 then 0#8
  else if a=0x80fff9de#32 then 0#8
  else if a=0x80fff9df#32 then 0#8
  else ReadSendWitness.ram false false a

/-- A proper Host-bearing byte-level fixture. This separate pure parser check
    does not claim that the unproved ELF head parser reached this cutpoint. -/
theorem head : HttpRequestBytes.parse raw 1024 1024=
    .done ⟨(0,4),(5,10),1,[⟨21,25,27,28⟩,⟨30,47,49,56⟩,⟨58,71,73,87⟩],91,.chunked⟩ := by decide +kernel

theorem pre (short : Bool) : MainChunkLoopInvariant.At B core (ram short) sp 91 91 91 (filled short) cStart := by
  cases short <;> constructor
  all_goals first
    | rfl
    | (unfold Memory.Block B UartPlatform.board sp;rw [ThermostatImage.image_rwBase];decide +kernel)
    | (exact ChunkDecodedInvariant.initial 1024)
    | (constructor! <;> decide +kernel)
    | decide +kernel

theorem app (short : Bool) : AppState.At (ram short) Spec.initial := by
  cases short <;> constructor
  all_goals first
    | (change ∀ i : Fin 10, ram _ (0x80ffebc0#32+BitVec.ofNat 32 i.val)=Encoding.snapshotByte Spec.initial i;decide +kernel)
    | decide +kernel

theorem unread (short : Bool) : ChunkBufferView.Unread wire (ram short) sp 91 (filled short) := by
  cases short
  · intro k hk he
    change k<105 at he
    have cases : k=91 ∨ k=92 ∨ k=93 ∨ k=94 ∨ k=95 ∨ k=96 ∨ k=97 ∨ k=98 ∨ k=99 ∨ k=100 ∨ k=101 ∨ k=102 ∨ k=103 ∨ k=104 := by omega
    rcases cases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide +kernel
  · intro k hk he
    change k<91 at he
    omega

theorem expected : ChunkBufferSpec.consume wire 14 91 91 cStart []=
    ⟨105,95,⟨7,0,0,4⟩,WireSpec.ascii "auto",.done⟩ := by decide +kernel

/-- A complete actual buffered dechunking run with a satisfiable main layout,
    exact payload and preserved committed App state/borrow availability. -/
theorem execution : ∃ n d after, n≤1750 ∧
    Trace.Closed B img n ⟨core,ram false⟩ ⟨d,after⟩ ∧ d.pc=0x8000106c#32 ∧
    ChunkBufferView.Body after sp 91 (WireSpec.ascii "auto") ∧
    ramRead after (sp+3656#32) .w=105#32 ∧ ramRead after (sp+3660#32) .w=95#32 ∧
    AppState.At after Spec.initial := by
  obtain ⟨n,d,after,hn,trace,bound,body,unread,appFrame,header,limit,exhaust,safe⟩ :=
    MainChunkBuffered.all_buffered wire (body := []) (pre false) (unread false) (by intro i;have := i.isLt;contradiction) rfl
  change n≤125*14 at hn
  change MainChunkBuffered.Boundary B d after sp 91 105 (ChunkBufferSpec.consume wire 14 91 91 cStart []) at bound
  rw [expected] at bound
  change MainChunkBuffered.Terminal after sp 91 ⟨105,95,⟨7,0,0,4⟩,WireSpec.ascii "auto",.done⟩ d at bound
  rcases bound with ⟨pc,obj,inv,rd,wr,layout,stack,mask,tag⟩
  change ChunkBufferView.Body after sp 91 (ChunkBufferSpec.consume wire 14 91 91 cStart []).body at body
  rw [expected] at body
  exact ⟨n,d,after,by omega,trace,pc,body,rd,wr,appFrame rfl Spec.initial (app false)⟩

/-- The empty-buffer invariant is also satisfiable: a real wait, ready poll,
    and RBR byte preserve it, without assuming an entire request arrived. -/
theorem refill : ∃ d after,
    Observed.Steps B img 30 ⟨core,ram true⟩ ⟨d,after⟩ (MainChunkRefill.reads [0#32] 1#32 52#32) [] ∧
    MainChunkLoopInvariant.At B d after sp 91 91 91 92 cStart ∧
    after ((sp+132#32)+91#32)=52#8 ∧ AppState.At after Spec.initial := by
  obtain ⟨d,after,trace,inv,rx,stored,appFrame⟩ := MainChunkRefill.contract (pre true) rfl (by decide)
    [0#32] 1#32 52#32 (by intro status hs;simp only [List.mem_singleton] at hs;subst status;decide +kernel) (by decide +kernel)
  exact ⟨d,after,trace,inv,stored,appFrame rfl Spec.initial (app true)⟩
end E5R.Thermostat.MainChunkBufferedWitness
