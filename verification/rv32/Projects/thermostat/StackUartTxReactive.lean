import Projects.thermostat.UartTxReactive
import Projects.thermostat.StackUartTxWaitSafety
import Projects.thermostat.StackUartStore
set_option autoImplicit false
set_option maxRecDepth 4000
namespace E5R.Thermostat.StackUartTxReactive
open E5R E5R.Thermostat ProtocolStreamSpec 
abbrev B := StackBoard.board
structure Context (c : Core) (ram : Word → BitVec 8) (src : Word) (bytes : List (BitVec 8)) : Prop where
  finish : c.get 14=src+BitVec.ofNat 32 bytes.length
  poll : c.get 13=0x10000000#32
  uart : c.get 15=0x10000000#32
  source : ReadBytes.Span B img ram src bytes
  nowrap : src.toNat+bytes.length<2^32
  masked : c.mie_=false

theorem recore {c d ram src bytes} (h : Context c ram src bytes)
    (regs : ∀ r : Reg,r≠12 → r≠16 → r≠17 → d.get r=c.get r) (csr : d.sameCsr c) : Context d ram src bytes :=
  ⟨(regs 14 (by decide) (by decide) (by decide)).trans h.finish,
   (regs 13 (by decide) (by decide) (by decide)).trans h.poll,
   (regs 15 (by decide) (by decide) (by decide)).trans h.uart,h.source,h.nowrap,(congrArg Prod.fst csr).trans h.masked⟩

structure Loading (c : Core) (ram : Word → BitVec 8) (src : Word) (byte : BitVec 8) (rest : List (BitVec 8)) : Prop where
  pc : c.pc=0x800007f4#32
  context : Context c ram src (byte::rest)
  pointer : c.get 12=src

structure Polling (c : Core) (ram : Word → BitVec 8) (src : Word) (byte : BitVec 8) (rest : List (BitVec 8)) : Prop where
  waiting : UartTxWaitSafety.Waiting c
  context : Context c ram src (byte::rest)
  pointer : c.get 12=src
  loaded : c.get 16=UartTxByte.word byte

structure BeforeEmit (c : Core) (ram : Word → BitVec 8) (src : Word) (byte : BitVec 8) (rest : List (BitVec 8)) : Prop where
  pc : c.pc=0x800007ea#32
  context : Context c ram src (byte::rest)
  pointer : c.get 12=src
  loaded : c.get 16=UartTxByte.word byte

structure Emitting (c : Core) (ram : Word → BitVec 8) (src : Word) (byte : BitVec 8) (rest : List (BitVec 8)) : Prop where
  pc : c.pc=0x800007ec#32
  context : Context c ram src (byte::rest)
  pointer : c.get 12=src+1#32
  loaded : c.get 16=UartTxByte.word byte

structure Branch (c : Core) (ram : Word → BitVec 8) (src : Word) (bytes : List (BitVec 8)) : Prop where
  pc : c.pc=0x800007f0#32
  context : Context c ram src bytes
  pointer : c.get 12=src

/-- Source RAM/ROM byte load is quiet for every oracle, not just one witness. -/
theorem load {c ram src byte rest} (h : Loading c ram src byte rest) :
    let d := c.wr 16 (UartTxByte.word byte) 0x800007f8#32
    Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ ∧ Polling d ram src byte rest := by
  refine ⟨?_,⟨Or.inl rfl,?_,?_,?_⟩⟩
  · intro o
    rw [Observed.stepInstr_of (by rw [h.pc];decide) (by rw [h.pc];exact tx2147485684),exec_load,h.pointer,BitVec.add_zero,
      ObservedByte.load (ReadBytes.head h.context.source) o _ 0 [] [],ReadBytes.extend_byte,h.pc]
    rfl
  · exact recore h.context (fun r a b e => Core.wr_get_ne _ _ _ _ _ b) rfl
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (12 : Reg)≠16)).trans h.pointer
  · exact Core.wr_get_self _ _ _ _ (by decide)

/-- Arbitrarily many arbitrary LSR values preserve the exact next output byte.
    Readiness is tested at its actual bit five, with no fairness premise. -/
theorem polling_next {c ram src byte rest} (h : Polling c ram src byte rest) (o : Oracle) :
    ∃ d reads,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [],reads⟩ ∧
      (Polling d ram src byte rest ∨ BeforeEmit d ram src byte rest) ∧
      UartTxWaitSafety.LsrOnly reads ∧ (∀ r : Reg,r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  obtain ⟨d,reads,step,post,only,regs,csr⟩ := StackUartTxWaitSafety.next ram ⟨h.waiting,h.context.poll,h.context.masked⟩ o
  have context := recore h.context (fun r a b e => regs r e) csr
  have pointer := (regs 12 (by decide)).trans h.pointer
  have loaded := (regs 16 (by decide)).trans h.loaded
  refine ⟨d,reads,step,?_,only,regs,csr⟩
  rcases post with waiting|exit
  · exact Or.inl ⟨waiting.1,context,pointer,loaded⟩
  · exact Or.inr ⟨exit.1,context,pointer,loaded⟩

theorem increment {c ram src byte rest} (h : BeforeEmit c ram src byte rest) :
    let d := c.wr 12 (src+1#32) 0x800007ec#32
    Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ ∧ Emitting d ram src byte rest := by
  refine ⟨?_,⟨rfl,recore h.context (fun r a b e => Core.wr_get_ne _ _ _ _ _ a) rfl,?_,?_⟩⟩
  · intro o
    rw [Observed.stepInstr_of (by rw [h.pc];decide) (by rw [h.pc];exact tx2147485674),exec_opimm,h.pointer,h.pc]
    rfl
  · exact Core.wr_get_self _ _ _ _ (by decide)
  · exact (Core.wr_get_ne _ _ _ _ _ (by decide : (16 : Reg)≠12)).trans h.loaded

/-- Every oracle produces the same single exact THR byte, no RBR byte and no
    RAM modification; the remaining source span and pointer are conclusions. -/
theorem emit {c ram src byte rest} (h : Emitting c ram src byte rest) (o : Oracle) :
    let d := c.goto 0x800007f0#32
    Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram [⟨0x10000000#32,UartTxByte.word byte⟩],[]⟩ ∧ Branch d ram (src+1#32) rest := by
  have store := StackUartStore.store ⟨c,ram⟩ o 15 16 0#32 4#32 0x10000000#32 (UartTxByte.word byte) UartPlatform.data
    (by rw [h.pc];decide) (by rw [h.pc];exact tx2147485676) (by rw [h.context.uart];decide +kernel) h.loaded
    (by decide) StackUartPlatform.data_device rfl rfl
  refine ⟨?_,⟨rfl,?_,h.pointer⟩⟩
  · simpa only [UartTxByte.word_mask,h.pc,show 0x800007ec#32+4#32=0x800007f0#32 by decide +kernel] using store
  · have next : (src+1#32).toNat=src.toNat+1 := WordZero.add_nat src 1 (by have := h.context.nowrap; simp only [List.length_cons] at this;omega)
    have finish : (src+1#32)+BitVec.ofNat 32 rest.length=src+BitVec.ofNat 32 (byte::rest).length := by
      rw [BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 rest.length]
    exact ⟨h.context.finish.trans finish.symm,h.context.poll,h.context.uart,ReadBytes.tail h.context.source,
      by rw [next];have := h.context.nowrap;simp only [List.length_cons] at this;omega,h.context.masked⟩


/-- The actual final-byte branch exits exactly when the source suffix is
    empty. Otherwise it returns to the checked next-byte load with its span. -/
theorem branch {c ram src bytes} (h : Branch c ram src bytes) :
    ∃ d,Quiet.Step B img ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=(if bytes=[] then 0x8000080a#32 else 0x800007f4#32) ∧
      Context d ram src bytes ∧ d.get 12=src ∧ (∀ r : Reg,d.get r=c.get r) ∧ d.sameCsr c := by
  let d := c.goto (if bytes=[] then 0x8000080a#32 else 0x800007f4#32)
  have equivalent : src=src+BitVec.ofNat 32 bytes.length ↔ bytes=[] := by
    constructor
    · intro eq
      have same : src+0#32=src+BitVec.ofNat 32 bytes.length := by simpa only [BitVec.add_zero] using eq
      rw [BitVec.add_right_inj] at same
      have numeric := congrArg BitVec.toNat same
      have small : bytes.length<2^32 := by have := h.context.nowrap;omega
      simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small] at numeric
      have zero : bytes.length=0 := by change 0=bytes.length at numeric;omega
      exact List.eq_nil_of_length_eq_zero zero
    · intro eq;subst bytes;exact (BitVec.add_zero src).symm
  have test : taken .eq src (src+BitVec.ofNat 32 bytes.length)=decide (bytes=[]) := by
    change decide (src=src+BitVec.ofNat 32 bytes.length)=decide (bytes=[])
    simp only [equivalent]
  refine ⟨d,?_,rfl,recore h.context (fun _ _ _ _ => rfl) rfl,h.pointer,fun _ => rfl,rfl⟩
  intro o
  rw [Observed.stepInstr_of (by rw [h.pc];decide) (by rw [h.pc];exact tx2147485680),exec_branch,h.pointer,h.context.finish,test]
  by_cases empty : bytes=[]
  · rw [decide_eq_true empty]
    simp only [ite_true]
    rw [h.pc,show 0x800007f0#32+26#32=0x8000080a#32 by decide +kernel,jump_ok _ _ (by decide)]
    simp only [d,empty,ite_true]
    rfl
  · rw [decide_eq_false empty]
    simp only [Bool.false_eq_true,ite_false,h.pc,d,empty]
    rfl
end E5R.Thermostat.StackUartTxReactive
