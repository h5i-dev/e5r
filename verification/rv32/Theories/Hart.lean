/-
  RV32IMAC + Zicsr hart semantics for the e5r firmware product scope.

  Original e5r code, Apache-2.0, written from the RISC-V Unprivileged ISA
  (20240411) and Privileged Architecture (20240411) specifications. The split
  between a pure instruction semantics that returns a first-order effect tree
  and a separate interpreter that owns memory and devices follows the design
  of Theorem Labs' rocq-linux-process-semantics (MIT): no code was copied.

  `exec` never touches memory. Loads, stores, atomics and nondeterministic
  choices are `Eff` nodes that a board interpreter (`Theories/Platform.lean`)
  answers. Two kinds of failure are kept apart, as in that design:

  * `Eff.trap` -- the architecture defines this execution to raise a
    synchronous exception (illegal instruction, misaligned target, ecall).
  * `Eff.unsupported` -- the model declines: a legal behavior that is outside
    the verified envelope (an unmodeled CSR, entering U-mode, ...).

  The product's safety statement proves that neither is reachable, so the
  model never needs to run an exception handler.
-/

set_option linter.constructorNameAsVariable false

namespace E5R

abbrev Word := BitVec 32
abbrev Reg := Fin 32

inductive Width where
  | b | h | w
  deriving DecidableEq, Repr

def Width.bytes : Width → Nat
  | .b => 1 | .h => 2 | .w => 4

inductive AluOp where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  deriving DecidableEq, Repr

inductive MulOp where
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr

inductive BrCond where
  | eq | ne | lt | ge | ltu | geu
  deriving DecidableEq, Repr

inductive AmoOp where
  | swap | add | xor | and | or | min | max | minu | maxu
  deriving DecidableEq, Repr

inductive CsrOp where
  | rw | rs | rc
  deriving DecidableEq, Repr

/-- The CSR operand: a register (`csrrw` & co.) or a 5-bit immediate. -/
inductive CsrSrc where
  | reg (r : Reg)
  | imm (v : Word)
  deriving DecidableEq, Repr

inductive Instr where
  | lui (rd : Reg) (imm : Word)
  | auipc (rd : Reg) (imm : Word)
  | jal (rd : Reg) (off : Word)
  | jalr (rd rs1 : Reg) (off : Word)
  | branch (c : BrCond) (rs1 rs2 : Reg) (off : Word)
  | load (w : Width) (signed : Bool) (rd rs1 : Reg) (off : Word)
  | store (w : Width) (rs1 rs2 : Reg) (off : Word)
  | opimm (op : AluOp) (rd rs1 : Reg) (imm : Word)
  | op (op : AluOp) (rd rs1 rs2 : Reg)
  | muldiv (op : MulOp) (rd rs1 rs2 : Reg)
  | lr (rd rs1 : Reg)
  | sc (rd rs1 rs2 : Reg)
  | amo (op : AmoOp) (rd rs1 rs2 : Reg)
  | fence
  | fencei
  | csr (op : CsrOp) (rd : Reg) (src : CsrSrc) (addr : Nat)
  | ecall
  | ebreak
  | mret
  | wfi
  deriving DecidableEq, Repr

/-! ## Decoding

Decoding is a total function of the fetched bits. Every encoding outside
RV32IMAC + Zicsr + Zifencei + {MRET, WFI} is `none`, which `step` turns into
an illegal-instruction trap: the FE310-G002's E31 core implements exactly
RV32IMAC, so on that core those encodings trap too. -/

def bits (w : Word) (lo len : Nat) : Nat := (w.extractLsb' lo len).toNat
def reg (w : Word) (lo : Nat) : Reg := ⟨bits w lo 5 % 32, Nat.mod_lt _ (by decide)⟩
def sext (len : Nat) (v : Nat) : Word := (BitVec.ofNat len v).signExtend 32

def immI (w : Word) : Word := sext 12 (bits w 20 12)
def immS (w : Word) : Word := sext 12 (bits w 25 7 * 32 + bits w 7 5)
def immB (w : Word) : Word :=
  sext 13 (bits w 31 1 * 4096 + bits w 7 1 * 2048 + bits w 25 6 * 32 + bits w 8 4 * 2)
def immJ (w : Word) : Word :=
  sext 21 (bits w 31 1 * 1048576 + bits w 12 8 * 4096 + bits w 20 1 * 2048 + bits w 21 10 * 2)
def immU (w : Word) : Word := BitVec.ofNat 32 (bits w 12 20 * 4096)

def decode32 (w : Word) : Option Instr :=
  let rd := reg w 7
  let rs1 := reg w 15
  let rs2 := reg w 20
  let f3 := bits w 12 3
  let f7 := bits w 25 7
  match bits w 0 7 with
  | 0x37 => some (.lui rd (immU w))
  | 0x17 => some (.auipc rd (immU w))
  | 0x6f => some (.jal rd (immJ w))
  | 0x67 => if f3 = 0 then some (.jalr rd rs1 (immI w)) else none
  | 0x63 =>
    let c? : Option BrCond := match f3 with
      | 0 => some .eq | 1 => some .ne | 4 => some .lt
      | 5 => some .ge | 6 => some .ltu | 7 => some .geu | _ => none
    c?.map fun c => .branch c rs1 rs2 (immB w)
  | 0x03 =>
    match f3 with
    | 0 => some (.load .b true rd rs1 (immI w))
    | 1 => some (.load .h true rd rs1 (immI w))
    | 2 => some (.load .w true rd rs1 (immI w))
    | 4 => some (.load .b false rd rs1 (immI w))
    | 5 => some (.load .h false rd rs1 (immI w))
    | _ => none
  | 0x23 =>
    match f3 with
    | 0 => some (.store .b rs1 rs2 (immS w))
    | 1 => some (.store .h rs1 rs2 (immS w))
    | 2 => some (.store .w rs1 rs2 (immS w))
    | _ => none
  | 0x13 =>
    let imm := immI w
    match f3 with
    | 0 => some (.opimm .add rd rs1 imm)
    | 2 => some (.opimm .slt rd rs1 imm)
    | 3 => some (.opimm .sltu rd rs1 imm)
    | 4 => some (.opimm .xor rd rs1 imm)
    | 6 => some (.opimm .or rd rs1 imm)
    | 7 => some (.opimm .and rd rs1 imm)
    | 1 => if f7 = 0 then some (.opimm .sll rd rs1 (BitVec.ofNat 32 (bits w 20 5))) else none
    | 5 =>
      if f7 = 0 then some (.opimm .srl rd rs1 (BitVec.ofNat 32 (bits w 20 5)))
      else if f7 = 0x20 then some (.opimm .sra rd rs1 (BitVec.ofNat 32 (bits w 20 5)))
      else none
    | _ => none
  | 0x33 =>
    if f7 = 0 then
      let op : AluOp := match f3 with
        | 0 => .add | 1 => .sll | 2 => .slt | 3 => .sltu
        | 4 => .xor | 5 => .srl | 6 => .or | _ => .and
      some (.op op rd rs1 rs2)
    else if f7 = 0x20 then
      if f3 = 0 then some (.op .sub rd rs1 rs2)
      else if f3 = 5 then some (.op .sra rd rs1 rs2) else none
    else if f7 = 1 then
      let op : MulOp := match f3 with
        | 0 => .mul | 1 => .mulh | 2 => .mulhsu | 3 => .mulhu
        | 4 => .div | 5 => .divu | 6 => .rem | _ => .remu
      some (.muldiv op rd rs1 rs2)
    else none
  | 0x0f =>
    -- The FENCE fields (fm, pred, succ, rd, rs1) do not change behavior on
    -- one hart with no other bus master; the spec asks that unknown values be
    -- treated as an ordinary fence.
    if f3 = 0 then some .fence else if f3 = 1 then some .fencei else none
  | 0x73 =>
    if f3 = 0 then
      if w = 0x00000073 then some .ecall
      else if w = 0x00100073 then some .ebreak
      else if w = 0x30200073 then some .mret
      else if w = 0x10500073 then some .wfi
      else none
    else
      let addr := bits w 20 12
      let uimm : Word := BitVec.ofNat 32 (bits w 15 5)
      match f3 with
      | 1 => some (.csr .rw rd (.reg rs1) addr)
      | 2 => some (.csr .rs rd (.reg rs1) addr)
      | 3 => some (.csr .rc rd (.reg rs1) addr)
      | 5 => some (.csr .rw rd (.imm uimm) addr)
      | 6 => some (.csr .rs rd (.imm uimm) addr)
      | 7 => some (.csr .rc rd (.imm uimm) addr)
      | _ => none
  | 0x2f =>
    if f3 ≠ 2 then none else
    match bits w 27 5 with
    | 0x02 => if bits w 20 5 = 0 then some (.lr rd rs1) else none
    | 0x03 => some (.sc rd rs1 rs2)
    | 0x01 => some (.amo .swap rd rs1 rs2)
    | 0x00 => some (.amo .add rd rs1 rs2)
    | 0x04 => some (.amo .xor rd rs1 rs2)
    | 0x0c => some (.amo .and rd rs1 rs2)
    | 0x08 => some (.amo .or rd rs1 rs2)
    | 0x10 => some (.amo .min rd rs1 rs2)
    | 0x14 => some (.amo .max rd rs1 rs2)
    | 0x18 => some (.amo .minu rd rs1 rs2)
    | 0x1c => some (.amo .maxu rd rs1 rs2)
    | _ => none
  | _ => none

/-- Compressed register field: x8..x15. -/
def creg (h : Word) (lo : Nat) : Reg := ⟨8 + bits h lo 3, by unfold bits; omega⟩

/-- RV32C without the floating-point loads and stores, expanded to the base
    instruction each encoding is defined to be. Reserved encodings and the
    all-zero halfword are `none` (illegal). HINT encodings expand to their
    base instruction, which is what they execute as. -/
def decode16 (h : Word) : Option Instr :=
  let rd := reg h 7
  let rs2 := reg h 2
  let f3 := bits h 13 3
  let imm6 := sext 6 (bits h 12 1 * 32 + bits h 2 5)
  let cj := sext 12 (bits h 12 1 * 2048 + bits h 8 1 * 1024 + bits h 9 2 * 256 +
    bits h 6 1 * 128 + bits h 7 1 * 64 + bits h 2 1 * 32 + bits h 11 1 * 16 + bits h 3 3 * 2)
  let cb := sext 9 (bits h 12 1 * 256 + bits h 5 2 * 64 + bits h 2 1 * 32 +
    bits h 10 2 * 8 + bits h 3 2 * 2)
  let clw := BitVec.ofNat 32 (bits h 5 1 * 64 + bits h 10 3 * 8 + bits h 6 1 * 4)
  match bits h 0 2, f3 with
  | 0, 0 =>
    let n := bits h 7 4 * 64 + bits h 11 2 * 16 + bits h 5 1 * 8 + bits h 6 1 * 4
    if n = 0 then none else some (.opimm .add (creg h 2) 2 (BitVec.ofNat 32 n))
  | 0, 2 => some (.load .w true (creg h 2) (creg h 7) clw)
  | 0, 6 => some (.store .w (creg h 7) (creg h 2) clw)
  | 1, 0 => some (.opimm .add rd rd imm6)
  | 1, 1 => some (.jal 1 cj)
  | 1, 2 => some (.opimm .add rd 0 imm6)
  | 1, 3 =>
    if rd.val = 2 then
      let n := bits h 12 1 * 512 + bits h 3 2 * 128 + bits h 5 1 * 64 +
        bits h 2 1 * 32 + bits h 6 1 * 16
      if n = 0 then none else some (.opimm .add 2 2 (sext 10 n))
    else
      let n := bits h 12 1 * 32 + bits h 2 5
      if n = 0 then none else some (.lui rd (sext 18 (n * 4096)))
  | 1, 4 =>
    let r := creg h 7
    let sh := BitVec.ofNat 32 (bits h 2 5)
    match bits h 10 2 with
    | 0 => if bits h 12 1 = 0 then some (.opimm .srl r r sh) else none
    | 1 => if bits h 12 1 = 0 then some (.opimm .sra r r sh) else none
    | 2 => some (.opimm .and r r imm6)
    | _ =>
      if bits h 12 1 = 1 then none else
      let op : AluOp := match bits h 5 2 with
        | 0 => .sub | 1 => .xor | 2 => .or | _ => .and
      some (.op op r r (creg h 2))
  | 1, 5 => some (.jal 0 cj)
  | 1, 6 => some (.branch .eq (creg h 7) 0 cb)
  | 1, 7 => some (.branch .ne (creg h 7) 0 cb)
  | 2, 0 =>
    if bits h 12 1 = 0 then some (.opimm .sll rd rd (BitVec.ofNat 32 (bits h 2 5))) else none
  | 2, 2 =>
    if rd.val = 0 then none else
    some (.load .w true rd 2 (BitVec.ofNat 32 (bits h 2 2 * 64 + bits h 12 1 * 32 + bits h 4 3 * 4)))
  | 2, 4 =>
    if bits h 12 1 = 0 then
      if rs2.val = 0 then (if rd.val = 0 then none else some (.jalr 0 rd 0))
      else some (.op .add rd 0 rs2)
    else
      if rs2.val = 0 then (if rd.val = 0 then some .ebreak else some (.jalr 1 rd 0))
      else some (.op .add rd rd rs2)
  | 2, 6 => some (.store .w 2 rs2 (BitVec.ofNat 32 (bits h 7 2 * 64 + bits h 9 4 * 4)))
  | _, _ => none

/-! ## Core state -/

/-- The architectural state the ISA owns. Memory and devices are not here.
    Only the machine-mode CSRs of the product scope are state; any other CSR
    access is `unsupported`. -/
structure Core where
  pc : Word
  x : Reg → Word
  mie_ : Bool        -- mstatus.MIE
  mpie : Bool        -- mstatus.MPIE
  mpp : BitVec 2     -- mstatus.MPP
  mieReg : Word      -- mie (only MSIE, MTIE, MEIE are implemented)
  mtvec : Word
  mepc : Word
  mcause : Word
  mscratch : Word
  /-- An LR reservation is held. SC may succeed only while one is. -/
  resv : Bool

def Core.get (c : Core) (r : Reg) : Word := if r.val = 0 then 0 else c.x r
def Core.set (c : Core) (r : Reg) (v : Word) : Core :=
  if r.val = 0 then c else { c with x := fun i => if i = r then v else c.x i }

inductive Exc where
  | illegal | misalignedFetch | ecall | ebreak
  deriving DecidableEq, Repr

/-- The effect tree of one instruction (or one interrupt entry). -/
inductive Eff where
  | done (c : Core)
  | trap (e : Exc)
  | unsupported (why : String)
  /-- A zero-extended load of `w`; `atomic` marks LR and AMOs. -/
  | load (w : Width) (addr : Word) (atomic : Bool) (k : Word → Eff)
  | store (w : Width) (addr : Word) (v : Word) (atomic : Bool) (k : Eff)
  /-- A nondeterministic choice the environment makes (SC success, mip). -/
  | choose (k : Bool → Eff)
  | pick (k : Word → Eff)

/-! ## Arithmetic -/

def alu (op : AluOp) (a b : Word) : Word :=
  match op with
  | .add => a + b
  | .sub => a - b
  | .sll => a <<< (b.toNat % 32)
  | .slt => if a.slt b then 1 else 0
  | .sltu => if a.ult b then 1 else 0
  | .xor => a ^^^ b
  | .srl => a >>> (b.toNat % 32)
  | .sra => a.sshiftRight (b.toNat % 32)
  | .or => a ||| b
  | .and => a &&& b

/-- M extension, with the division-by-zero and overflow results the
    specification defines (no trap). -/
def muldiv (op : MulOp) (a b : Word) : Word :=
  match op with
  | .mul => a * b
  | .mulh => BitVec.ofInt 32 ((a.toInt * b.toInt) / 4294967296)
  | .mulhsu => BitVec.ofInt 32 ((a.toInt * (b.toNat : Int)) / 4294967296)
  | .mulhu => BitVec.ofNat 32 (a.toNat * b.toNat / 4294967296)
  | .div => if b = 0 then BitVec.allOnes 32 else BitVec.ofInt 32 (a.toInt.tdiv b.toInt)
  | .divu => if b = 0 then BitVec.allOnes 32 else BitVec.ofNat 32 (a.toNat / b.toNat)
  | .rem => if b = 0 then a else BitVec.ofInt 32 (a.toInt.tmod b.toInt)
  | .remu => if b = 0 then a else BitVec.ofNat 32 (a.toNat % b.toNat)

def amoOp (op : AmoOp) (old v : Word) : Word :=
  match op with
  | .swap => v
  | .add => old + v
  | .xor => old ^^^ v
  | .and => old &&& v
  | .or => old ||| v
  | .min => if old.slt v then old else v
  | .max => if old.slt v then v else old
  | .minu => if old.ult v then old else v
  | .maxu => if old.ult v then v else old

def taken (c : BrCond) (a b : Word) : Bool :=
  match c with
  | .eq => a == b | .ne => a != b
  | .lt => a.slt b | .ge => !a.slt b
  | .ltu => a.ult b | .geu => !a.ult b

def extend (w : Width) (signed : Bool) (v : Word) : Word :=
  match w, signed with
  | .b, true => (v.setWidth 8).signExtend 32
  | .h, true => (v.setWidth 16).signExtend 32
  | .b, false => v &&& 0xff
  | .h, false => v &&& 0xffff
  | .w, _ => v

/-- A control transfer. With C, IALIGN is 16: only bit 0 must be clear. -/
def jump (c : Core) (target : Word) : Eff :=
  if target.getLsbD 0 then .trap .misalignedFetch else .done { c with pc := target }

/-! ## Machine-mode CSRs of the product scope -/

def csrMstatus := 0x300
def csrMie := 0x304
def csrMtvec := 0x305
def csrMscratch := 0x340
def csrMepc := 0x341
def csrMcause := 0x342
def csrMip := 0x344
def csrMhartid := 0xf14

def mstatusOf (c : Core) : Word :=
  (if c.mie_ then 8 else 0) ||| (if c.mpie then 0x80 else 0) ||| (c.mpp.setWidth 32 <<< 11)

/-- Bits of mie that the E31 implements: MSIE, MTIE, MEIE. -/
def mieMask : Word := 0x888

/-- Write a CSR. Fields outside the modeled subset decline rather than guess
    at WARL behavior. -/
def csrWrite (c : Core) (addr : Nat) (v : Word) (fin : Core → Eff) : Eff :=
  if addr = csrMstatus then
    let mpp := v.extractLsb' 11 2
    if v &&& ~~~(0x1888 : Word) ≠ 0 then .unsupported "mstatus field outside MIE/MPIE/MPP"
    else if mpp ≠ 0 ∧ mpp ≠ 3 then .unsupported "mstatus.MPP other than M or U"
    else fin { c with mie_ := v.getLsbD 3, mpie := v.getLsbD 7, mpp := mpp }
  else if addr = csrMie then fin { c with mieReg := v &&& mieMask }
  else if addr = csrMtvec then
    if v.extractLsb' 0 2 = 0 ∨ v.extractLsb' 0 2 = 1 then fin { c with mtvec := v }
    else .unsupported "mtvec mode"
  else if addr = csrMscratch then fin { c with mscratch := v }
  else if addr = csrMepc then fin { c with mepc := v &&& ~~~1 }
  -- MSIP, MTIP and MEIP are read-only in mip; the other bits are not implemented.
  else if addr = csrMip then fin c
  else .unsupported "CSR write"

/-- Read a CSR and continue. mip is environmental: its pending bits change
    with time and devices, so its value is picked. -/
def csrRead (c : Core) (addr : Nat) (k : Word → Eff) : Eff :=
  if addr = csrMstatus then k (mstatusOf c)
  else if addr = csrMie then k c.mieReg
  else if addr = csrMtvec then k c.mtvec
  else if addr = csrMscratch then k c.mscratch
  else if addr = csrMepc then k c.mepc
  else if addr = csrMcause then k c.mcause
  else if addr = csrMip then .pick fun v => k (v &&& mieMask)
  else if addr = csrMhartid then k 0
  else .unsupported "CSR read"

def execCsr (c : Core) (op : CsrOp) (rd : Reg) (src : CsrSrc) (addr : Nat)
    (fin : Core → Eff) : Eff :=
  let operand := match src with | .reg r => c.get r | .imm v => v
  let srcZero : Bool := match src with | .reg r => r.val == 0 | .imm v => v == 0
  let writes : Bool := op == .rw || !srcZero
  -- addr[11:10] = 3 marks a read-only CSR: writing one is illegal.
  if writes && addr / 1024 == 3 then .trap .illegal else
  csrRead c addr fun old =>
    let c' := c.set rd old
    if !writes then fin c' else
    let new := match op with
      | .rw => operand | .rs => old ||| operand | .rc => old &&& ~~~operand
    csrWrite c' addr new fin

/-! ## Instruction semantics

`exec c len i`: `len` is the encoded length (2 or 4), so `pc + len` is the
fall-through and link address. -/

def exec (c : Core) (len : Word) (i : Instr) : Eff :=
  let next := c.pc + len
  let adv (c' : Core) : Eff := .done { c' with pc := next }
  match i with
  | .lui rd imm => adv (c.set rd imm)
  | .auipc rd imm => adv (c.set rd (c.pc + imm))
  | .jal rd off => jump (c.set rd next) (c.pc + off)
  | .jalr rd rs1 off => jump (c.set rd next) ((c.get rs1 + off) &&& ~~~1)
  | .branch cond rs1 rs2 off =>
    if taken cond (c.get rs1) (c.get rs2) then jump c (c.pc + off) else adv c
  | .load w signed rd rs1 off =>
    .load w (c.get rs1 + off) false fun v => adv (c.set rd (extend w signed v))
  | .store w rs1 rs2 off => .store w (c.get rs1 + off) (c.get rs2) false (adv c)
  | .opimm op rd rs1 imm => adv (c.set rd (alu op (c.get rs1) imm))
  | .op op rd rs1 rs2 => adv (c.set rd (alu op (c.get rs1) (c.get rs2)))
  | .muldiv op rd rs1 rs2 => adv (c.set rd (muldiv op (c.get rs1) (c.get rs2)))
  | .lr rd rs1 =>
    .load .w (c.get rs1) true fun v => adv ({ c with resv := true }.set rd v)
  | .sc rd rs1 rs2 =>
    -- With a reservation the SC may still fail (the spec permits spurious
    -- failure); without one it must fail. Either way the reservation ends.
    let fail := adv ({ c with resv := false }.set rd 1)
    if ¬ c.resv then fail else
    .choose fun ok =>
      if ok then .store .w (c.get rs1) (c.get rs2) true (adv ({ c with resv := false }.set rd 0))
      else fail
  | .amo op rd rs1 rs2 =>
    .load .w (c.get rs1) true fun old =>
      .store .w (c.get rs1) (amoOp op old (c.get rs2)) true (adv (c.set rd old))
  | .fence => adv c
  | .fencei => adv c
  | .csr op rd src addr => execCsr c op rd src addr adv
  | .ecall => .trap .ecall
  | .ebreak => .trap .ebreak
  | .mret =>
    -- MPP = U would enter user mode, which is outside the scope.
    if c.mpp ≠ 3 then .unsupported "mret to a mode other than M" else
    jump { c with mie_ := c.mpie, mpie := true, mpp := 0 } c.mepc
  -- WFI may be a NOP; with interrupts possible at every boundary that covers
  -- every stall a core can make.
  | .wfi => adv c

/-- Interrupt causes the E31's CLINT mode can raise: software (3), timer (7)
    and external (11). -/
def irqCodes : List Nat := [3, 7, 11]

/-- Machine-mode interrupt entry (Privileged spec 3.1.6.1, 3.1.7). -/
def takeIrq (c : Core) (code : Nat) : Eff :=
  let base := c.mtvec &&& ~~~3
  let target := if c.mtvec.extractLsb' 0 2 = 1 then base + BitVec.ofNat 32 (4 * code) else base
  if target.getLsbD 0 then .trap .misalignedFetch else
  .done { c with pc := target, mepc := c.pc, mcause := BitVec.ofNat 32 (2^31 + code),
                 mpie := c.mie_, mie_ := false, mpp := 3 }

/-- An interrupt with `code` may be taken at an instruction boundary when
    machine interrupts are enabled and that source is enabled. Whether it is
    pending is environmental, so the model allows it whenever it is enabled. -/
def irqEnabled (c : Core) (code : Nat) : Bool :=
  c.mie_ && code ∈ irqCodes && c.mieReg.getLsbD code

end E5R
