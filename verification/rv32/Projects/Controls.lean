/-
  Negative controls for the platform model: each fault class the model
  claims to detect, demonstrated on a one-instruction image and checked by
  the kernel. A model that silently accepted any of these would make a
  safety proof meaningless, so each is pinned here.
-/
import Theories.Platform
import Theories.Board.Hifive1Revb

set_option maxRecDepth 100000

namespace E5R.Controls
open E5R

abbrev B := Hifive1Revb.board

/-- One instruction word at the HiFive1 entry point. -/
def img (w : Nat) : List Segment :=
  [⟨0x20010000, [w % 256, w / 256 % 256, w / 65536 % 256, w / 16777216 % 256], true⟩]

/-- A core at the entry with `a0` = `a`, `a1` = `b`, a reservation `resv`. -/
def core (a b : Word) (resv := false) (mie := false) (mieReg : Word := 0) (mpp : BitVec 2 := 3) : Core :=
  { pc := 0x20010000, x := fun r => if r.val = 10 then a else if r.val = 11 then b else 0,
    mie_ := mie, mpie := false, mpp := mpp, mieReg := mieReg, mtvec := 0x20010000,
    mepc := 0x20010000, mcause := 0, mscratch := 0, resv := resv }

def run (w : Nat) (c : Core) : Result := stepInstr B (img w) ⟨c, fun _ => 0⟩ (fun _ => 1)

def isFault (f : Fault) : Result → Bool
  | .fault g => g == f
  | _ => false

def unsupportedFault : Result → Bool
  | .fault (.unsupported _) => true
  | _ => false

def okWith (p : Core → Bool) : Result → Bool
  | .ok c _ _ => p c
  | _ => false

-- lw a2, 0(a0) / sw a1, 0(a0) / lr.w / amoadd.w with a0 as the address
def lw := 0x00052603
def sw := 0x00b52023
def lh := 0x00051603
def lrw := 0x1005262f
def amoadd := 0x00b5262f
def scw := 0x18b5262f

theorem misaligned_load : isFault .misaligned (run lw (core 0x80000002 0)) = true := by decide +kernel
theorem misaligned_halfword : isFault .misaligned (run lh (core 0x80000001 0)) = true := by decide +kernel
theorem misaligned_store : isFault .misaligned (run sw (core 0x80000006 0)) = true := by decide +kernel
theorem unmapped_load : unsupportedFault (run lw (core 0x40000000 0)) = true := by decide +kernel
theorem load_past_ram : unsupportedFault (run lw (core 0x80004000 0)) = true := by decide +kernel
theorem store_to_flash : unsupportedFault (run sw (core 0x20010000 0)) = true := by decide +kernel
theorem device_halfword_read : unsupportedFault (run lh (core 0x10013004 0)) = true := by decide +kernel
theorem device_write_to_read_only : unsupportedFault (run sw (core 0x0200bff8 0)) = true := by decide +kernel
theorem unlisted_device : unsupportedFault (run lw (core 0x10012000 0)) = true := by decide +kernel
theorem atomic_on_device : unsupportedFault (run amoadd (core 0x10015024 0)) = true := by decide +kernel
theorem lr_on_flash : unsupportedFault (run lrw (core 0x20010000 0)) = true := by decide +kernel
-- An accepted device write is an observable event and leaves RAM alone.
theorem device_write_is_an_event :
    (match run sw (core 0x10015024 77) with
     | .ok _ _ evs => evs == [⟨0x10015024, 77⟩]
     | _ => false) = true := by decide +kernel

theorem illegal_float : isFault (.trap .illegal) (run 0x00b57553 (core 0 0)) = true := by decide +kernel
theorem illegal_zero_halfword : isFault (.trap .illegal) (run 0 (core 0 0)) = true := by decide +kernel
theorem illegal_compressed_float : isFault (.trap .illegal) (run 0x2000 (core 0 0)) = true := by decide +kernel
theorem ecall_traps : isFault (.trap .ecall) (run 0x00000073 (core 0 0)) = true := by decide +kernel
theorem ebreak_traps : isFault (.trap .ebreak) (run 0x00100073 (core 0 0)) = true := by decide +kernel
theorem c_ebreak_traps : isFault (.trap .ebreak) (run 0x9002 (core 0 0)) = true := by decide +kernel
-- csrr a2, misa: an unmodeled CSR is declined, not guessed.
theorem unmodeled_csr : unsupportedFault (run 0x30102673 (core 0 0)) = true := by decide +kernel
-- csrw mhartid, a1: writing a read-only CSR is architecturally illegal.
theorem read_only_csr_write : isFault (.trap .illegal) (run 0xf1459073 (core 0 0)) = true := by decide +kernel
-- csrw mstatus, a1 with MPRV (bit 17) set: outside the modeled fields.
theorem mstatus_field : unsupportedFault (run 0x30059073 (core 0 0x20000)) = true := by decide +kernel
-- csrw mtvec, a1 with mode 2: an unmodeled vector mode.
theorem mtvec_mode : unsupportedFault (run 0x30559073 (core 0 0x20010002)) = true := by decide +kernel
-- mret with MPP = U would enter user mode.
theorem mret_to_user : unsupportedFault (run 0x30200073 (core 0 0 (mpp := 0))) = true := by decide +kernel
-- SC with no reservation fails (rd = 1) and writes nothing.
theorem sc_without_reservation :
    okWith (fun c => c.get 12 == 1) (run scw (core 0x80000000 5)) = true := by decide +kernel
-- With one, the environment decides; here it chose success.
theorem sc_with_reservation :
    okWith (fun c => c.get 12 == 0 && !c.resv) (run scw (core 0x80000000 5 (resv := true))) = true := by
  decide +kernel
-- Fetch outside the image, and from an odd pc.
theorem fetch_outside : unsupportedFault (stepInstr B (img lw) ⟨{ core 0 0 with pc := 0x20020000 }, fun _ => 0⟩
    (fun _ => 0)) = true := by decide +kernel
theorem odd_pc : isFault (.trap .misalignedFetch) (stepInstr B (img lw)
    ⟨{ core 0 0 with pc := 0x20010001 }, fun _ => 0⟩ (fun _ => 0)) = true := by decide +kernel
-- jalr clears bit 0; a branch to an odd target cannot be encoded, but a
-- vectored trap base can produce one only if mtvec is odd, which csrw refuses.
theorem jalr_clears_bit0 :
    okWith (fun c => c.pc == 0x80000000) (run 0x000500e7 (core 0x80000001 0)) = true := by decide +kernel
-- No interrupt is enabled while MIE = 0, whatever mie says.
theorem no_irq_when_disabled :
    [3, 7, 11].all (fun k => !irqEnabled (core 0 0 (mieReg := 0x888)) k) = true := by decide +kernel
theorem irq_when_enabled : irqEnabled (core 0 0 (mie := true) (mieReg := 0x80)) 7 = true := by decide +kernel
theorem only_enabled_source : irqEnabled (core 0 0 (mie := true) (mieReg := 0x80)) 11 = false := by
  decide +kernel

end E5R.Controls
