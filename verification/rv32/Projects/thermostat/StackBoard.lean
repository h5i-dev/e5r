import Projects.thermostat.MainHeaderResetQuiet
import Projects.thermostat.UartPlatform
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.StackBoard
open E5R E5R.Thermostat

/-- A verification monitor: the same ROM and UART devices, with writable
    RAM restricted to the existing64KiB stack arena. This is not a new claim
    about hardware or a replacement execution model for the final theorem. -/
def board : Board := ⟨0x80ff0000,65536,UartPlatform.board.devices⟩

theorem available : Memory.Block board 0x80ff0000#32 65536 := by
  unfold Memory.Block
  change 0x80ff0000≤0x80ff0000 ∧ 0x81000000≤0x81000000 ∧ 0x81000000≤4294967296
  decide +kernel

theorem original_board : UartPlatform.board=QemuVirtRv32.board 0x80005f18 := by
  unfold UartPlatform.board
  rw [ThermostatImage.image_rwBase]

theorem included {a n} (inside : board.inRam a n=true) : UartPlatform.board.inRam a n=true := by
  rw [original_board,Board.inRam_iff]
  rw [Board.inRam_iff] at inside
  change 0x80ff0000≤a.toNat ∧ a.toNat+n≤0x81000000 at inside
  change 0x80005f18≤a.toNat ∧ a.toNat+n≤0x81000000
  omega

theorem broad_lower {a n} (inside : UartPlatform.board.inRam a n=true) : 0x80005f18≤a.toNat := by
  rw [original_board,Board.inRam_iff] at inside
  exact inside.1

theorem devices (a : Word) : board.device? a=UartPlatform.board.device? a := by
  unfold Board.device? board
  rfl

theorem rom_byte_none (a : Nat) (lower : 0x80005f18≤a) : romByte? img a false=none := by
  have first : (decide (0x80000000≤a) && decide (a<0x80000000+782))=false := by
    simp only [Bool.and_eq_false_iff,decide_eq_false_iff_not];omega
  have second : (decide (0x8000030e≤a) && decide (a<0x8000030e+21402))=false := by
    simp only [Bool.and_eq_false_iff,decide_eq_false_iff_not];omega
  have third : (decide (0x800056a8≤a) && decide (a<0x800056a8+2160))=false := by
    simp only [Bool.and_eq_false_iff,decide_eq_false_iff_not];omega
  unfold romByte?
  rw [PackedFetch.ro_eq]
  simp only [List.find?,List.length_append,PackedSlice.slice_length,List.length_replicate,Nat.add_zero,
    Bool.not_false,Bool.true_or,Bool.and_true,first,second,third]

theorem rom_none (a : Word) (w : Width) (lower : 0x80005f18≤a.toNat) : romRead? img a.toNat w.bytes false=none := by
  have h0 := rom_byte_none a.toNat lower
  have h1 := rom_byte_none (a.toNat+1) (by omega)
  have h2 := rom_byte_none (a.toNat+2) (by omega)
  have h3 := rom_byte_none (a.toNat+3) (by omega)
  cases w <;> simp only [Width.bytes,romRead?,romRead?.go,h0,h1,h2,h3,Nat.add_zero,Option.bind_none,Option.map_none]
  all_goals rfl

theorem device_none (a : Word) (lower : 0x80005f18≤a.toNat) : board.device? a=none := by
  have ne (n : Nat) (small : n<0x80005f18) : (n==a.toNat)=false := by
    simp only [beq_eq_false_iff_ne];omega
  simp only [Board.device?,board,UartPlatform.board,QemuVirtRv32.board,List.find?,ne 0x10000000 (by decide),
    ne 0x10000001 (by decide),ne 0x10000002 (by decide),ne 0x10000003 (by decide),
    ne 0x10000004 (by decide),ne 0x10000005 (by decide),ne 0x10000006 (by decide),ne 0x10000007 (by decide)]

/-- Existing generic instruction contracts already certify the entire reset
    prefix under the restricted RAM monitor, from arbitrary initial bytes. -/
theorem boot {c ram} (pc : c.pc=0x80000000#32) (mpp : c.mpp=0 ∨ c.mpp=3) :
    ∃ d after,Quiet.Steps board img 2550 ⟨c,ram⟩ ⟨d,after⟩ ∧ MainHeaderFirstPoll.Ready board d after :=
  MainHeaderResetQuiet.contract board c ram pc mpp available
end E5R.Thermostat.StackBoard
