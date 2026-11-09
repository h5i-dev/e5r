import Projects.thermostat.StackBoard
import Projects.thermostat.ReadBytes
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.StackAccess
open E5R E5R.Thermostat
abbrev narrow := StackBoard.board
abbrev broad := UartPlatform.board

theorem outside {a width} (h : broad.inRam a width=false) : narrow.inRam a width=false := by
  cases e : narrow.inRam a width with
  | false => rfl
  | true => exact False.elim (Bool.noConfusion (h.symm.trans (StackBoard.included e)))

theorem block {p n} (h : Memory.Block narrow p n) : Memory.Block broad p n := by
  change Memory.Block UartPlatform.board p n
  rw [StackBoard.original_board]
  change 0x80005f18≤p.toNat ∧ p.toNat+n≤0x81000000 ∧ p.toNat+n≤2^32
  change 0x80ff0000≤p.toNat ∧ p.toNat+n≤0x81000000 ∧ p.toNat+n≤2^32 at h
  omega

theorem span {ram p xs} (h : Bytes.Span narrow ram p xs) : Bytes.Span broad ram p xs :=
  ⟨h.length,h.nowrap,fun i => StackBoard.included (h.memory i),h.bytes⟩

theorem rom_byte {image ram a v} (h : ReadBytes.Byte broad image ram a v)
    (ro : broad.inRam a 1=false) : ReadBytes.Byte narrow image ram a v := by
  cases h with
  | ram hi value => exact False.elim (Bool.noConfusion (ro.symm.trans hi))
  | rom _ value => exact .rom (outside ro) value

theorem rom_span {image ram p xs} (h : ReadBytes.Span broad image ram p xs)
    (ro : ∀ i : Fin xs.length,broad.inRam (p+BitVec.ofNat 32 i.val) 1=false) : ReadBytes.Span narrow image ram p xs :=
  ⟨h.length,h.nowrap,fun i => rom_byte (h.bytes i) (ro i)⟩
end E5R.Thermostat.StackAccess
