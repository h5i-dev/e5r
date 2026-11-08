import Projects.thermostat.RomSpan
import Projects.thermostat.UartPlatform
import Projects.thermostat.WordRegions
import Projects.thermostat.ResponseHeadSpec
namespace E5R.Thermostat.ResponseHeadLiterals
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def pointer : Fin 4 → Word
  | 0 => 0x80005d19#32
  | 1 => 0x80005d0b#32
  | 2 => 0x800056b8#32
  | 3 => 0x80005d1b#32

def bytes : Fin 4 → List (BitVec 8)
  | 0 => WireSpec.ascii "\r\n"
  | 1 => WireSpec.ascii "Content-Type: "
  | 2 => WireSpec.ascii "Content-Length: "
  | 3 => WireSpec.ascii "Connection: close\r\n"

theorem outside (k : Fin 4) : ∀ i : Fin (bytes k).length, B.inRam (pointer k+BitVec.ofNat 32 i.val) 1=false := by
  have h : ∀ k : Fin 4, ∀ i : Fin (bytes k).length, B.inRam (pointer k+BitVec.ofNat 32 i.val) 1=false := by decide +kernel
  exact h k

theorem span (ram : Word → BitVec 8) (k : Fin 4) : ReadBytes.Span B img ram (pointer k) (bytes k) := by
  refine ReadBytes.of_data _ _ _ _ ?_ ?_ ?_ (outside k) ?_
  · have h : ∀ k : Fin 4, (bytes k).length<2^32 := by decide +kernel
    exact h k
  · have h : ∀ k : Fin 4, (pointer k).toNat+(bytes k).length≤2^32 := by decide +kernel
    exact h k
  · have h : ∀ k : Fin 4, ∀ i : Fin (bytes k).length, 0x800056a8≤(pointer k+BitVec.ofNat 32 i.val).toNat ∧ (pointer k+BitVec.ofNat 32 i.val).toNat<0x80005f18 := by decide +kernel
    exact h k
  · have h : ∀ k : Fin 4, ∀ i : Fin (bytes k).length, BitVec.ofNat 32 (PackedData.dataByte (pointer k+BitVec.ofNat 32 i.val).toNat)=BitVec.ofNat 32 (bytes k)[i.val].toNat := by decide +kernel
    exact h k

theorem disjoint (dst : Word) (cap : Nat) (hm : Memory.Block B dst cap) (k : Fin 4) :
    WordRegions.Disjoint (pointer k) (bytes k).length dst cap := by
  intro i j he
  have hd := Memory.block_access hm (off := j.val) (width := 1) (by decide) (by have := j.isLt;omega)
  rw [←he,outside k i] at hd
  contradiction
end E5R.Thermostat.ResponseHeadLiterals
