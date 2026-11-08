/-
  Faster evaluation of the SAME fetched image, by proved packed-file equations.
  Generic slice/fetch proof pattern: Projects/rmk/Fetch.lean, original e5r,
  Apache-2.0. This module binds that pattern to the thermostat's own ELF.
-/
import Projects.thermostat.Proof
import Projects.thermostat.PackedSlice
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.PackedFetch
open E5R E5R.RamElf E5R.Thermostat.PackedSlice
abbrev elf := ThermostatImage.elf

/-- Only the reader's header parse is evaluated here; segment bytes stay packed. -/
def roShape : Bool :=
  match check 0x80000000 0x1000000 elf with
  | .ok (_,ls,_) => (ls.filter (!·.write)).map (fun l => (l.vaddr,l.off,l.filesz,l.memsz,l.exec)) ==
      [(0x80000000,4096,782,782,true), (0x8000030e,4878,21402,21402,true),
       (0x800056a8,26280,2160,2160,false)]
  | .error _ => false

theorem roShape_ok : roShape = true := by decide +kernel

theorem ro_eq : img = [⟨0x80000000,elf.slice 4096 782 ++ List.replicate 0 0,true⟩,
    ⟨0x8000030e,elf.slice 4878 21402 ++ List.replicate 0 0,true⟩,
    ⟨0x800056a8,elf.slice 26280 2160 ++ List.replicate 0 0,false⟩] := by
  have h := roShape_ok
  unfold roShape at h
  show (imageOf 0x80000000 0x1000000 elf).ro = _
  unfold imageOf
  split at h
  · rename_i e ls r hc
    rw [hc]
    simp only
    generalize ls.filter (!·.write) = ro at h ⊢
    have h' := beq_iff_eq.mp h
    rcases ro with _ | ⟨l0, _ | ⟨l1, _ | ⟨l2, _ | ⟨l3,rest⟩⟩⟩⟩
    · simp at h'
    · simp at h'
    · simp at h'
    · simp only [List.map_cons,List.map_nil,List.cons.injEq,Prod.mk.injEq,and_true] at h'
      obtain ⟨⟨a0,o0,f0,m0,x0⟩,⟨a1,o1,f1,m1,x1⟩,a2,o2,f2,m2,x2⟩ := h'
      simp [a0,o0,f0,m0,x0,a1,o1,f1,m1,x1,a2,o2,f2,m2,x2]
    · simp at h'
  · cases h

/-- The two executable segments are contiguous in virtual and file addresses. -/
def textByte (a : Nat) : Nat := rawByte elf.words (4096+(a-0x80000000))

theorem romByte_text (a : Nat) (hlo : 0x80000000 ≤ a) (hhi : a < 0x800056a8) :
    romByte? img a true = some (textByte a) := by
  unfold romByte?
  rw [ro_eq]
  have hlen0 : (elf.slice 4096 782 ++ List.replicate 0 0).length = 782 := by simp [slice_length]
  have hlen1 : (elf.slice 4878 21402 ++ List.replicate 0 0).length = 21402 := by simp [slice_length]
  simp only [List.find?,hlen0,hlen1]
  by_cases hfirst : a < 0x8000030e
  · have hp : (0x80000000 ≤ a && decide (a < 0x80000000+782) && (!true || true)) = true := by
      simp [hlo,hfirst]
    rw [hp]
    simp only [Segment.byte?,hlo,ite_true]
    rw [List.getElem?_append_left (by rw [slice_length];omega),slice_get _ _ _ _ (by omega)]
    rfl
  · have hp : (0x80000000 ≤ a && decide (a < 0x80000000+782) && (!true || true)) = false := by
      simp [hlo,hfirst]
    have hlo1 : 0x8000030e ≤ a := by omega
    have hp1 : (0x8000030e ≤ a && decide (a < 0x8000030e+21402) && (!true || true)) = true := by
      simp [hlo1,hhi]
    rw [hp,hp1]
    simp only [Segment.byte?,hlo1,ite_true,ite_false]
    rw [List.getElem?_append_left (by rw [slice_length];omega),slice_get _ _ _ _ (by omega)]
    unfold textByte
    rw [show 4878+(a-0x8000030e) = 4096+(a-0x80000000) by omega]

/-- Little-endian read over an abstract byte source, with no ROM-list expansion. -/
def rd (byte : Nat → Nat) (a : Nat) : Nat → Nat
  | 0 => 0
  | k+1 => rd byte a k+byte (a+k)*256^k

theorem romRead_go {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x true = some (byte x)) (a : Nat) :
    ∀ n, lo ≤ a → a+n ≤ hi → romRead?.go img a true n = some (rd byte a n)
  | 0,_,_ => rfl
  | n+1,h1,h2 => by
    simp only [romRead?.go]
    rw [hb (a+n) (by omega) (by omega),romRead_go hb a n h1 (by omega)]
    rfl

def fetchT (byte : Nat → Nat) (pc : Word) : Option (Word × Word) :=
  let lo := BitVec.ofNat 32 (rd byte pc.toNat 2)
  if lo &&& 3 ≠ 3 then some (lo,2)
  else some ((BitVec.ofNat 32 (rd byte (pc.toNat+2) 2) <<< 16) ||| lo,4)

theorem fetch_eq {byte : Nat → Nat} {lo hi : Nat}
    (hb : ∀ x, lo ≤ x → x < hi → romByte? img x true = some (byte x))
    (pc : Word) (h1 : lo ≤ pc.toNat) (h2 : pc.toNat+4 ≤ hi) :
    fetch img pc = fetchT byte pc := by
  unfold fetch fetchT romRead?
  rw [romRead_go hb _ 2 h1 (by omega),romRead_go hb _ 2 (by omega) (by omega)]
  rfl

theorem fetch_text (pc : Word) (h1 : 0x80000000 ≤ pc.toNat) (h2 : pc.toNat+4 ≤ 0x800056a8) :
    fetch img pc = fetchT textByte pc :=
  fetch_eq (fun x a b => romByte_text x a b) pc h1 h2

theorem fetchDecode_of (pc : Word) (h1 : 0x80000000 ≤ pc.toNat) (h2 : pc.toNat+4 ≤ 0x800056a8)
    {bits len : Word} {i : Instr} (hf : fetchT textByte pc = some (bits,len))
    (hd : decode bits len = some i) : fetchDecode img pc = some (i,len) := by
  unfold fetchDecode
  rw [fetch_text pc h1 h2,hf]
  simp [hd]
end E5R.Thermostat.PackedFetch
