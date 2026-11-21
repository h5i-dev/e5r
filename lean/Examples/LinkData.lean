import NoCompiler.Relocate
import NoCompiler.Tactic

/-
A function that reads data, verified over every layout (decision 2026-11-21 (2)).

`get` is `auipc a0, %pcrel_hi(table); ld a0, %pcrel_lo(table)(a0); ret`: two
relocations (R_RISCV_PCREL_HI20, R_RISCV_PCREL_LO12_I) against the data symbol
`table`. Its specification at layout `L` names the table's address,
`L.addr "table"`: `get` returns the 64-bit word there. `get_verified :
Verified module "get" spec` holds for every layout the module can be linked
at. The proof steps the three patched words with the distance `d` symbolic:
`decode_auipc`/`decode_ld` decode them (`Reloc.toNat_patchU/I`), and
`Reloc.hi_lo` adds the two parts back to `d` (NoCompiler/Relocate.lean).
-/
namespace Examples.LinkData
open NoCompiler Module

/-- `auipc a0, 0`, patched with `d`. -/
theorem decode_auipc (d : Word) :
    decode (Reloc.patchU 0x00000517#32 d) = some (.auipc 10 (BitVec.ofNat 20 (((d + 0x800#64) >>> 12).toNat))) := by
  have ht := Reloc.toNat_patchU 0x00000517#32 d (by decide)
  have h0 : bits (Reloc.patchU 0x00000517#32 d) 0 7 = 0x17 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have h7 : bits (Reloc.patchU 0x00000517#32 d) 7 5 = 10 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have hu : immU (Reloc.patchU 0x00000517#32 d) = BitVec.ofNat 20 (((d + 0x800#64) >>> 12).toNat) := by
    unfold immU; simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  unfold decode
  simp only [h0, regAt, h7, hu]
  rfl

/-- `ld a0, 0(a0)`, patched with `d`. -/
theorem decode_ld (d : Word) :
    decode (Reloc.patchI 0x00053503#32 d) = some (.load .ld 10 10 (BitVec.ofNat 12 (d.toNat % 4096))) := by
  have ht := Reloc.toNat_patchI 0x00053503#32 d (by decide)
  have h0 : bits (Reloc.patchI 0x00053503#32 d) 0 7 = 0x03 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have h7 : bits (Reloc.patchI 0x00053503#32 d) 7 5 = 10 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have h12 : bits (Reloc.patchI 0x00053503#32 d) 12 3 = 3 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have h15 : bits (Reloc.patchI 0x00053503#32 d) 15 5 = 10 := by simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; omega
  have hi : immI (Reloc.patchI 0x00053503#32 d) = BitVec.ofNat 12 (d.toNat % 4096) := by
    unfold immI; simp only [bits, ht, Nat.shiftRight_eq_div_pow, BitVec.toNat_ofNat]; apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  unfold decode
  simp only [h0, regAt, h7, h12, h15, hi]
  rfl



/-- `get`: `auipc a0, %pcrel_hi(table); ld a0, %pcrel_lo(table)(a0); ret`. -/
def getF : RFunc where
  name := "get"
  words := [0x00000517#32, 0x00053503#32, 0x00008067#32]
  relocs := [⟨0, .pcrelHi, "table", 0, 0⟩, ⟨4, .pcrelLoI, "table", 0, 0⟩]

def module : Module where
  funcs := [getF]
  data := [⟨"table", [42, 0, 0, 0, 0, 0, 0, 0], false⟩]

/-- At layout `L`: `get` returns the word at `table`, wherever the layout put it. -/
def spec (L : Layout) : Spec Unit where
  pre := fun _ _ => aligned (L.addr "table") 8
  post := fun _ s t => t.reg 10 = loadVal .ld s.mem (L.addr "table")
  reads := fun _ _ => [⟨L.addr "table", 8⟩]

theorem getF_mem : getF ∈ module.funcs := by simp [module]

theorem patched (L : Layout) : getF.patched L =
    [Reloc.patchU 0x00000517#32 (L.addr "table" + BitVec.ofInt 64 0 - (L.addr "get" + BitVec.ofNat 64 0)),
     Reloc.patchI 0x00053503#32 (L.addr "table" + BitVec.ofInt 64 0 - (L.addr "get" + BitVec.ofNat 64 0)),
     0x00008067#32] := rfl

theorem get_verified : Verified module "get" spec := by
  intro L hL
  have hd : module.dom L "get" = [getF.region L] := Module.dom_leaf hL getF_mem rfl
  rw [hd]
  generalize hdd : L.addr "table" + BitVec.ofInt 64 0 - (L.addr "get" + BitVec.ofNat 64 0) = d
  have hrange : (Reloc.mk 0 .pcrelHi "table" 0 0).InRange L getF.name :=
    (hL.relocs getF getF_mem _ (by simp [getF])).1
  have hr1 : -(2 : Int) ^ 31 - 2 ^ 11 ≤ d.toInt ∧ d.toInt < 2 ^ 31 - 2 ^ 11 := by
    simpa [Reloc.InRange, Reloc.dist, getF, ← hdd] using hrange
  have hpat := patched L
  rw [hdd] at hpat
  have hi : ∀ i (h : i < 3), (module.link L).instr (L.addr "get" + BitVec.ofNat 64 (4 * i)) =
      ((getF.patched L).getD i 0 |> decode) := by
    intro i h
    unfold Code.instr
    rw [show L.addr "get" = L.addr getF.name from rfl, Module.fetch_link hL getF_mem (by simp [getF]; omega)]
    rfl
  have he0 : d + L.addr "get" = L.addr "table" := by rw [← hdd]; bv_omega
  intro a s he hpre
  have hpc : s.pc = L.addr "get" := he.pc
  have hdom : ∀ i, i < 3 → Dom.mem [getF.region L] (L.addr "get" + BitVec.ofNat 64 (4 * i)) := by
    intro i h
    simp only [Dom.mem, RFunc.region, getF, List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq,
      List.length_cons, List.length_nil]
    rw [show L.addr "get" + BitVec.ofNat 64 (4 * i) - L.addr "get" = BitVec.ofNat 64 (4 * i) by bv_omega,
      BitVec.toNat_ofNat]
    omega
  -- 1. auipc a0, hi
  have i0 := hi 0 (by decide)
  rw [hpat] at i0
  simp only [List.getD_cons_zero, decode_auipc] at i0
  refine Reach.exec_step (i := .auipc 10 (BitVec.ofNat 20 (((d + 0x800#64) >>> 12).toNat)))
    (by rw [hpc]; simpa using hdom 0 (by decide)) he.live (by rw [hpc]; simpa using i0) trivial ?_
  simp only [exec, Reach.opt_some]
  -- 2. ld a0, lo(a0): its address is the table, wherever the layout put it.
  have hea : s.pc + ((BitVec.ofNat 20 (((d + 0x800#64) >>> 12).toNat)).setWidth 32 <<< 12).signExtend 64 +
      (BitVec.ofNat 12 (d.toNat % 4096)).signExtend 64 = L.addr "table" := by
    rw [BitVec.add_assoc, Reloc.hi_lo d hr1.1 hr1.2, hpc, BitVec.add_comm, he0]
  have i1 := hi 1 (by decide)
  rw [hpat] at i1
  simp only [List.getD_cons_succ, List.getD_cons_zero, decode_ld] at i1
  refine Reach.exec_step (i := .load .ld 10 10 (BitVec.ofNat 12 (d.toNat % 4096)))
    (by simp only [State.setPc_pc, hpc]; simpa using hdom 1 (by decide))
    (by simp [he.live]) (by simp only [State.setPc_pc, hpc]; simpa using i1) ?_ ?_
  · show Perm.canRead _ _ _
    simp only [ea, State.setPc_reg, State.reg_setReg_same _ _ _ (by decide : (10 : Reg) ≠ 0), hea]
    refine .inr ⟨⟨L.addr "table", 8⟩, by simp [Spec.perm, spec], ?_⟩
    simp [Region.covers, LdOp.width]
  have hal : aligned (L.addr "table") 8 := hpre
  simp only [exec, ea, State.setPc_reg, State.reg_setReg_same _ _ _ (by decide : (10 : Reg) ≠ 0), hea,
    LdOp.width]
  simp only [hal, ↓reduceIte, Reach.opt_some]
  -- 3. ret
  have i2 := hi 2 (by decide)
  rw [hpat] at i2
  simp only [List.getD_cons_succ, List.getD_cons_zero] at i2
  have hret : decode 0x00008067#32 = some (.jalr 0 1 0) := by decide
  rw [hret] at i2
  refine Reach.exec_step (i := .jalr 0 1 0)
    (by simp only [State.setPc_pc, hpc]; simpa [BitVec.add_assoc] using hdom 2 (by decide))
    (by simp [he.live]) (by simp only [State.setPc_pc, hpc]; simpa [BitVec.add_assoc] using i2)
    trivial ?_
  have hra : aligned (s.reg 1) 4 := he.retAligned
  have h01 : (1 : Reg) ≠ 10 := by decide
  have hz : BitVec.signExtend 64 (0 : BitVec 12) = 0 := by decide
  have h0 : ∀ t : State, ∀ v, t.setReg 0 v = t := fun t v => by simp [State.setReg]
  have ht : s.reg 1 + 0 &&& ~~~1 = s.reg 1 := by
    rw [show s.reg 1 + (0 : Word) = s.reg 1 by bv_omega]; exact and_not_one_of_aligned hra
  simp only [exec, State.reg_setReg_other _ _ _ _ h01, State.setPc_reg, hz, h0]
  simp only [ht, jumpTo, hra, ↓reduceIte, Reach.opt_some]
  refine .done ⟨.inl (by simpa using he.ret), .inl ⟨by simp [he.live], by simp, ?_, ?_⟩⟩
  · intro r hr
    have h10 : r ≠ 10 := by
      intro h; subst h; revert hr; decide
    simp [State.reg_setReg_other _ _ _ _ h10]
  · show _ = loadVal .ld s.mem (L.addr "table")
    simp [State.reg_setReg_same _ _ _ (by decide : (10 : Reg) ≠ 0)]

/-! ## Control -/

/-- Without the low-part relocation the load misses the table: at a layout with
    `get` at 0x1000 and `table` at 0x2010 (distance 0x1010), `auipc` alone
    gives 0x2000. -/
example : (0x1000#64 : Word) + ((BitVec.ofNat 20 (((0x1010#64 + 0x800#64) >>> 12).toNat)).setWidth 32
    <<< 12).signExtend 64 + (BitVec.ofNat 12 0).signExtend 64 ≠ 0x2010#64 := by decide

/-- With it, the same layout gives the table. -/
example : (0x1000#64 : Word) + ((BitVec.ofNat 20 (((0x1010#64 + 0x800#64) >>> 12).toNat)).setWidth 32
    <<< 12).signExtend 64 + (BitVec.ofNat 12 ((0x1010#64 : Word).toNat % 4096)).signExtend 64 = 0x2010#64 := by
  decide

end Examples.LinkData
