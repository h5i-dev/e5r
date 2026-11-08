import Projects.thermostat.ControlBytes
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.Control
open E5R

theorem opcode_join (lo hi : Word) : bits ((hi <<< 16) ||| lo) 0 7 = bits lo 0 7 := by
  unfold bits
  rw [BitVec.extractLsb'_or]
  have hz : (hi <<< 16).extractLsb' 0 7 = 0#7 := by
    apply BitVec.eq_of_getLsbD_eq
    intro k
    simp [BitVec.getLsbD_extractLsb',BitVec.getLsbD_shiftLeft]
    omega
  rw [hz,BitVec.zero_or]

theorem read_opcode {img : List Segment} {a : Nat} {lo : Word}
    (h : romRead? img a 2 true = some lo) :
    ∃ b, romByte? img a true = some b ∧ bits lo 0 7 = b%128 := by
  cases h1 : romByte? img (a+1) true with
  | none => simp [romRead?,romRead?.go,h1] at h
  | some b1 =>
    cases h0 : romByte? img a true with
    | none => simp [romRead?,romRead?.go,h1,h0] at h
    | some b0 =>
      simp [romRead?,romRead?.go,h1,h0] at h
      subst lo
      refine ⟨b0,rfl,?_⟩
      simp [bits,BitVec.extractLsb',BitVec.toNat_ofNat]
      omega

/-- Any decoded CSR or MRET must start at an exhaustively listed byte site.
    No instruction-boundary assumption beyond alignment is used. -/
theorem system_site {img : List Segment} {pc : Word} {i : Instr} {len : Word}
    (ha : pc.toNat%2 = 0) (hd : fetchDecode img pc = some (i,len))
    (hi : IsSystem i = true) : pc.toNat ∈ systemSites img := by
  unfold fetchDecode at hd
  cases hf : fetch img pc with
  | none => simp [hf] at hd
  | some pair =>
    obtain ⟨w,l⟩ := pair
    simp only [hf] at hd
    cases hdec : decode w l with
    | none => simp [hdec] at hd
    | some ins =>
      simp only [hdec,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hd
      obtain ⟨rfl,rfl⟩ := hd
      unfold fetch at hf
      cases hr : romRead? img pc.toNat 2 true with
      | none => simp [hr] at hf
      | some lo =>
        rw [hr] at hf
        simp only [Option.bind_eq_bind,Option.bind_some,Option.pure_def] at hf
        split at hf
        · simp only [Option.some.injEq,Prod.mk.injEq] at hf
          obtain ⟨rfl,rfl⟩ := hf
          have hh := compressed _ ins (by simpa [decode] using hdec)
          rw [hi] at hh
          contradiction
        · cases hhi : romRead? img (pc.toNat+2) 2 true with
          | none => simp [hhi] at hf
          | some upper =>
            simp only [hhi,Option.bind_some,Option.some.injEq,Prod.mk.injEq] at hf
            obtain ⟨rfl,rfl⟩ := hf
            have h32 : decode32 ((upper <<< 16) ||| lo) = some ins := by simpa [decode] using hdec
            have hop : bits ((upper <<< 16) ||| lo) 0 7 = 0x73 := by
              by_cases hn : bits ((upper <<< 16) ||| lo) 0 7 = 0x73
              · exact hn
              · have hh := non_system_opcode _ ins h32 hn
                rw [hi] at hh
                contradiction
            obtain ⟨b,hb,hopb⟩ := read_opcode hr
            apply rom_system_site hb _ ha
            rw [opcode_join] at hop
            omega

theorem ok_decoded {B img m o c r evs} (h : stepInstr B img m o = .ok c r evs) :
    m.core.pc.getLsbD 0 = false ∧ ∃ i len, fetchDecode img m.core.pc = some (i,len) ∧
      interp B img o (exec m.core len i) m.ram 0 [] = .ok c r evs := by
  cases ha : m.core.pc.getLsbD 0 with
  | true =>
    simp only [stepInstr,ha,ite_true] at h
    contradiction
  | false =>
    cases hf : fetch img m.core.pc with
    | none =>
      simp only [stepInstr,ha,Bool.false_eq_true,ite_false,hf] at h
      contradiction
    | some pair =>
      obtain ⟨bits,len⟩ := pair
      cases hd : decode bits len with
      | none =>
        simp only [stepInstr,ha,Bool.false_eq_true,ite_false,hf,hd] at h
        contradiction
      | some i =>
        exact ⟨rfl,i,len,by simp [fetchDecode,hf,hd],by simpa only [stepInstr,ha,Bool.false_eq_true,ite_false,hf,hd] using h⟩
end E5R.Thermostat.Control
