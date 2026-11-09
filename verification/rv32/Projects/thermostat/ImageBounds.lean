import Projects.thermostat.ControlFetch
import Projects.thermostat.PackedFetch
set_option autoImplicit false
namespace E5R.Thermostat.ImageBounds
open E5R E5R.Thermostat

/-- A fetched executable byte belongs to one of this unchanged ELF's two
    contiguous RX segments, never its non-executable rodata or writable RAM. -/
theorem outside (a : Nat) (bad : a<0x80000000 ∨ 0x800056a8≤a) : romByte? img a true=none := by
  have first : (decide (0x80000000≤a) && decide (a<0x80000000+782))=false := by
    simp only [Bool.and_eq_false_iff,decide_eq_false_iff_not];omega
  have second : (decide (0x8000030e≤a) && decide (a<0x8000030e+21402))=false := by
    simp only [Bool.and_eq_false_iff,decide_eq_false_iff_not];omega
  unfold romByte?
  rw [PackedFetch.ro_eq]
  simp only [List.find?,List.length_append,PackedSlice.slice_length,List.length_replicate,Nat.add_zero,
    Bool.not_true,Bool.false_or,Bool.and_true,Bool.and_false,first,second]

theorem executable_byte {a b} (h : romByte? img a true=some b) : 0x80000000≤a ∧ a<0x800056a8 := by
  by_cases lower : 0x80000000≤a
  · by_cases upper : a<0x800056a8
    · exact ⟨lower,upper⟩
    · rw [outside a (Or.inr (by omega))] at h;cases h
  · rw [outside a (Or.inl (by omega))] at h;cases h

theorem decoded {B m} (safe : ¬Escapes B img m) :
    m.core.pc.getLsbD 0=false ∧ ∃ i len,fetchDecode img m.core.pc=some (i,len) := by
  cases step : stepInstr B img m (fun _ => 0#32) with
  | fault f => exact False.elim (safe (Or.inl ⟨(fun _ => 0#32),f,step⟩))
  | ok c ram evs =>
    obtain ⟨aligned,i,len,fetch,execute⟩ := Control.ok_decoded step
    exact ⟨aligned,i,len,fetch⟩

theorem code {B m} (safe : ¬Escapes B img m) :
    m.core.pc.getLsbD 0=false ∧ 0x80000000≤m.core.pc.toNat ∧ m.core.pc.toNat<0x800056a8 := by
  obtain ⟨aligned,i,len,decoded⟩ := decoded safe
  refine ⟨aligned,?_⟩
  unfold fetchDecode at decoded
  cases fetched : fetch img m.core.pc with
  | none => simp only [fetched] at decoded;cases decoded
  | some pair =>
    unfold fetch at fetched
    cases low : romRead? img m.core.pc.toNat 2 true with
    | none => simp only [low,Option.bind_eq_bind,Option.bind_none] at fetched;cases fetched
    | some bits =>
      obtain ⟨byte,inside,opcode⟩ := Control.read_opcode low
      exact executable_byte inside

end E5R.Thermostat.ImageBounds
