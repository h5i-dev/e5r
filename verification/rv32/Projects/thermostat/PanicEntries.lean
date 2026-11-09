import Projects.thermostat.PanicLoop
import Projects.thermostat.EffectCoreProperty
set_option autoImplicit false
set_option maxRecDepth 3000
namespace E5R.Thermostat.PanicEntries
open E5R E5R.Thermostat EffectCoreProperty
theorem fetch80004b34 : fetchDecode img 0x80004b34#32=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001101#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b36 : fetchDecode img 0x80004b36#32=some (.store .w 2 1 0x0000001c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000ce06#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b38 : fetchDecode img 0x80004b38#32=some (.store .w 2 8 0x00000018#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000cc22#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b3a : fetchDecode img 0x80004b3a#32=some (.opimm .add 8 2 0x00000020#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001000#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b3c : fetchDecode img 0x80004b3c#32=some (.op .add 12 0 10,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000862a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b3e : fetchDecode img 0x80004b3e#32=some (.opimm .add 10 2 0x00000017#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x01710513#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b42 : fetchDecode img 0x80004b42#32=some (.lui 11 0x80005000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x800055b7#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b46 : fetchDecode img 0x80004b46#32=some (.opimm .add 11 11 0x0000014e#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x14e58593#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b4a : fetchDecode img 0x80004b4a#32=some (.store .w 2 10 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c62a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b4c : fetchDecode img 0x80004b4c#32=some (.store .w 2 11 0x00000010#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c82e#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b4e : fetchDecode img 0x80004b4e#32=some (.lui 10 0x80006000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x80006537#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b52 : fetchDecode img 0x80004b52#32=some (.opimm .add 10 10 0xfffff818#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x81850513#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b56 : fetchDecode img 0x80004b56#32=some (.opimm .add 11 2 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000006c#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b58 : fetchDecode img 0x80004b58#32=some (.auipc 1 0x00000000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000097#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b5c : fetchDecode img 0x80004b5c#32=some (.jalr 1 1 0x0000003a#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x03a080e7#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b60 : fetchDecode img 0x80004b60#32=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001101#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b62 : fetchDecode img 0x80004b62#32=some (.store .w 2 1 0x0000001c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000ce06#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b64 : fetchDecode img 0x80004b64#32=some (.store .w 2 8 0x00000018#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000cc22#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b66 : fetchDecode img 0x80004b66#32=some (.opimm .add 8 2 0x00000020#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001000#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b68 : fetchDecode img 0x80004b68#32=some (.store .w 2 11 0x00000004#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c22e#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b6a : fetchDecode img 0x80004b6a#32=some (.store .w 2 10 0x00000000#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c02a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b6c : fetchDecode img 0x80004b6c#32=some (.opimm .add 10 2 0x00000004#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000048#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b6e : fetchDecode img 0x80004b6e#32=some (.lui 11 0x80005000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x800055b7#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b72 : fetchDecode img 0x80004b72#32=some (.opimm .add 11 11 0xffffffa4#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0xfa458593#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b76 : fetchDecode img 0x80004b76#32=some (.op .add 13 0 2,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000868a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b78 : fetchDecode img 0x80004b78#32=some (.store .w 2 10 0x00000008#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c42a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b7a : fetchDecode img 0x80004b7a#32=some (.store .w 2 11 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c62e#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b7c : fetchDecode img 0x80004b7c#32=some (.store .w 2 13 0x00000010#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c836#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b7e : fetchDecode img 0x80004b7e#32=some (.store .w 2 11 0x00000014#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000ca2e#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b80 : fetchDecode img 0x80004b80#32=some (.lui 10 0x80006000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x80006537#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b84 : fetchDecode img 0x80004b84#32=some (.opimm .add 10 10 0xfffff842#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x84250513#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b88 : fetchDecode img 0x80004b88#32=some (.opimm .add 11 2 0x00000008#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000002c#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b8a : fetchDecode img 0x80004b8a#32=some (.auipc 1 0x00000000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000097#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b8e : fetchDecode img 0x80004b8e#32=some (.jalr 1 1 0x00000008#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x008080e7#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b92 : fetchDecode img 0x80004b92#32=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001101#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b94 : fetchDecode img 0x80004b94#32=some (.store .w 2 1 0x0000001c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000ce06#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b96 : fetchDecode img 0x80004b96#32=some (.store .w 2 8 0x00000018#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000cc22#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b98 : fetchDecode img 0x80004b98#32=some (.opimm .add 8 2 0x00000020#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001000#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b9a : fetchDecode img 0x80004b9a#32=some (.store .w 2 11 0x00000008#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c42e#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b9c : fetchDecode img 0x80004b9c#32=some (.store .w 2 10 0x00000004#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c22a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004b9e : fetchDecode img 0x80004b9e#32=some (.opimm .add 10 2 0x00000004#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000048#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004ba0 : fetchDecode img 0x80004ba0#32=some (.opimm .add 11 0 0x00000001#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00004585#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004ba2 : fetchDecode img 0x80004ba2#32=some (.store .w 2 10 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c62a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004ba4 : fetchDecode img 0x80004ba4#32=some (.store .w 2 12 0x00000010#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c832#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004ba6 : fetchDecode img 0x80004ba6#32=some (.store .h 2 11 0x00000014#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00b11a23#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004baa : fetchDecode img 0x80004baa#32=some (.opimm .add 10 2 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000068#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004bac : fetchDecode img 0x80004bac#32=some (.auipc 1 0xffffc000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0xffffc097#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004bb0 : fetchDecode img 0x80004bb0#32=some (.jalr 1 1 0xfffffcb0#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0xcb0080e7#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004de2 : fetchDecode img 0x80004de2#32=some (.opimm .add 2 2 0xfffffff0#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00001141#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004de4 : fetchDecode img 0x80004de4#32=some (.store .w 2 1 0x0000000c#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c606#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004de6 : fetchDecode img 0x80004de6#32=some (.store .w 2 8 0x00000008#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000c422#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004de8 : fetchDecode img 0x80004de8#32=some (.opimm .add 8 2 0x00000010#32,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000800#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004dea : fetchDecode img 0x80004dea#32=some (.op .add 12 0 10,2#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x0000862a#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004dec : fetchDecode img 0x80004dec#32=some (.lui 10 0x80006000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x80006537#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004df0 : fetchDecode img 0x80004df0#32=some (.opimm .add 10 10 0xfffffed8#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0xed850513#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004df4 : fetchDecode img 0x80004df4#32=some (.opimm .add 11 0 0x00000047#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x04700593#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004df8 : fetchDecode img 0x80004df8#32=some (.auipc 1 0x00000000#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0x00000097#32) (by decide +kernel) (by decide +kernel)
theorem fetch80004dfc : fetchDecode img 0x80004dfc#32=some (.jalr 1 1 0xfffffd9a#32,4#32) := by
  exact PackedFetch.fetchDecode_of _ (by decide) (by decide) (bits := 0xd9a080e7#32) (by decide +kernel) (by decide +kernel)

def simple : List Word := [0x80004b34#32,0x80004b36#32,0x80004b38#32,0x80004b3a#32,0x80004b3c#32,0x80004b3e#32,0x80004b42#32,0x80004b46#32,0x80004b4a#32,0x80004b4c#32,0x80004b4e#32,0x80004b52#32,0x80004b56#32,0x80004b58#32,0x80004b60#32,0x80004b62#32,0x80004b64#32,0x80004b66#32,0x80004b68#32,0x80004b6a#32,0x80004b6c#32,0x80004b6e#32,0x80004b72#32,0x80004b76#32,0x80004b78#32,0x80004b7a#32,0x80004b7c#32,0x80004b7e#32,0x80004b80#32,0x80004b84#32,0x80004b88#32,0x80004b8a#32,0x80004b92#32,0x80004b94#32,0x80004b96#32,0x80004b98#32,0x80004b9a#32,0x80004b9c#32,0x80004b9e#32,0x80004ba0#32,0x80004ba2#32,0x80004ba4#32,0x80004ba6#32,0x80004baa#32,0x80004bac#32,0x80004de2#32,0x80004de4#32,0x80004de6#32,0x80004de8#32,0x80004dea#32,0x80004dec#32,0x80004df0#32,0x80004df4#32,0x80004df8#32]
def At (c : Core) : Prop := PanicLoop.At c ∨ c.pc∈simple ∨
  (c.pc=0x80004b5c#32 ∧ c.get 1=0x80004b58#32) ∨
  (c.pc=0x80004b8e#32 ∧ c.get 1=0x80004b8a#32) ∨
  (c.pc=0x80004bb0#32 ∧ c.get 1=0x80000bac#32) ∨
  (c.pc=0x80004dfc#32 ∧ c.get 1=0x80004df8#32)

/-- Every successful real panic-routine instruction remains in its
    nonreturning region. RAM failure is not assumed away by this theorem. -/
theorem instr {B c ram o d after evs} (h : At c) (actual : stepInstr B img ⟨c,ram⟩ o=.ok d after evs) : At d := by
  rcases h with loop|inside|⟨pc,ra⟩|⟨pc,ra⟩|⟨pc,ra⟩|⟨pc,ra⟩
  · obtain ⟨e,step,post⟩ := PanicLoop.next (B := B) (ram := ram) loop
    rw [step.det o] at actual
    cases actual
    exact Or.inl post
  · have pcs : c.pc=0x80004b34#32 ∨ c.pc=0x80004b36#32 ∨ c.pc=0x80004b38#32 ∨ c.pc=0x80004b3a#32 ∨ c.pc=0x80004b3c#32 ∨ c.pc=0x80004b3e#32 ∨ c.pc=0x80004b42#32 ∨ c.pc=0x80004b46#32 ∨ c.pc=0x80004b4a#32 ∨ c.pc=0x80004b4c#32 ∨ c.pc=0x80004b4e#32 ∨ c.pc=0x80004b52#32 ∨ c.pc=0x80004b56#32 ∨ c.pc=0x80004b58#32 ∨ c.pc=0x80004b60#32 ∨ c.pc=0x80004b62#32 ∨ c.pc=0x80004b64#32 ∨ c.pc=0x80004b66#32 ∨ c.pc=0x80004b68#32 ∨ c.pc=0x80004b6a#32 ∨ c.pc=0x80004b6c#32 ∨ c.pc=0x80004b6e#32 ∨ c.pc=0x80004b72#32 ∨ c.pc=0x80004b76#32 ∨ c.pc=0x80004b78#32 ∨ c.pc=0x80004b7a#32 ∨ c.pc=0x80004b7c#32 ∨ c.pc=0x80004b7e#32 ∨ c.pc=0x80004b80#32 ∨ c.pc=0x80004b84#32 ∨ c.pc=0x80004b88#32 ∨ c.pc=0x80004b8a#32 ∨ c.pc=0x80004b92#32 ∨ c.pc=0x80004b94#32 ∨ c.pc=0x80004b96#32 ∨ c.pc=0x80004b98#32 ∨ c.pc=0x80004b9a#32 ∨ c.pc=0x80004b9c#32 ∨ c.pc=0x80004b9e#32 ∨ c.pc=0x80004ba0#32 ∨ c.pc=0x80004ba2#32 ∨ c.pc=0x80004ba4#32 ∨ c.pc=0x80004ba6#32 ∨ c.pc=0x80004baa#32 ∨ c.pc=0x80004bac#32 ∨ c.pc=0x80004de2#32 ∨ c.pc=0x80004de4#32 ∨ c.pc=0x80004de6#32 ∨ c.pc=0x80004de8#32 ∨ c.pc=0x80004dea#32 ∨ c.pc=0x80004dec#32 ∨ c.pc=0x80004df0#32 ∨ c.pc=0x80004df4#32 ∨ c.pc=0x80004df8#32 := by
      simpa only [simple,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using inside
    rcases pcs with pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc|pc
    · have decoded : fetchDecode img c.pc=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by rw [pc];exact fetch80004b34
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 1 0x0000001c#32,2#32) := by rw [pc];exact fetch80004b36
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 8 0x00000018#32,2#32) := by rw [pc];exact fetch80004b38
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 8 2 0x00000020#32,2#32) := by rw [pc];exact fetch80004b3a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.op .add 12 0 10,2#32) := by rw [pc];exact fetch80004b3c
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 2 0x00000017#32,4#32) := by rw [pc];exact fetch80004b3e
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.lui 11 0x80005000#32,4#32) := by rw [pc];exact fetch80004b42
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 11 0x0000014e#32,4#32) := by rw [pc];exact fetch80004b46
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 10 0x0000000c#32,2#32) := by rw [pc];exact fetch80004b4a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 11 0x00000010#32,2#32) := by rw [pc];exact fetch80004b4c
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.lui 10 0x80006000#32,4#32) := by rw [pc];exact fetch80004b4e
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 10 0xfffff818#32,4#32) := by rw [pc];exact fetch80004b52
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 2 0x0000000c#32,2#32) := by rw [pc];exact fetch80004b56
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.auipc 1 0x00000000#32,4#32) := by rw [pc];exact fetch80004b58
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inr
      refine Or.inl (⟨?_,?_⟩)
      · change c.pc+4#32=0x80004b5c#32
        rw [pc];decide +kernel
      · change (c.set 1 (c.pc+0x00000000#32)).get 1=0x80004b58#32
        rw [Core.get_set_self _ _ _ (by decide),pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by rw [pc];exact fetch80004b60
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 1 0x0000001c#32,2#32) := by rw [pc];exact fetch80004b62
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 8 0x00000018#32,2#32) := by rw [pc];exact fetch80004b64
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 8 2 0x00000020#32,2#32) := by rw [pc];exact fetch80004b66
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 11 0x00000004#32,2#32) := by rw [pc];exact fetch80004b68
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 10 0x00000000#32,2#32) := by rw [pc];exact fetch80004b6a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 2 0x00000004#32,2#32) := by rw [pc];exact fetch80004b6c
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.lui 11 0x80005000#32,4#32) := by rw [pc];exact fetch80004b6e
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 11 0xffffffa4#32,4#32) := by rw [pc];exact fetch80004b72
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.op .add 13 0 2,2#32) := by rw [pc];exact fetch80004b76
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 10 0x00000008#32,2#32) := by rw [pc];exact fetch80004b78
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 11 0x0000000c#32,2#32) := by rw [pc];exact fetch80004b7a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 13 0x00000010#32,2#32) := by rw [pc];exact fetch80004b7c
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 11 0x00000014#32,2#32) := by rw [pc];exact fetch80004b7e
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.lui 10 0x80006000#32,4#32) := by rw [pc];exact fetch80004b80
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 10 0xfffff842#32,4#32) := by rw [pc];exact fetch80004b84
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 2 0x00000008#32,2#32) := by rw [pc];exact fetch80004b88
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.auipc 1 0x00000000#32,4#32) := by rw [pc];exact fetch80004b8a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inr
      refine Or.inr (Or.inl (⟨?_,?_⟩))
      · change c.pc+4#32=0x80004b8e#32
        rw [pc];decide +kernel
      · change (c.set 1 (c.pc+0x00000000#32)).get 1=0x80004b8a#32
        rw [Core.get_set_self _ _ _ (by decide),pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 2 2 0xffffffe0#32,2#32) := by rw [pc];exact fetch80004b92
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 1 0x0000001c#32,2#32) := by rw [pc];exact fetch80004b94
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 8 0x00000018#32,2#32) := by rw [pc];exact fetch80004b96
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 8 2 0x00000020#32,2#32) := by rw [pc];exact fetch80004b98
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 11 0x00000008#32,2#32) := by rw [pc];exact fetch80004b9a
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 10 0x00000004#32,2#32) := by rw [pc];exact fetch80004b9c
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 2 0x00000004#32,2#32) := by rw [pc];exact fetch80004b9e
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 0 0x00000001#32,2#32) := by rw [pc];exact fetch80004ba0
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 10 0x0000000c#32,2#32) := by rw [pc];exact fetch80004ba2
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 12 0x00000010#32,2#32) := by rw [pc];exact fetch80004ba4
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .h 2 11 0x00000014#32,4#32) := by rw [pc];exact fetch80004ba6
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 2 0x0000000c#32,2#32) := by rw [pc];exact fetch80004baa
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.auipc 1 0xffffc000#32,4#32) := by rw [pc];exact fetch80004bac
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inr
      refine Or.inr (Or.inr (Or.inl (⟨?_,?_⟩)))
      · change c.pc+4#32=0x80004bb0#32
        rw [pc];decide +kernel
      · change (c.set 1 (c.pc+0xffffc000#32)).get 1=0x80000bac#32
        rw [Core.get_set_self _ _ _ (by decide),pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 2 2 0xfffffff0#32,2#32) := by rw [pc];exact fetch80004de2
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 1 0x0000000c#32,2#32) := by rw [pc];exact fetch80004de4
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.store .w 2 8 0x00000008#32,2#32) := by rw [pc];exact fetch80004de6
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 8 2 0x00000010#32,2#32) := by rw [pc];exact fetch80004de8
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.op .add 12 0 10,2#32) := by rw [pc];exact fetch80004dea
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+2#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.lui 10 0x80006000#32,4#32) := by rw [pc];exact fetch80004dec
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 10 10 0xfffffed8#32,4#32) := by rw [pc];exact fetch80004df0
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.opimm .add 11 0 0x00000047#32,4#32) := by rw [pc];exact fetch80004df4
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inl
      change c.pc+4#32∈simple
      rw [pc];decide +kernel
    · have decoded : fetchDecode img c.pc=some (.auipc 1 0x00000000#32,4#32) := by rw [pc];exact fetch80004df8
      rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
      apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
      change At _
      apply Or.inr;apply Or.inr
      refine Or.inr (Or.inr (Or.inr (⟨?_,?_⟩)))
      · change c.pc+4#32=0x80004dfc#32
        rw [pc];decide +kernel
      · change (c.set 1 (c.pc+0x00000000#32)).get 1=0x80004df8#32
        rw [Core.get_set_self _ _ _ (by decide),pc];decide +kernel
  · have decoded : fetchDecode img c.pc=some (.jalr 1 1 0x0000003a#32,4#32) := by rw [pc];exact fetch80004b5c
    rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
    apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
    rw [exec_jalr,ra]
    change Holds At (jump _ ((0x80004b58#32+0x0000003a#32) &&& ~~~1))
    rw [show (0x80004b58#32+0x0000003a#32) &&& ~~~1=0x80004b92#32 by decide +kernel,jump_ok _ _ (by decide)]
    change At _
    exact Or.inr (Or.inl (by change 0x80004b92#32∈simple;decide +kernel))
  · have decoded : fetchDecode img c.pc=some (.jalr 1 1 0x00000008#32,4#32) := by rw [pc];exact fetch80004b8e
    rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
    apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
    rw [exec_jalr,ra]
    change Holds At (jump _ ((0x80004b8a#32+0x00000008#32) &&& ~~~1))
    rw [show (0x80004b8a#32+0x00000008#32) &&& ~~~1=0x80004b92#32 by decide +kernel,jump_ok _ _ (by decide)]
    change At _
    exact Or.inr (Or.inl (by change 0x80004b92#32∈simple;decide +kernel))
  · have decoded : fetchDecode img c.pc=some (.jalr 1 1 0xfffffcb0#32,4#32) := by rw [pc];exact fetch80004bb0
    rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
    apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
    rw [exec_jalr,ra]
    change Holds At (jump _ ((0x80000bac#32+0xfffffcb0#32) &&& ~~~1))
    rw [show (0x80000bac#32+0xfffffcb0#32) &&& ~~~1=0x8000085c#32 by decide +kernel,jump_ok _ _ (by decide)]
    change At _
    exact Or.inl (Or.inr (Or.inl rfl))
  · have decoded : fetchDecode img c.pc=some (.jalr 1 1 0xfffffd9a#32,4#32) := by rw [pc];exact fetch80004dfc
    rw [stepInstr_of (m := ⟨c,ram⟩) (by change c.pc.getLsbD 0=false;rw [pc];decide) decoded] at actual
    apply EffectCoreProperty.interp_holds (P := At) ?_ o ram 0 [] d after evs actual
    rw [exec_jalr,ra]
    change Holds At (jump _ ((0x80004df8#32+0xfffffd9a#32) &&& ~~~1))
    rw [show (0x80004df8#32+0xfffffd9a#32) &&& ~~~1=0x80004b92#32 by decide +kernel,jump_ok _ _ (by decide)]
    change At _
    exact Or.inr (Or.inl (by change 0x80004b92#32∈simple;decide +kernel))

theorem quiet {B n m d} (h : At m.core) (trace : Quiet.Steps B img n m d) : At d.core := by
  induction trace with
  | refl => exact h
  | @step n m mid d first rest ih => exact ih (instr h (first.det (fun _ => 0#32)))

def Pc (c : Core) : Prop := c.pc=0x80000034#32 ∨ (0x8000085c≤c.pc.toNat ∧ c.pc.toNat≤0x80000860) ∨
  (0x80004b34≤c.pc.toNat ∧ c.pc.toNat<0x80004e00)

theorem pc_bound {c} (h : At c) : Pc c := by
  rcases h with loop|inside|⟨pc,ra⟩|⟨pc,ra⟩|⟨pc,ra⟩|⟨pc,ra⟩
  · rcases loop with pc|pc|pc
    all_goals unfold Pc;rw [pc];decide +kernel
  · have checked : simple.all (fun w => decide (0x80004b34≤w.toNat ∧ w.toNat<0x80004e00))=true := by decide +kernel
    exact Or.inr (Or.inr (of_decide_eq_true (List.all_eq_true.mp checked c.pc inside)))
  · unfold Pc;rw [pc];decide +kernel
  · unfold Pc;rw [pc];decide +kernel
  · unfold Pc;rw [pc];decide +kernel
  · unfold Pc;rw [pc];decide +kernel

def entries : List Word := [0x80004b34#32,0x80004b60#32,0x80004b92#32,0x80004de2#32]
theorem entry {c} (h : c.pc∈entries) : At c := by
  have pcs : c.pc=0x80004b34#32 ∨ c.pc=0x80004b60#32 ∨ c.pc=0x80004b92#32 ∨ c.pc=0x80004de2#32 := by simpa only [entries,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using h
  rcases pcs with pc|pc|pc|pc
  all_goals apply Or.inr;apply Or.inl;rw [pc];decide +kernel
end E5R.Thermostat.PanicEntries
