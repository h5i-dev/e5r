import Theories.Logic
set_option linter.unusedSimpArgs false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
set_option linter.constructorNameAsVariable false
namespace E5R.Thermostat.Observed
open E5R

/-- Accepted device reads, including their original per-instruction oracle index.
    Values are exactly width-masked by the existing platform interpreter. -/
structure Read where
  addr : Word
  width : Width
  value : Word
  oracleIndex : Nat

structure Result where
  value : E5R.Result
  reads : List Read

/-- An instrumented copy of interp. The erasure theorem below relates every
    branch, fault and oracle choice to the unchanged platform interpreter. -/
def interp (B : Board) (img : List Segment) (o : Oracle) :
    Eff → (Word → BitVec 8) → Nat → List Event → List Read → Result
  | .done c, ram, _, evs, reads => ⟨.ok c ram evs,reads⟩
  | .trap e, _, _, _, reads => ⟨.fault (.trap e),reads⟩
  | .unsupported why, _, _, _, reads => ⟨.fault (.unsupported why),reads⟩
  | .choose k, ram, i, evs, reads => interp B img o (k ((o i).getLsbD 0)) ram (i+1) evs reads
  | .pick k, ram, i, evs, reads => interp B img o (k (o i)) ram (i+1) evs reads
  | .load w a atomic k, ram, i, evs, reads =>
    if a.toNat % w.bytes ≠ 0 then ⟨.fault .misaligned,reads⟩
    else if B.inRam a w.bytes then interp B img o (k (ramRead ram a w)) ram i evs reads
    else if atomic then ⟨.fault (.unsupported "atomic access outside RAM"),reads⟩
    else match romRead? img a.toNat w.bytes false with
      | some v => interp B img o (k v) ram i evs reads
      | none => match B.device? a with
        | some d => if d.read && w.bytes = d.width then
            interp B img o (k (devVal w (o i))) ram (i+1) evs (reads ++ [⟨a,w,devVal w (o i),i⟩])
          else ⟨.fault (.unsupported "device read"),reads⟩
        | none => ⟨.fault (.unsupported "load from an unmodeled address"),reads⟩
  | .store w a v atomic k, ram, i, evs, reads =>
    if a.toNat % w.bytes ≠ 0 then ⟨.fault .misaligned,reads⟩
    else if B.inRam a w.bytes then interp B img o k (ramWrite ram a v w) i evs reads
    else if atomic then ⟨.fault (.unsupported "atomic access outside RAM"),reads⟩
    else match B.device? a with
      | some d => if d.write && w.bytes = d.width then interp B img o k ram i (evs ++ [⟨a,devVal w v⟩]) reads
          else ⟨.fault (.unsupported "device write"),reads⟩
      | none => ⟨.fault (.unsupported "store to an unmodeled address"),reads⟩

theorem erase (B : Board) (img : List Segment) (o : Oracle) (e : Eff)
    (ram : Word → BitVec 8) (i : Nat) (evs : List Event) (reads : List Read) :
    (interp B img o e ram i evs reads).value = E5R.interp B img o e ram i evs := by
  induction e generalizing ram i evs reads with
  | done c => rfl
  | trap e => rfl
  | unsupported why => rfl
  | choose k ih => exact ih _ ram (i+1) evs reads
  | pick k ih => exact ih _ ram (i+1) evs reads
  | load w a atomic k ih =>
    simp only [interp,E5R.interp]
    split
    · rfl
    · split
      · exact ih _ ram i evs reads
      · split
        · rfl
        · cases hr : romRead? img a.toNat w.bytes false with
          | some v =>
            simp only [hr]
            exact ih v ram i evs reads
          | none =>
            simp only [hr]
            cases hd : B.device? a with
            | none => rfl
            | some d =>
              simp only [hd]
              split
              · exact ih _ ram (i+1) evs _
              · rfl
  | store w a v atomic k ih =>
    simp only [interp,E5R.interp]
    split
    · rfl
    · split
      · exact ih _ i evs reads
      · split
        · rfl
        · cases hd : B.device? a with
          | none => rfl
          | some d =>
            simp only [hd]
            split
            · exact ih ram i _ reads
            · rfl

def stepInstr (B : Board) (img : List Segment) (m : Machine) (o : Oracle) : Result :=
  if m.core.pc.getLsbD 0 then ⟨.fault (.trap .misalignedFetch),[]⟩ else
  match fetch img m.core.pc with
  | none => ⟨.fault (.unsupported "fetch outside the executable image"),[]⟩
  | some (bits,len) => match decode bits len with
    | none => ⟨.fault (.trap .illegal),[]⟩
    | some i => interp B img o (exec m.core len i) m.ram 0 [] []

theorem erase_step (B : Board) (img : List Segment) (m : Machine) (o : Oracle) :
    (stepInstr B img m o).value = E5R.stepInstr B img m o := by
  unfold stepInstr E5R.stepInstr
  split
  · rfl
  · cases hf : fetch img m.core.pc with
    | none => rfl
    | some v =>
      rcases v with ⟨bits,len⟩
      simp only
      cases hd : decode bits len with
      | none => rfl
      | some i => exact erase B img o (exec m.core len i) m.ram 0 [] []


theorem stepInstr_of {B img} {m : Machine} {i len o}
    (hal : m.core.pc.getLsbD 0 = false) (hd : fetchDecode img m.core.pc = some (i,len)) :
    stepInstr B img m o = interp B img o (exec m.core len i) m.ram 0 [] [] := by
  unfold fetchDecode at hd
  unfold stepInstr
  rw [hal]
  split at hd
  · rename_i bits len' hf
    simp only [hf]
    cases hdec : decode bits len' with
    | none => simp [hdec] at hd
    | some i' =>
      simp only [hdec,Option.map_some,Option.some.injEq,Prod.mk.injEq] at hd
      obtain ⟨rfl,rfl⟩ := hd
      rfl
  · simp at hd

inductive Step (B : Board) (img : List Segment) : Machine → Machine → List Read → List Event → Prop
  | instr {m c ram evs} (o : Oracle) (h : (stepInstr B img m o).value = .ok c ram evs) :
      Step B img m ⟨c,ram⟩ (stepInstr B img m o).reads evs
  | irq {m c} (code : Nat) (h : irqEnabled m.core code = true) (hk : takeIrq m.core code = .done c) :
      Step B img m ⟨c,m.ram⟩ [] []

theorem step_erase {B img m m' reads evs} (h : Step B img m m' reads evs) : E5R.Step B img m m' evs := by
  cases h with
  | instr o h => exact .instr o ((erase_step B img m o).symm.trans h)
  | irq code h hk => exact .irq code h hk


/-- Empty read logs require a pure effect proof, not merely DetStep: an
    ignored device read can have a deterministic result and still be observed. -/
theorem pure_step {B img} {m : Machine} {i len c}
    (hal : m.core.pc.getLsbD 0 = false) (hf : fetchDecode img m.core.pc = some (i,len))
    (he : exec m.core len i = .done c) : Step B img m ⟨c,m.ram⟩ [] [] := by
  let o : Oracle := fun _ => 0#32
  have hk : stepInstr B img m o = ⟨.ok c m.ram [],[]⟩ := by
    rw [stepInstr_of hal hf,he]
    rfl
  have hs : Step B img m ⟨c,m.ram⟩ (stepInstr B img m o).reads [] := .instr o (by rw [hk])
  simpa only [hk] using hs

/-- Every original successful step lifts, using its same oracle/IRQ choice. -/
theorem step_complete {B img m m' evs} (h : E5R.Step B img m m' evs) :
    ∃ reads, Step B img m m' reads evs := by
  cases h with
  | instr o h => exact ⟨_,.instr o ((erase_step B img m o).trans h)⟩
  | irq code h hk => exact ⟨[],.irq code h hk⟩

def Escapes (B : Board) (img : List Segment) (m : Machine) : Prop :=
  (∃ o f, (stepInstr B img m o).value = .fault f) ∨
  (∃ code e, irqEnabled m.core code = true ∧ takeIrq m.core code = .trap e)

theorem escapes_iff (B : Board) (img : List Segment) (m : Machine) :
    Escapes B img m ↔ E5R.Escapes B img m := by
  simp only [Escapes,E5R.Escapes,erase_step]

inductive Reach (B : Board) (img : List Segment) (Init : Machine → Prop) :
    Machine → List Read → List Event → Prop
  | init {m} : Init m → Reach B img Init m [] []
  | step {m m' reads reads' evs evs'} : Reach B img Init m reads evs → Step B img m m' reads' evs' →
      Reach B img Init m' (reads++reads') (evs++evs')

theorem reach_erase {B img Init m reads evs} (h : Reach B img Init m reads evs) : E5R.Reach B img Init m evs := by
  induction h with
  | init h => exact .init h
  | step _ hs ih => exact .step ih (step_erase hs)

theorem reach_complete {B img Init m evs} (h : E5R.Reach B img Init m evs) :
    ∃ reads, Reach B img Init m reads evs := by
  induction h with
  | init h => exact ⟨[],.init h⟩
  | step _ hs ih =>
    obtain ⟨reads,hr⟩ := ih
    obtain ⟨reads',hs'⟩ := step_complete hs
    exact ⟨reads++reads',.step hr hs'⟩


/-- Finite observed paths with a logical transition count. This does not
    assign physical cycles or assume that the scheduler takes the next step. -/
inductive Steps (B : Board) (img : List Segment) : Nat → Machine → Machine → List Read → List Event → Prop
  | refl (m) : Steps B img 0 m m [] []
  | step {n m m1 m2 reads0 reads1 evs0 evs1} :
      Step B img m m1 reads0 evs0 → Steps B img n m1 m2 reads1 evs1 →
      Steps B img (n+1) m m2 (reads0++reads1) (evs0++evs1)

theorem Steps.single {B img m m' reads evs} (h : Step B img m m' reads evs) :
    Steps B img 1 m m' reads evs := by
  simpa using Steps.step h (Steps.refl m')

theorem Steps.trans {B img n k a b c reads0 reads1 evs0 evs1}
    (h : Steps B img n a b reads0 evs0) (hk : Steps B img k b c reads1 evs1) :
    Steps B img (n+k) a c (reads0++reads1) (evs0++evs1) := by
  induction h with
  | refl => simpa using hk
  | step hs _ ih =>
    simpa only [Nat.add_right_comm,List.append_assoc] using Steps.step hs (ih hk)

theorem Steps.reach {B img Init n a b reads evs reads0 evs0}
    (h : Steps B img n a b reads evs) (ha : Reach B img Init a reads0 evs0) :
    Reach B img Init b (reads0++reads) (evs0++evs) := by
  induction h generalizing reads0 evs0 with
  | refl => simpa using ha
  | step hs _ ih =>
    have hh := ih (Reach.step ha hs)
    simpa only [List.append_assoc] using hh

/-- Delivered UART bytes are the accepted byte-wide RBR reads. Interpreting
    these as physical host input additionally requires DLAB/configuration and
    delivery assumptions; no readiness or FIFO guarantee is added here. -/
def input (reads : List Read) : List (BitVec 8) := reads.filterMap fun r =>
  if r.addr = 0x10000000#32 ∧ r.width.bytes = 1 then some (r.value.setWidth 8) else none

/-- Low-byte projection of original events at the UART address. This matches
    THR byte writes when the board declares that register byte-wide. -/
def output (evs : List Event) : List (BitVec 8) := evs.filterMap fun e =>
  if e.addr = 0x10000000#32 then some (e.val.setWidth 8) else none

theorem input_append (a b : List Read) : input (a++b) = input a++input b := by simp [input,List.filterMap_append]
theorem output_append (a b : List Event) : output (a++b) = output a++output b := by simp [output,List.filterMap_append]

/-- An observational stream view of the original semantics, with no assumed
    application behavior or progress. Both directions below are proved. -/
def UARTReach (B : Board) (img : List Segment) (Init : Machine → Prop) (m : Machine)
    (rx tx : List (BitVec 8)) : Prop :=
  ∃ reads evs, Reach B img Init m reads evs ∧ input reads = rx ∧ output evs = tx

theorem uart_erase {B img Init m rx tx} (h : UARTReach B img Init m rx tx) :
    ∃ evs, E5R.Reach B img Init m evs ∧ output evs = tx := by
  obtain ⟨_,evs,hr,_,htx⟩ := h
  exact ⟨evs,reach_erase hr,htx⟩

theorem uart_complete {B img Init m evs} (h : E5R.Reach B img Init m evs) :
    ∃ rx, UARTReach B img Init m rx (output evs) := by
  obtain ⟨reads,hr⟩ := reach_complete h
  exact ⟨input reads,reads,evs,hr,rfl,rfl⟩

end E5R.Thermostat.Observed
