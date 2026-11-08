import Projects.thermostat.Quiet
namespace E5R.Thermostat.QuietEffect
open E5R E5R.Thermostat

/-- A structural sufficient condition for an effect to accept no device reads.
    Atomic accesses outside RAM still fail closed. Device writes are allowed
    here: silence is obtained separately from the deterministic-step premise. -/
inductive Safe (B : Board) (img : List Segment) : Eff → Prop
  | done (c) : Safe B img (.done c)
  | trap (e) : Safe B img (.trap e)
  | unsupported (why) : Safe B img (.unsupported why)
  | choose {k} (all : ∀ b, Safe B img (k b)) : Safe B img (.choose k)
  | pick {k} (all : ∀ v, Safe B img (k v)) : Safe B img (.pick k)
  | store {w a v atomic k} (next : Safe B img k) : Safe B img (.store w a v atomic k)
  | load {w a atomic k}
      (source : atomic=true ∨ B.inRam a w.bytes=true ∨ ∃ v, romRead? img a.toNat w.bytes false=some v)
      (all : ∀ v, Safe B img (k v)) : Safe B img (.load w a atomic k)

theorem reads {B img e} (h : Safe B img e) (o : Oracle) (ram : Word → BitVec 8) (index : Nat)
    (events : List Event) (log : List Observed.Read) : (Observed.interp B img o e ram index events log).reads=log := by
  induction h generalizing ram index events log with
  | done c => rfl
  | trap e => rfl
  | unsupported why => rfl
  | choose _ ih => exact ih _ ram (index+1) events log
  | pick _ ih => exact ih _ ram (index+1) events log
  | store _ ih =>
    simp only [Observed.interp]
    split
    · rfl
    · split
      · exact ih _ index events log
      · split
        · rfl
        · split
          · split
            · exact ih ram index _ log
            · rfl
          · rfl
  | load source _ ih =>
    simp only [Observed.interp]
    split
    · rfl
    · split
      · exact ih _ ram index events log
      · split
        · rfl
        · cases hr : romRead? img _ _ false with
          | some value =>
            simp only [hr]
            exact ih value ram index events log
          | none =>
            exfalso
            rcases source with ha|ha|⟨value,hv⟩ <;> simp_all

theorem result_ext {a b : Observed.Result} (hv : a.value=b.value) (hr : a.reads=b.reads) : a=b := by
  cases a;cases b;cases hv;cases hr;rfl

/-- Upgrade an existing deterministic instruction proof only after proving
    that its actual effect cannot accept a device read. -/
theorem promote {B : Board} {img : List Segment} {c d : Core} {ram after : Word → BitVec 8} {i : Instr} {len : Word}
    (hal : c.pc.getLsbD 0=false) (fetch : fetchDecode img c.pc=some (i,len))
    (safe : Safe B img (exec c len i)) (step : DetStep B img ⟨c,ram⟩ ⟨d,after⟩) : Quiet.Step B img ⟨c,ram⟩ ⟨d,after⟩ := by
  intro o
  apply result_ext
  · exact (Observed.erase_step B img ⟨c,ram⟩ o).trans (step o)
  · have hs := Observed.stepInstr_of (B := B) (img := img) (m := (⟨c,ram⟩ : Machine)) (o := o) hal fetch
    exact (congrArg Observed.Result.reads hs).trans (reads safe o ram 0 [] [])
end E5R.Thermostat.QuietEffect
