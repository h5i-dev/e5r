/- Independent thermostat specification. Original e5r code, Apache-2.0.
   Inputs are the full Rust domains; rejection leaves device state unchanged. -/
namespace E5R.Thermostat.Spec

inductive Mode where
  | off | heat | auto
  deriving DecidableEq

structure Snapshot where
  setpoint : BitVec 16
  temp : BitVec 16
  heater : Bool
  relays : Fin 4 → Bool
  mode : Mode

inductive Command where
  | setpoint (dc : BitVec 16)
  | reportTemp (dc : BitVec 16)
  | relay (index : BitVec 8) (on : Bool)
  | mode (value : Mode)
  | read

inductive Error where
  | setpointOutOfRange | noSuchRelay | forbidden
  deriving DecidableEq

structure Success where
  write : Option Snapshot
  reply : Snapshot

def heater (m : Mode) (t sp : BitVec 16) : Bool :=
  decide (t.toInt < 350) && match m with
    | .off => false
    | .heat => true
    | .auto => decide (t.toInt < sp.toInt)

def settle (s : Snapshot) : Snapshot := { s with heater := heater s.mode s.temp s.setpoint }

def initial : Snapshot := ⟨200, 200, false, fun _ => false, .off⟩

def apply (s : Snapshot) : Option Snapshot → Snapshot
  | none => s
  | some n => n

def readOnly : Command → Bool
  | .read => true
  | _ => false

def configurable : Command → Bool
  | .setpoint _ | .relay _ _ | .mode _ => true
  | _ => false

def changed (s : Snapshot) : Except Error Success := .ok ⟨some s, s⟩

/-- Expected API behavior, including authorization priority and unchanged replies. -/
def transition (admin : Bool) (s : Snapshot) : Command → Except Error Success
  | .read => .ok ⟨none, s⟩
  | .reportTemp t => changed (settle { s with temp := t })
  | .setpoint sp =>
    if !admin then .error .forbidden
    else if sp.toInt < 50 ∨ 300 < sp.toInt then .error .setpointOutOfRange
    else changed (settle { s with setpoint := sp })
  | .relay i on =>
    if !admin then .error .forbidden
    else if i.toNat < 4 then
      changed { s with relays := fun r => if r.val = i.toNat then on else s.relays r }
    else .error .noSuchRelay
  | .mode m =>
    if !admin then .error .forbidden
    else changed (settle { s with mode := m })

/-- Committing a rejected command leaves the snapshot unchanged. -/
def commit (s : Snapshot) : Except Error Success → Snapshot
  | .error _ => s
  | .ok r => apply s r.write

def Inv (s : Snapshot) : Prop :=
  (s.heater = true → s.temp.toInt < 350) ∧ 50 ≤ s.setpoint.toInt ∧ s.setpoint.toInt ≤ 300

theorem heater_interlock (m t sp) (h : heater m t sp = true) : t.toInt < 350 := by
  simp only [heater, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1

theorem settle_interlock (s : Snapshot) :
    (settle s).heater = true → (settle s).temp.toInt < 350 := heater_interlock _ _ _

theorem initial_inv : Inv initial := by unfold Inv initial; decide +kernel

theorem read_sound (admin s) : transition admin s .read = .ok ⟨none, s⟩ := rfl

theorem read_only_sound (admin s cmd r) (hc : readOnly cmd = true)
    (hr : transition admin s cmd = .ok r) : r.write = none ∧ r.reply = s := by
  cases cmd <;> simp [readOnly] at hc
  simp [transition] at hr
  subst r
  exact ⟨rfl, rfl⟩

theorem reply_committed (admin s cmd r) (hr : transition admin s cmd = .ok r) :
    r.reply = apply s r.write := by
  cases cmd <;> simp only [transition] at hr
  all_goals (try split at hr) <;> (try split at hr) <;> simp_all [changed, apply]
  all_goals subst r; rfl

theorem unauthorized (s : Snapshot) (cmd : Command)
    (hc : (match cmd with | .setpoint _ | .relay _ _ | .mode _ => true | _ => false) = true) :
    transition false s cmd = .error .forbidden := by
  cases cmd <;> simp_all [transition]

theorem bad_relay (s : Snapshot) (i : BitVec 8) (on : Bool) (hi : 4 ≤ i.toNat) :
    transition true s (.relay i on) = .error .noSuchRelay := by
  simp [transition, show ¬i.toNat < 4 by omega]

theorem bad_setpoint (s : Snapshot) (sp : BitVec 16)
    (h : sp.toInt < 50 ∨ 300 < sp.toInt) :
    transition true s (.setpoint sp) = .error .setpointOutOfRange := by simp [transition, h]

theorem commit_inv (admin : Bool) (s : Snapshot) (cmd : Command) (hs : Inv s) :
    Inv (commit s (transition admin s cmd)) := by
  obtain ⟨hh, hl, hu⟩ := hs
  cases cmd with
  | read => exact ⟨hh, hl, hu⟩
  | reportTemp t => exact ⟨settle_interlock _, hl, hu⟩
  | setpoint sp =>
    simp only [transition]
    split
    · exact ⟨hh, hl, hu⟩
    · split
      · exact ⟨hh, hl, hu⟩
      · rename_i h
        exact ⟨settle_interlock _, by change 50 ≤ sp.toInt; omega,
          by change sp.toInt ≤ 300; omega⟩
  | relay i on =>
    simp only [transition]
    split
    · exact ⟨hh, hl, hu⟩
    · split <;> exact ⟨hh, hl, hu⟩
  | mode m =>
    simp only [transition]
    split
    · exact ⟨hh, hl, hu⟩
    · exact ⟨settle_interlock _, hl, hu⟩

/-- Successful and refused commands from arbitrary actors are both included. -/
inductive Reachable : Snapshot → Prop
  | initial : Reachable initial
  | step {s} : Reachable s → (admin : Bool) → (cmd : Command) →
      Reachable (commit s (transition admin s cmd))

theorem reachable_inv {s} (h : Reachable s) : Inv s := by
  induction h with
  | initial => exact initial_inv
  | step _ admin cmd ih => exact commit_inv admin _ cmd ih

end E5R.Thermostat.Spec
