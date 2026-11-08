import Projects.thermostat.WriteBoard
import Projects.thermostat.WordRegions
import Projects.thermostat.RequestWitness
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.WriteWitness
open E5R E5R.Thermostat

def futureByte : Nat → BitVec 8
  | 6 => 2#8 | 7 => 128#8 | 10 => 1#8 | 11 => 128#8
  | 14 => 7#8 | 15 => 128#8 | 17 => 4#8 | _ => 0#8

def ram (a : Word) : BitVec 8 :=
  if 0x80030000 ≤ a.toNat ∧ a.toNat < 0x80030029 then futureByte (a.toNat-0x80030000)
  else RequestWitness.ram a

def core : Core :=
  ⟨0x800004c6#32,(fun r => if r = 1 then 0x80000abc#32 else if r = 2 then 0x800500b0#32
    else if r = 10 then 0x80060000#32 else if r = 11 then 0x80030000#32
    else BitVec.ofNat 32 (0x11110000+r.val)),false,false,3,0,0,0,0,0,false⟩

theorem region (obj : Word) (n : Nat) (hs : WordRegions.Disjoint obj n 0x80030000#32 41) :
    ViewFrame.Region RequestWitness.ram ram obj n := by
  intro i
  have ho := WordRegions.outside hs (by decide) i
  change (if 0x80030000 ≤ (obj+BitVec.ofNat 32 i.val).toNat ∧
    (obj+BitVec.ofNat 32 i.val).toNat < 0x80030029 then _ else _) = _
  change ¬(0x80030000 ≤ (obj+BitVec.ofNat 32 i.val).toNat ∧ (obj+BitVec.ofNat 32 i.val).toNat < 0x80030029) at ho
  rw [ite_eq_right ho]

theorem avoid (obj : Word) (n : Nat) (hsp : WordRegions.Disjoint obj n 0x80050050#32 96)
    (hf : WordRegions.Disjoint obj n 0x80030000#32 41) : WriteInput.Avoid obj n 0x80050050#32 0x80030000#32 := ⟨hsp,hf⟩

theorem pre : WriteInput.Pre UartPlatform.board core ram 0x80050000#32 0x80030000#32 0x80060000#32
    0x80020000#32 0x80010000#32 0x80040000#32 0x80040005#32 0x80040049#32
    RequestWitness.raw RequestWitness.path RequestWitness.body RequestWitness.entries none true Spec.initial := by
  have he : WordRegions.Disjoint 0x80010000#32 25 0x80030000#32 41 := WordRegions.before _ _ _ _ (by decide) (by decide)
  have hr : WordRegions.Disjoint 0x80020000#32 372 0x80030000#32 41 := WordRegions.before _ _ _ _ (by decide) (by decide)
  have hraw : WordRegions.Disjoint 0x80040000#32 RequestWitness.raw.length 0x80030000#32 41 := WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hpath : WordRegions.Disjoint 0x80040005#32 RequestWitness.path.length 0x80030000#32 41 := WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hbody : WordRegions.Disjoint 0x80040049#32 RequestWitness.body.length 0x80030000#32 41 := WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide))
  have hl := WriteInput.layout_frame (WriteInput.of_txn RequestWitness.pre) (region _ _ he) (region _ _ hr)
    (region _ _ hraw) (region _ _ hpath) (region _ _ hbody)
  refine ⟨rfl,rfl,rfl,rfl,?_,?_,by decide,?_,by decide +kernel,by decide +kernel,by decide +kernel,hl,?_,?_,?_,?_,?_⟩
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · unfold Memory.Block UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
  · exact WordRegions.before _ _ _ _ (by decide) (by decide)
  · exact avoid _ _ (WordRegions.before _ _ _ _ (by decide) (by decide)) he
  · exact avoid _ _ (WordRegions.before _ _ _ _ (by decide) (by decide)) hr
  · exact avoid _ _ (WordRegions.before _ _ _ _ (by decide) (by decide)) hraw
  · exact avoid _ _ (WordRegions.before _ _ _ _ (by decide) (by decide)) hpath
  · exact avoid _ _ (WordRegions.before _ _ _ _ (by decide) (by decide)) hbody

/-- Real handler entry with arbitrary nonzero caller saves, concrete complete
    HTTP bytes and fresh Future reaches the actual committed auto reply. -/
theorem accepts_auto :
    ∃ n d r, n ≤ 1163 ∧ DetSteps UartPlatform.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000736#32 ∧ r 0x8001000d#32 = 2#8 ∧ ramRead r 0x80010000#32 .w = 0#32 ∧
      Engine.InvariantAt r 0x80010000#32 ∧ ramRead r 0x8005007c#32 .w = core.get 27 := by
  obtain ⟨n,d,r,hn,ht,hpost,hi⟩ := WriteBoard.contract_inv core ram
    0x80050000#32 0x80030000#32 0x80060000#32 0x80020000#32 0x80010000#32
    0x80040000#32 0x80040005#32 0x80040049#32 RequestWitness.raw RequestWitness.path RequestWitness.body
    RequestWitness.entries none true Spec.initial (.mode .auto) pre
    (by decide +kernel) (by decide +kernel) Spec.initial_inv
  refine ⟨n,d,r,hn,ht,hpost.pc,hpost.state ⟨9,by decide⟩,hpost.released,hi,?_⟩
  have hw := ViewFrame.word hpost.saved 0 (by decide)
  have hs := (OuterSave.saved ram 0x80050050#32 core).2.2.2.2.2.2.2.2.2.2.2.2
  exact hw.trans hs
theorem accepts_auto_closed :
    ∃ n d r, n ≤ 1163 ∧ Trace.Closed UartPlatform.board img n ⟨core,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80000736#32 ∧ r 0x8001000d#32 = 2#8 ∧ ramRead r 0x80010000#32 .w = 0#32 ∧
      Engine.InvariantAt r 0x80010000#32 ∧ ramRead r 0x8005007c#32 .w = core.get 27 := by
  obtain ⟨n,d,r,hn,ht,hpc,hm,hb,hi,hs⟩ := accepts_auto
  exact ⟨n,d,r,hn,Interrupt.close ht rfl,hpc,hm,hb,hi,hs⟩
end E5R.Thermostat.WriteWitness
