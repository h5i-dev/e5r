import Projects.thermostat.Observed
namespace E5R.Thermostat.ObservedRam
open E5R E5R.Thermostat

theorem load (B : Board) (img : List Segment) (o : Oracle) (w : Width) (a : Word) (atomic : Bool)
    (k : Word → Eff) (ram : Word → BitVec 8) (i : Nat) (evs : List Event) (reads : List Observed.Read)
    (hal : a.toNat%w.bytes=0) (hin : B.inRam a w.bytes=true) :
    Observed.interp B img o (.load w a atomic k) ram i evs reads =
      Observed.interp B img o (k (ramRead ram a w)) ram i evs reads := by
  simp [Observed.interp,hal,hin]

theorem store (B : Board) (img : List Segment) (o : Oracle) (w : Width) (a v : Word) (atomic : Bool)
    (k : Eff) (ram : Word → BitVec 8) (i : Nat) (evs : List Event) (reads : List Observed.Read)
    (hal : a.toNat%w.bytes=0) (hin : B.inRam a w.bytes=true) :
    Observed.interp B img o (.store w a v atomic k) ram i evs reads =
      Observed.interp B img o k (ramWrite ram a v w) i evs reads := by
  simp [Observed.interp,hal,hin]
end E5R.Thermostat.ObservedRam
