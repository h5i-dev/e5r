/-
  MEASUREMENT ONLY, NOT A PROOF: a draft summary of the actuator's channel
  head update (0x20010698..0x200106ae), used with `E5R_RING_DRAFT=1` to ask
  the analyzer how far a proved summary would get it. No theorem uses it;
  the proved summary belongs to the hybrid work (Theories/Hybrid/).
-/
import Theories.Absint
open E5R E5R.AI

namespace Analyze.RingDraft

def pc : Nat := 0x20010698
def exitPc : Nat := 0x200106b0

def accepts (s : AState) : Bool :=
  s.mie == .no &&
  match s.get 10, s.get 9 with
  | .vals l, .vals [p] => !l.isEmpty && l.all (· < 4) && p % 4 == 0 && 0x80000000 ≤ p && p + 0x24 ≤ 0x80004000
  | _, _ => false

def post (s : AState) : AState :=
  match s.get 10, s.get 9 with
  | .vals l, .vals [p] =>
    let a0 := mkVals (l.map fun h => (h + 1) % 4)
    let s := ((((s.set 10 a0).set 11 (.rng 0 255)).set 12 (mkVals (l.map (· + 1)))).set 13
      (mkVals (l.map fun h => (h + 1 + M32 - 4) % M32)))
    { s with pc := exitPc, mem := storeStrong s.mem .abs (p + 0x14) .w a0 }
  | _, _ => { s with pc := exitPc, regs := s.regs.map fun _ => .top, mem := [] }

def spec : SumSpec := { pc, accepts, post }

end Analyze.RingDraft
