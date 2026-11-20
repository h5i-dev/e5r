import NoCompiler.RefineLockstep

/-
Regions: the unit of a changed interval (docs/isa/refine.md, items 3 and 4).

A region pairs an interval of B's code with an interval of A's: each has
one entry and one exit (a subtree of the block/loop tree, or a straight-line
run inside one), and the region says which registers are live at the entry
and at the exit. Inside, the two may differ arbitrarily: different
instructions, different numbers of them, different loop shapes.

`Region.Ok` is what has to be proved about one: a local refinement. From
any two states at the two entries that agree on `liveIn` (and on memory,
trace and exit status), where A's run through its interval is safe and
terminates, B's run through its interval is safe and terminates, and every
way B leaves it is matched by a way A leaves it: both at their exits,
agreeing on `liveOut`, with A's ra as it was; or both exited the process
with the same status and events. Every access inside is under the same
permission `P`, for every `P`: what B touches, A touches.

How a region is proved is open: by stepping both sides symbolically
(straight-line), by a relational loop invariant (same-shaped loops), by a
k:1 correspondence (an unrolled loop), or by local summaries. Facts about
the entry state that hold of A's runs but are not in `liveIn` (for example,
that two pointers do not alias) are not available; a region that needs one
is stated with it as an extra entry condition `pre`, which becomes a
reported precondition of the refinement.

The certificate of `NoCompiler/RefineLockstep.lean` pairs single, identical
instructions; a region pair stands for a whole changed interval in it, with
its `Region.Ok` proof as a hypothesis of the soundness theorem (next step).
-/
namespace NoCompiler

/-- A changed interval: B's code `domB` entered at `pb` and left at `pbExit`,
    A's code `domA` entered at `pa` and left at `paExit`. -/
structure RRegion where
  pb : Word
  pa : Word
  pbExit : Word
  paExit : Word
  domB : Dom
  domA : Dom
  liveIn : List Reg
  liveOut : List Reg
  deriving DecidableEq, Repr

namespace RRegion

/-- How the two runs leave a region, seen from A's state `sa` at its entry. -/
def Exit (r : RRegion) (sa ta tb : State) : Prop :=
  (ta.exit = none ∧ ta.pc = r.paExit ∧ tb.pc = r.pbExit ∧ ta.reg 1 = sa.reg 1 ∧ Agree r.liveOut ta tb) ∨
  (ta.exit ≠ none ∧ Agree [] ta tb)

/-- What a region's proof establishes, under an entry condition `pre` on A's
    state (`fun _ => True` when the region needs none). -/
def Ok (cA cB : Code) (r : RRegion) (pre : State → Prop := fun _ => True) : Prop :=
  ∀ (P : Perm) (sa sb : State), sa.exit = none → sa.pc = r.pa → sb.pc = r.pb →
    Agree r.liveIn sa sb → pre sa →
    Exec cA P r.domA (fun _ => True) sa →
    Exec cB P r.domB (fun tb => ∃ ta, Run cA P r.domA sa ta ∧ Final r.domA ta ∧ r.Exit sa ta tb) sb

/-- The region checks a certificate needs of its shape, decided by the
    kernel: the entries lie in the intervals, the exits do not, and the
    intervals lie inside the functions' code. -/
def shapeOk (DA DB : Dom) (r : RRegion) : Bool :=
  decide (r.domB.mem r.pb) && decide (r.domA.mem r.pa) &&
  !decide (r.domB.mem r.pbExit) && !decide (r.domA.mem r.paExit) &&
  r.domB.all (fun x => DB.contains x) && r.domA.all (fun x => DA.contains x)

end RRegion
end NoCompiler
