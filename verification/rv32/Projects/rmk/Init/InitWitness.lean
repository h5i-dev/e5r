/-
  Non-vacuity of the initialization entry `InitAt` (Init/InitPath.lean): a concrete machine with
  the values observed on QEMU virt satisfies it.

  Original e5r code, Apache-2.0.

  PROVED here: `initAt_real : InitAt mI`. NOT shown: that the task's first poll reaches it.
-/
import Projects.rmk.Init.InitPath
import Projects.rmk.Deframer.SomeWitness

set_option maxRecDepth 100000

namespace E5R.Rmk.Init
open E5R E5R.Rmk E5R.Rmk.Deframer.Session E5R.Rmk.Deframer.SomeW

/-- sp = 0x80fffe10; arguments [sp+0x1c] = RX 0x8002a1c0, [sp+0x18] = TX 0x8002a1e4; the flag pointer
    [sp+0x24] = 0x8002a7c9; both UART structs at base 0x10000000, stride 1. -/
def tI : List (Nat × Nat) :=
  [(0x80fffe2c, 0xc0), (0x80fffe2d, 0xa1), (0x80fffe2e, 0x02), (0x80fffe2f, 0x80),
   (0x80fffe28, 0xe4), (0x80fffe29, 0xa1), (0x80fffe2a, 0x02), (0x80fffe2b, 0x80),
   (0x80fffe34, 0xc9), (0x80fffe35, 0xa7), (0x80fffe36, 0x02), (0x80fffe37, 0x80),
   (0x8002a1df, 0x10), (0x8002a1e0, 1), (0x8002a203, 0x10), (0x8002a204, 1)]

def mI : Machine := ⟨mkCore 0x80003b38 [(2, 0x80fffe10), (22, s6v), (23, s7v)], memT tI⟩

theorem initAt_real : InitAt mI :=
  ⟨rfl, mkCore_quiet _ _, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, by decide, by decide⟩

end E5R.Rmk.Init
