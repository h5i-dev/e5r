/-
  The RMK session poll's UART send path on the image the job runner generates
  (`jobs/rmk/rmk-uart-send-round.json`). Original e5r code, Apache-2.0.

  Restates, with their types written out (an interface change fails this job):
  * main's `send_bytes` (5bf94a2, no contract), with `SendEnv`/`SendPost` pinned field by field and two
    concrete witnesses (Projects/ramimage/SendBytes.lean);
  * `send_round`: the poll's send loop from 0x8000429e, composed with `send_bytes`;
  * `send_to_loop`: continued through the unpark site to the loop head with `SessInv`.
  Both are FROM `SendAt` (and, for `send_to_loop`, `Extras` + parked/discarding), which are hypotheses here.
  `w_sendAt` / `w_sendLoop` show they are satisfiable. Not built on DispatchContract/EncodeContract
  (refuted, isa-review 3ecd81b).

  BOUNDARIES (not proved): the yield poll 0x8001e14a and the executor beyond it; that the Some path
  reaches 0x8000429e with `SendAt`. Interrupts: `Quiet` is carried, never assumed preserved by others.
  `SessionSafe` is NOT proved.
-/
import Projects.ramimage.SendBytes
import Projects.rmk.Uart.SendToLoop

namespace E5R.RmkSend
open E5R E5R.Rmk.Deframer E5R.Rmk.Deframer.SessionI
open E5R.Rmk (Lands)
open E5R.Rmk.Uart (SendAt SendQ SendLoopQ)

theorem send_round (m₀ : Machine) (h : SendAt m₀) : Lands B img (SendQ m₀) m₀ :=
  E5R.Rmk.Uart.send_round m₀ h

theorem send_to_loop (m₀ : Machine) (h : SendAt m₀) (E : Extras m₀)
    (hpk : (ramRead m₀.ram 0x8002a798 .w).toNat ≤ bufLen) (hdc : discarding m₀.ram Session.dfr ≤ 1) :
    Lands B img (SendLoopQ m₀) m₀ :=
  E5R.Rmk.Uart.send_to_loop m₀ h E hpk hdc

theorem nonvacuous : ∃ m, SendAt m ∧ Extras m ∧ (ramRead m.ram 0x8002a798 .w).toNat ≤ bufLen ∧
    discarding m.ram Session.dfr ≤ 1 :=
  ⟨_, E5R.Rmk.Uart.w_sendLoop⟩

end E5R.RmkSend
