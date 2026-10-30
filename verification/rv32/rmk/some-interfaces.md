# Some-path interfaces: repair proposal after the 07a17e5 audit (main, 2026-10-30)

STATUS (update): the dispatch side is IMPLEMENTED in main's files (Session RecvOut s9; SessionInv Extras
svc/tx/txBase/txStride/fixNot, SomeAt.s9; SomeRound Kept +0x8002a200..0x8002a205, DispEnv svc/s9/msg/hdr,
`DispatchContract W`, `WAt`; witnesses in Deframer/SomeWitness.lean). EncEnv still awaits the peer.
Original status: PROPOSAL for agreement before shared-file edits. Until the repaired contracts are in place,
`some_round` / `some_pos` (07a17e5, bf1723f) are VACUOUS. On 3ecd81b (verify/isa-review branch,
review/SomeAudit.lean) the peer proved `dispatch_contract_false`, `encode_contract_false` and
`some_hyps_false`. Treat no receipt that pins `some_round` as safety progress.

## What the audit found, and why
- `DispEnv` / `SomeAt` leave the RynkService pointer word [0x8002a780] free. With 0 there, dispatch
  faults at 0x8000026e.
- `EncEnv` lets the `Kept` UART-struct bytes alias encode_frame's output buffer 0x8002a7b1..+7, and
  encode_frame overwrites them.

## Observed real layout (QEMU virt, pinned f39d833f ELF, idle at the session read; monitor `xp`)
- [0x8002a780] = 0x8002a4c0 (RynkService, = s7+0xf1, stored at 0x80003da6).
- [0x8002a784] = 0x8002a1c0 (RX Uart16550; +0x1c = 0x10000000, +0x20 = 1).
- [0x8002a788] = 0x8002a1e4 (TX Uart16550; +0x1c = 0x8002a200 holds 0x10000000, +0x20 holds 1).
- Service struct, 0x50 bytes at 0x8002a4c0, as words: 80026b7d 3 80026b80 c 8 6b6e7972 4b4d523a 8002a208
  4 0 80fffe58 1f 20 46434c4b 8002a3b4 1 0 1 0 1. It holds pointers into .rodata, statics and the
  executor stack.
- s9 at the Some point 0x80003e70 = s7+0x1b1 = msgA (set at 0x80003e5e). recv_step will export it.

## Session invariant additions (main owns SessionInv)
`Extras` gains:
- `svc` : [0x8002a780] = 0x8002a4c0, outside SW;
- `tx` : [0x8002a788] = 0x8002a1e4, with base/stride at +0x1c/+0x20 and those bytes outside SW;
- the flag byte is none of the bytes 0x8002a780..0x8002a78b.

`SomeAt` gains:
- `s9 = msgA`;
- frame length ≤ message length.

Initialization of all of these stays OPEN.

## DispatchContract, repaired (main owns it; it stays a NAMED, undischarged hypothesis)
`DispEnv` adds:
- svc word = 0x8002a4c0, and the service struct's 0x50 bytes in RAM, disjoint from the future, the
  message, the buffer and the frame;
- s9 = msgA and futMsg = msgA, with SomeAt's message facts;
- `W m.ram` for an explicit world predicate `W`. `W` stands for everything dispatch dereferences
  beyond the struct (keymap, the stack object at 0x80fffe58, ...). It is a parameter of
  `DispatchContract W`, and `some_round` takes `W m₀.ram` as a per-state hypothesis. `W` is open
  (initialization and preservation).

`Kept` for dispatch adds the service struct bytes and the TX pointer word.

## EncodeContract, repaired (the PEER proves it in new Encode/* modules; main consumes it)
`EncEnv` adds:
- s6 = s6v;
- [a1, a1+7) (output buffer), [a0, a0+8) (result slot) and the callee frame [sp-0x50, sp) are RAM,
  pairwise disjoint, and disjoint from every `Kept` byte;
- the Result argument byte at a5 = sp+0x140 is RAM. Its value is dispatch's byte or 8; the peer
  states which values serialize defines, and main proves the caller passes only those.

`EncRes` stays the same: tag byte at sp+0x40 is 1, or 0 with length ≤ 7. Peer, please propose exact
field names / statement. Main will not edit Encode/*.

## Send path (EXPORTER owns new Uart/SendRound.lean)
From 0x8000429e, through send_bytes (0x800042f8 -> 0x800098a6, proved: Uart.send_bytes) and
yield_now (0x80004320 -> 0x8001e14a), with explicit Pending/executor boundaries. send_bytes needs
`SendEnv` for the TX struct, which the new `Extras.tx` provides. Main will not edit SendRound.
