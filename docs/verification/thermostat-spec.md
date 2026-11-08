# Thermostat ELF proof specification and closure plan

Status: specification draft, 2026-11-08. This document fixes the intended claims
and work order; it is not a new Lean theorem or evidence that the joins are proved.
It takes precedence over historical instructions to keep adding local proofs.
The full-firmware objective remains; intermediate milestones must be labelled.

## Artifact and execution envelope

The executable is the existing h5i thermostat port, target
`riscv32imac-unknown-none-elf`, SHA-256
`bfb1bc620b30dc20aaa1090e91c327a0a86f1aa7de0c58e2043701ece8c45a18`.
Source reference: h5i `41eb6cc83776e146d29f36dd3c905b9cdb860d7b` with the retained
kernel export/inline attributes. Changing the executable requires a new reviewed
identity and correspondence proof, not silently updating this specification.

Assume the ELF loader establishes the specified image/RAM map and reset PC,
a single RV32 hart, no DMA or external RAM writers, and the existing e5r ISA,
platform and UART observation semantics. Reset code must establish interrupt
masking; it must not be assumed at an interior PC to justify the reset theorem.
UART reads/writes are byte events at the actual UART addresses. RX and TX arrays
are 2048 and 1024 bytes. Effective default head/body limits are 1024 bytes each;
head and encoded body storage must fit the receive buffer. The per-serve request
limit is 100. The fixed application key is `dev-key`; this is a functional demo,
not a claim of secret provisioning or cryptographic security.

## Observable specification

Use an independent pure specification, with no PCs, registers, Rust enum bytes
or assumptions that the desired parser/handler result has already occurred.
Reuse `Spec.lean` for thermostat state and commands. Review and reuse existing
pure parser/auth/decode/serialization specifications where they express the
following behavior; list exact names in the obligation map before implementation.

Initial state: setpoint=200, temperature=200 (tenths of a degree), mode=off,
heater=false and all four relays=false. For committed states:
`heater=true -> temperature<350` and `50<=setpoint<=300`.
For updated temperature/setpoint/mode, heater is false at temperature>=350;
otherwise it is false in off, true in heat, and temperature<setpoint in auto.
Read and rejected commands preserve state. Relay updates change only the chosen
relay; they preserve the already established heater invariant.

| Route | Authentication | Command/body |
| --- | --- | --- |
| GET /state | public | read snapshot |
| PUT /setpoint | required | trimmed signed i16 decimal; accept 50..300 |
| POST /temp | required | trimmed signed i16 decimal, full i16 domain |
| PUT /mode | required | trimmed `off`, `heat`, or `auto` |
| PUT /relay/{i} | required | decimal u8 index; trimmed `on` or `off` |

All HTTP writes, including temperature reports, require authentication. Select
Authorization by the existing specified header lookup rule; its value must be
exactly `Bearer dev-key`. Missing/bad credentials yield 401 before body decoding.
Malformed command bodies yield 400; relay parameter decoding/range beyond u8
yields 404; decoded relay indices 4..255 yield kernel 404; out-of-range setpoints
yield 422. A non-admin configurable typed command yields kernel 403, although
successful HTTP authentication supplies the fixed admin principal. Route
not-found and wrong-method behavior must be specified separately (404/405),
including path/query splitting, HEAD handling and route precedence. Do not infer
these details merely from route names; close their pure-spec review obligation.

Successful commands yield 200 and the exact JSON snapshot with fields in order:
`setpoint_dc`, `temp_dc`, `heater`, `relays`, `mode`. Booleans, signed decimals,
mode strings, kernel error bodies, empty early-refusal bodies, Content-Length,
content type, status line and all emitted header bytes must match the reviewed
serializer specification. A JSON-only equality is insufficient. No state changes
are allowed on auth/decode/router/parser refusal. Transaction boundaries expose
the committed state, borrow=0, and the invariant; this does not assert atomic
invariants between individual RAM stores.

Parser behavior must have an explicit acceptance/rejection specification,
including request-line/version, Host, Content-Length/Transfer-Encoding conflicts,
duplicate headers, framing, limits, chunk extensions/trailers and malformed
input. Existing parser spec modules are candidates, not an automatic claim of
HTTP standards compliance. Unresolved policy details must be settled and recorded
before proving their binary branches. An implementation/spec mismatch is a bug
or an explicitly reviewed policy change, not a reason to redefine the spec.

Connection closure is HTTP/1.0, the 100th request within a serve call, or any
case-insensitive Connection header with any comma-separated, ASCII-trimmed token
equal to `close`, plus response/parser-requested closure. UART has no TCP close:
state precisely which serve return, counter reset and buffer reset this causes
before the next outer-loop serve. Retained unread bytes and any buffer compaction
must be accounted for; never assume `filled=used` without deriving it from the
one-byte UART reader and the relevant control path.

## Target statements

Names below are proposed proof interfaces, not existing theorem declarations.

**T1: one transaction from reset.** For every request in the explicitly defined
fixed-length HTTP/1.1 API domain (including absent/bad credentials and malformed
command bodies), and every allowed finite UART schedule delivering its exact
bytes and permitting all response writes, execution from reset reaches the
transaction-complete boundary. Accepted RX bytes, ordered TX bytes and committed
RAM snapshot equal the pure spec; the state invariant and borrow=0 hold. Derive
all parser, layout, auth, decoder and handler preconditions along this execution.
T1 is the first integration milestone, not the whole-firmware result. Its request
domain must be a pure predicate covering all five routes and unbounded values
within the stated buffer/domain limits, not a list of test fixtures.

**T2: repeated transactions.** Extend T1 to arbitrary finite sequences within
this domain, with the actual serve/outer-loop behavior, close conditions,
request counter reset, preserved App state and exact unread-buffer accounting.
Prove the concrete loop invariant and the induction step; do not merely iterate
an interior engine contract whose preconditions the caller has not established.

**T3: full input-domain safety and correspondence.** Extend the boundary theorem
to every finite input byte stream, including unsupported methods/routes,
malformed/oversized heads and bodies, chunked framing, pipelining, incomplete
requests and all rejection/close/restart paths. For every finite execution prefix
under the admitted platform environment, execution remains in specified code,
RAM/stack bounds and device accesses, with no fault/unsupported-instruction or
panic escape. Observations refine a pure stream machine; partial input/output
prefixes and intermediate transaction states must be represented explicitly.
Committed-state invariants are asserted only at the specified boundaries.

Safety is separate from liveness. Infinite silence or perpetual TX-not-ready
cannot imply response completion. Conditional progress quantifies over finite
valid readiness/data schedules, or a separately defined and justified fairness
condition. It must not assume the response, desired final state, final PC, or
successful internal preconditions. RX/TX schedules must respect the selected UART
model; arbitrary oracle responses do not automatically establish physical FIFO
behavior. Provide satisfying executions/fixtures for theorem premises.

Physical PWM/LED behavior, deadlines, analog temperature safety, multi-hart
concurrency, constant-time security and all possible compiler builds are outside
these claims. QEMU running this same ELF is integration evidence; it is not a
formal proof of QEMU or of physical devices. Renode is optional visualization
only unless a separate peripheral specification and implementation are added.

## Obligation map and completion gates

Initial evidence below is a navigation aid; exact theorem names, assumptions,
source hashes and current audit status must be checked by the worker. Historical
counts or compilation-only prototypes do not discharge a gate.

| ID | Required join | Existing starting points | Current gap |
| --- | --- | --- | --- |
| G0 | pure HTTP/stream spec and explicit T1 domain | Spec, parser/auth/decode/serializer spec modules | review policies; state theorem interfaces |
| G1 | reset -> initialized receive boundary | reset/App/UART contracts | select strongest composed interface |
| G2 | received bytes -> parsed Request and actual routing inputs | HeadColdParser, MainLengthReset, MainRequestInputs prototypes | connect checked layouts and preserve App/RX |
| G3 | Request -> route, auth, typed command or exact refusal | header/auth/decoder/write/Read contracts | actual caller registers/stack/ABI joins |
| G4 | typed execution -> committed state and response object | Engine.contract_inv, ReadEngine, WriteSuccess | establish all branch preconditions from G3 |
| G5 | response object -> exact UART reply and transaction boundary | Send/UART contracts | preserve state and connect real continuation |
| G6 | completed boundary -> next transaction/serve | close/request-count/buffer work | concrete loop invariant and induction |
| G7 | all malformed/chunked/partial input branches | local parser/error contracts | enumerate branch coverage and close global safety |
| G8 | reproducible final evidence | e5r audit, negative controls, QEMU runner | current hashes, full replay, same-ELF run, commit/push |

T1 requires G0..G5 and its G8 evidence; T2 adds G6; T3 adds G7 and full-domain G8.
Completion requires the actual composed Lean statements and their audited proofs,
not this table, increasing theorem counts, or only concrete witness executions.
No percentage is assigned until the gates have explicit accepted evidence.

## Work and cost policy

1. Checkpoint existing work. Do not delete prototypes or alter frozen audit inputs.
2. Before further helper expansion, fill a separate closure map with exact
   declaration names, premise/conclusion mismatches and the next required join.
   Record locally checked, independently audited and stale evidence separately.
3. Close T1 first. Implement only a missing premise/lemma identified by a gate.
   If a helper does not discharge a named obligation, defer it.
4. Reuse stronger contracts to derive weaker ones. Share normal/Quiet execution
   reasoning where sound; deterministic steps alone do not prove absence of MMIO.
   Avoid a broad rewrite of the existing proof tree before an integration theorem.
5. During development compile changed modules and affected import dependants.
   Batch full independent replays at integration milestones. Do not launch a new
   chain of full audits for every small helper batch; let current frozen jobs
   finish safely. Never weaken final axiom/fidelity/replay checks to reduce cost.
6. At a checkpoint, report gates closed/open, new proof source size, verification
   time and available token/cost evidence. Review any unexpected expansion before
   spending another open-ended proof phase. CPU time is not API spend.
7. Commit coherent, reviewed milestones and push the authorized feature branch
   without force. Record remote SHA. Do not include ignored build artifacts or
   claim work is committed/pushed before verifying Git state.
