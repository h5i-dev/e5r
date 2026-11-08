# Thermostat closure: G0–G8

Current 2026-11-08 21:22:46 UTC. The fixed specification at commit c00e933 and pinned ELF are
unchanged. **T1 has a local compiled declaration, independent replay pending**;
whole firmware is OPEN. All names below have prefix `E5R.Thermostat.`.
The older review/log retained below is historical and is superseded by this table.

| Goal | Exact current declarations / actual boundary | Remaining mismatch or obligation |
| --- | --- | --- |
| G0 | `ApiRequestSpec.Fixed11`, `.head`, `.reply`; `ApiFixedHead.accepted`; `ApiHeadPrefix.incomplete`; `ApiConsume.exact_head/delivered`; `ApiRouting.method_case/path`; `ApiReplySpec.close/invariant` | LOCAL structural byte grammar derives parser acceptance/first-complete-prefix/length/method/path. No desired parse result or machine layout is a domain field. Full stream evaluator outside T1 remains G7. |
| G1 | Audited `MainHeaderResetQuiet.safe_contract`, `Boot.contract/mask`, `Interrupt.reach_masked/no_irq`; reused in `Firmware.one_request` | Reset PC0, hardware-reset MIE=false, mpp0/3, pinned map/image, single hart/no external writers and64KiB allocation are explicit. Masking is derived along actual bootstrap, not assumed at an interior PC. |
| G2 | `MainNextLengthReset.contract` audited to0a9a; local `MainRequestBuildReset.contract`, `MainCloseRequestReset.contract_routes`, then `Firmware.one_request` | Pure head/framing premises are now discharged in T1. Exact bytes, actual Request offsets/close/table/futures derived. Independent replay of staged joins pending. |
| G3 | Local `MainReadReset.contract`, `MainTempReset.contract`, `MainSetpointReset.contract`, `MainModeReset.contract`, `MainRelayReset.contract`; composed by `Firmware.one_request` | All5real route traversals/methods/captures/auth/decode/caller layouts derived from the T1 bytes. Relay arbitrary nonempty visible segment excludes slash and question mark because this is a path segment before query splitting. No auth/decode/kernel-outcome premise. |
| G4 | Audited `Acquire.contract_inv`, `Engine.contract_inv`, `ReadEngine.contract_inv`; local `MainApiWriteCaller.transaction` and T1 | Reset App supplies borrow availability; actual borrow acquisition/persistence/ABI derived. T1 concludes exact pure committed App, borrow0 and actualRAM invariant. No invariant at each intermediate store or physical-actuator claim. |
| G5 | Audited `MainWriteTransactions.success_exact/error_exact`, `ReadRound.contract_exact`; local `MainWriteReturnJoin.contract_exact`, generic refusal joins and `Firmware.one_request` | Exact status/MIME/Content-Length/header and payload UART writes, all API outcomes; real completion17be/0978 selected by Connection policy. Independent T1 replay pending. |
| G6 | Existing `MainCompletionKeep/Close.contract` stop at17be/0978 | OPEN: actual keep→compaction56a0/5310 (or derived zero-leftover)→next RX; close→serve/outer restart, count100, App/freeborrow/live stack and unread-byte recurrence. T1 does not imply this. |
| G7 | Existing `HeadColdParser.contract`, `MainChunkStreaming.contract`, `Main*WaitSafety.fragment_safety` are local pieces | OPEN: malformed/empty/chunk/reject/404/405/HEAD/partial/pipelined paths joined to one stream invariant and every finite actual prefix. Infinite silence/not-ready implies no unconditional progress. |
| G8 | Baseline9047/all2142independent replays/all874controls/standard3axioms; lastCURRENT21:13UTC | T1 ten-source fresh compile +16semantic negatives PASS40.519270638s, standard3axioms; independent T1 replay pending. Consolidate its dependency closure once; automatic audit chains stay stopped. |

Actual T1 declaration, `Firmware.one_request` (local source `build/FirmwareOneRequest.lean`):

```text
for every r : ApiRequestSpec.Fixed11, actual reset Core/RAM envelope,
wire whose request prefix is exactly r.bytes, and finite valid RX/TX schedules,
there exist actual instruction count n, final Core d and RAM after such that
  Observed.Steps pinnedBoard pinnedImage n (resetCore, resetRAM) (d,after)
    exact-schedule-read-log (TX events of the pure HTTP headers and payload),
  acceptedRX = r.bytes,
  d.pc = if pureClose r then 0x80000978 else 0x800017be,
  d.sp=0x80ffeb90, d.fp=0x80fff814, d.mie=false,
  AppState.At after (r.reply Spec.initial).state,
  borrow(after)=0, Spec.Inv (r.reply Spec.initial).state,
  Engine.InvariantAt after 0x80ffebbc.
```

No parser-success/framing/method/path/caller/auth/decode/transition result is
an outer premise. The structural domain covers arbitrary bounded values, not
fixtures. Environment assumptions are conditional progress premises. This theorem
ends at one completed transaction; reusable loop closure and unconditional
whole-prefix safety remain separate. No completion percentage/ETA is justified.
Concise operational map: `/root/e5r-agent-runs/thermostat-proof/CLOSURE.md`.

## Historical review and evidence ledger

## Evidence categories

- **A — finalized independent audit:**9,047 theorems,2,142 modules
  (2,134 proof+8 model/image), all independently replayed; all874 controls passed
  (872 wrong proofs+2 wrong actual UART/HTTP expectations). Runtime
  1767.912199677s,peakstage1388MiB;2116 compilation stages reused, no kernel
  replay skipped. Only `propext`, `Classical.choice`, `Quot.sound`.
  Final `CURRENT` and all2154 frozen hashes passed. Archive:
  `verification/rv32/build/thermostat-next-length-finalized.json`.
- **B — newly finalized Next boundary:** `MainNextLengthReset.contract` reaches
  actual fixed-length Next dispatch PC`0x80000a9a`; included in A. There is no
  active audit/control job. The previous8947/2116/all847 archive remains history.
- **C — checked, staged, not independently audited:** 147 additional modules:
  serve-next 43, target/query 28, method 33, Request construction 43. Their
  fresh positive sweeps and semantic negative sweeps passed, but the four pending
  audit-launch/finalizer watchers were stopped. Sources, stages and controls
  remain intact. They are not registered in the current 2,142-module job.
- **D — individually compiled prototypes only:** 57 close/input modules in
  the ignored build directory, including `MainRequestInputs` and the complete
  nonempty value-token loop. No fresh aggregate sweep, negative suite,
  registration or independent replay for this group. It is not audited evidence.

Below, `E5R.Thermostat.` is the prefix of every application declaration unless
another namespace is written. Module filenames alone are not declarations:
for example `MainWriteTransactionsExact.lean` declares
`MainWriteTransactions.success_exact` and `.error_exact`.

## G0 — pure specification and domain: OPEN, review required

Existing pure definitions that can be reused:

| Exact declaration | Meaning and limit |
| --- | --- |
| `Spec.initial`, `Spec.transition`, `Spec.commit`, `Spec.Inv`, `Spec.commit_inv` | Full typed thermostat domains and committed-state invariant. `reportTemp` itself does not require admin; HTTP authentication must still gate **all** four write routes. |
| `HttpRequestSpec.requestLine`, `.headerLine`, `.addHeader`, `.parseHead`, `.chunkStep`; `HttpRequestBytes.parse` | Independent byte/parser policy, not general HTTP compliance. Full parser/loop composition is separate. |
| `HeaderSpec.lookup`, `.find`, `.lookup_find` | First matching Authorization field, case-insensitive name; later duplicates do not override it. Header values are the parser's OWS-trimmed slices. |
| `AuthSpec.token`, `.authorized` | Case-sensitive `Bearer ` prefix and exact remaining key bytes. Outer HTTP OWS normalization precedes this check. |
| `DecimalSpec.parse`; `WireSpec.parseU32`, `.decode`, `.relay` | Signed i16 and relay parameter/body decoding. `WireSpec.decode`'s fallback assumes routing supplied a relay parameter; it is **not** a router specification. |
| `ReplyJson.snapshot`, `.errorStatus`, `.errorBody`; `ResponseHeadSpec.bytes`, `.body`, `.encode` | Exact ordered JSON, error payloads/statuses and entire HTTP response framing. `ErrorLiterals.pointer` is a ROM address and must not enter the pure evaluator. |
| `MainQuerySpec.position`, `.path`, `.query`; `MainMethodSpec.decode` | Pure first-`?` split and case-sensitive method classification, C status. Enum tags belong in the correspondence proof, not the observable spec. |
| `MainCloseSpec.hasClose`, `.wantsClose`, `.mustClose` | D status: any matching Connection field, any comma token, ASCII trim/case folding; HTTP/1.0 or count 100 forces closure. Not the first-header rule used for Authorization. |

Policies already visible in the independent parser/source, to record explicitly
when G0 is accepted:

- Request line is `method SP origin-form SP HTTP-version`, CRLF terminated;
  HTTP/1.1 requires Host. Duplicate Host is 400; maximum 16 header fields is
  enforced. Duplicate Content-Length is 400 even if identical; CL/TE conflict
  is 400. CL and TE trailing OWS is rejected. Unsupported transfer coding is
  501; TE on HTTP/1.0 is 400. Other headers, including Authorization, can repeat.
- Chunk sizes are 1–8 hexadecimal digits followed by CRLF; chunk extensions and
  nonempty trailers are outside this parser's accepted syntax and reject with
  400. Body overflow is 413. These are this application's policies, not a claim
  to accept every standards-conforming chunked request.
- The original router tries routes in registration order. The first completed
  match wins; a matching path with no matching method produces 405, a path
  matching none produces 404. HEAD invokes a GET handler and suppresses its
  body while retaining representation Content-Length. A parameter matches one
  nonempty segment. Query splitting occurs before routing; no percent-decoding
  behavior is proved by the current path decoder contracts.
- Signed input grammar is `-?[0-9]{1,5}` within i16, after `TrimMath.trim`.
  A plus sign is invalid. Relay parameters use 1–10 digits, checked u32, then
  u8; body decoding precedes the kernel's 0–3 relay check. Thus valid credentials
  plus index 5 plus malformed body yields 400, not a preemptive kernel 404.
  Bad credentials precede both parameter/body decoding and yield 401.
- Body trim uses bytes 9/10/12/13/32, excluding vertical tab. Header OWS uses
  only space/tab. These must not be conflated.

The router observations above were read from the application's own sources:
`/root/h5i/crates/h5i-app-embedded/src/lib.rs` (`Routes::dispatch`, `serve`,
`wants_close`) and `src/path.rs`, and
`/root/h5i/examples/embedded/thermostat/app/src/lib.rs` (`Wire`, `router`).
There is no existing single pure HTTP transaction/stream evaluator covering
all these policies. G0 still needs that reviewed definition and policy lemmas.

## G1 — reset to initialized receive: reusable A contract; envelope mismatch

Use `MainHeaderResetQuiet.contract` and `.safe_contract`
([source](../../verification/rv32/Projects/thermostat/MainHeaderResetQuiet.lean)).
They execute **2,550 actual instructions**, reset PC `0x80000000` to first
receive poll `0x80000ba2`, with empty device-read/output logs, and establish
`MainHeaderFirstPoll.Ready`: actual App initial snapshot/free borrow/key/admin
metadata, SP/FP/UART registers, allocated stack, limits and empty receive layout.
`MainInitTwo.contract` additionally exports the real `x18=2` used downstream.

Assumption mismatch: the safety/IRQ-closed theorem requires **reset**
`c.mie_=false`, `c.mpp=0 ∨ c.mpp=3`, and
`Memory.Block UartPlatform.board 0x80ff0000 65536`.
`Boot.mask` proves the actual two CSR writes and `Boot.contract` proves the
11-instruction bootstrap; no interior masking premise needs to be invented.
However, actual IRQ exclusion before the first CSR cannot follow from an
arbitrary initial interrupt-enabled machine. The reviewed reset envelope must
state the reset hardware/loader fact, or the theorem needs a weaker justified
initial IRQ-disable condition. Do not silently discharge it by an interior PC.

`Interrupt.decoded_safe`, `.step_masked`, `.reach_masked`, `.no_irq` prove global
mask preservation over the pinned image, including aligned interior halfwords.
They do **not** prove absence of faults, unsupported execution or panic paths.

## G2 — bytes to actual Request: OPEN integration, A/B/C/D pieces

| Exact declaration / status | Established boundary | Remaining mismatch |
| --- | --- | --- |
| `HeadColdParser.contract`, `.safe_contract` — A | Actual `parse_head`, arbitrary slice ≤2048, exact `HttpRequestBytes.parse input 1024 1024`, saved ABI/App/RX frame | Interior entry assumes actual input bytes/layout, stack, limits and ROM/RAM exclusion. |
| `MainHeaderResetStream.contract`, `.terminal` — A | Reset to header stream boundary; exact accepted RBR bytes and pure parser result | `.terminal` takes a pure complete-input fact. Derive it from the proposed grammar, not from desired execution. |
| `MainHeaderResetBody.contract` — A | Reset to actual body dispatch, copied Head/slice bounds | Takes `(consume wire fuel []).result=.done head`. This must become a lemma from domain bytes and first-complete-prefix behavior. |
| `MainLengthReset.contract`, `MainLengthResetEnd.contract` — A | Complete fixed body, including zero length, actual end register | Both still take pure head acceptance and `.length amount`; schedule validity and exact missing-byte count remain explicit. |
| `MainNextLengthReset.contract` — B | Reset through 407-instruction C98→A9A dispatch/copy, actual `MainNextLength.Ready` | Included in finalized A. Still takes accepted head and framing facts. |
| `MainServeNextReset.contract`, `MainRequestMethodResetPayload.contract`, `MainRequestBuildReset.contract` — C | Last reaches `0x80001246`, actual 376-byte Request slot, method/path/query/body, served=1, App/RX invariant | Full C dependency closure unregistered. Exact declarations checked in source; not in A report. |
| `MainRequestInputs.headers`, `.path`; `MainRequestSpans.raw_span`, `.path_span`, `.query_span`, `.body_span` — D | Derive `Header.Pre`, `PathDispatch.PathAt` and real byte spans from the built Request | Do not establish router parameter writes, handler futures, routing PC or ABI joins. |

The old parser-future `MainHeaderLayout` is overwritten by Request construction.
Use `MainTransactionStable.At` and `MainRequestStored.At` across the later joins.
The 376-byte Request slot includes three arbitrary tail-padding bytes; do not
replace arbitrary padding with zero. Method and pointer registers also change
roles at the later main setup.

T1 requires deriving accepted head/framing and the exact first complete head
prefix from its grammar; then derive body completion and `filled=used=wire.length`
from the one-byte reader. The statement must not assume parser success or
prebuilt `Ready` at an interior PC.

## G3 — Request to route/auth/typed result: OPEN, main missing join

Existing A declarations:

- `Header.contract`, `.bytes_contract`; `RequestAuth.contract_quiet` and
  `RequestAuthEnd.contract`; `Authorize.contract_quiet` implement actual lookup
  and Bearer authentication under object/slice/separation prerequisites.
- `PathDispatch.contract_quiet`, `Wire.contract_quiet`,
  `DecodeInput.contract_quiet`, `RequestTight.contract_io_quiet` connect actual
  decoding to `WireSpec.decode` after valid Request/parameter layouts are given.
  `PathDispatch` is the **write decoder's** path dispatch at `0x80001fb4`,
  not the main HTTP method/path router.
- `MainWriteInput.establishes` begins at actual main write call `0x8000195a`.
  `MainWriteInput.Ready` requires actual future fields at `0x80fffa2c`, Request
  fields/first parameter, admin App metadata and disjointness from handler stack
  and future. The upstream `MainRequestBuild.Ready` does not establish those.
- `WriteRefusal.contract_inv` returns an empty 401 response for failed auth.
  `WriteDecodeRefusal.contract_inv` returns empty 400/404 for malformed decoded
  input. They preserve committed state/free borrow and restore the caller ABI.
  They are Det/closed contracts, not existing Quiet wrappers.
- `ReadAcquire.Pre` starts at separate actual main PC `0x80001a08`, assuming
  engine pointer `x9`, public actor byte at `0x80fffe68`, typed Read storage at
  `0x80fffb10`, snapshot/free borrow and real stack. These are not yet derived
  from a parsed GET `/state` and the outer router.

The general pre-router close edge is now LOCAL complete:

- `MainWantsClose.contract`: actual PC`0x800023f2`, count/slice checks, every
  header including duplicates, actual name/value loops, eleven callee saves,
  stack restoration and RET; exact `MainCloseSpec.wantsClose` Boolean.
- `MainCloseScanned.contract`: constructed Request PC`0x80001246` through
  actual call and returned close flag, actual capacity guard and flag store to
  PC`0x8000129a`. Its actual48-byte stack allocation and Request/raw separation
  derive from `MainRequestBuild.Ready`; no separate acquired/valid layout premise
  is added. App, RX, Request, serve metadata, ABI and committed Inv are preserved.
- `MainCloseRequest.contract`: both the general HTTP1.1 scan and existing forced
  HTTP1.0/request-limit branches share `MainCloseReady.At` at PC`0x8000129a`.
- `MainCloseRequestReset.contract`: composes the whole reset/UART/header/body/
  Request chain with this general close path. It still explicitly assumes the
  pure consumed-head acceptance/framing and finite schedules; G0 must derive
  these from its reviewed pure domain. It does not reach a response.
- `MainCloseRequestWitness.execution`: four satisfying actual reset/UART
  HTTP1.1 examples reach router entry for no Connection, mixed-case close,
  near-miss tokens, and a later duplicate Connection containing close. Queries
  are retained upstream and removed from actual path layout by the existing chain.

Sixteen fresh positive compilations and17 semantic negative controls passed
in92.252363327s with stable source hashes; no independent replay/new audit job.
A whole nested `consume` evaluation exceeded the1500MiB Lean cap; the four
fixture checks now share kernel-checked byte-prefix parser/consume equalities.
They compile within the unchanged cap, without native evaluation or extra axioms.
The concrete witnesses are evidence of satisfying premises, not the T1 domain.

The initialized-router layout edge is now LOCAL connected. Exact declarations:
`MainHeaderFirstPoll.reset_routes`, `HeadFutureChecked.contract_routes`,
`HeadFutureLine.contract_routes`, `HeadFutureInput.contract_routes`,
`HeadColdFutureComplete.contract_routes`, `HeadColdFuture.contract_routes`,
`MainHeadParser.contract_routes`, `MainHeaderAppendServe.contract_routes`,
`MainHeaderLoopRegs.contract_routes`, `MainHeaderStreamRegs.contract_routes`,
`MainHeaderResetBank.contract_routes`, `MainHeaderResetBodyBank.contract_routes`,
`MainLengthEnterRegs.contract_routes`, `MainLengthLoopRegs.contract_routes`,
`MainLengthStreamRegs.contract_routes`, `MainLengthBodyRegs.contract_routes`,
`MainLengthResetBank.contract_routes`, `MainNextLengthResetBank.contract_routes`,
`MainServeNextResetPayload.contract_routes`,
`MainRequestMethodResetPayload.contract_routes`,
`MainRequestBuildReset.contract_routes`, `MainCloseScanned.contract_routes`,
`MainCloseRequest.contract_routes`, and
**`MainCloseRequestReset.contract_routes`**. The last starts at actual reset,
uses the real UART/header/body/Next/Request/close chain and reaches main router
entry PC`0x8000129a` with `MainCloseReady.At` AND `MainRouterTable.At`.
The table is derived from startup, not postulated at that PC or at reset.

`MainRouterTable.At` extracts exactly the initialized60-byte route storage from
`InitRoutes.Layout`; `.initialized` and `.preserve` transport this view across
explicit region equalities. It omits the unrelated initial RX-capacity scratch
word. Existing bank/serve/body-end facts are retained in the stronger composed
interfaces, rather than dropped and later assumed. The six parser companions
use existing checked region contracts; no ISA/platform model or trusted summary
is added. `MainCloseRequestWitness.execution_routes` supplies four concrete
reset/UART witnesses with correct initialized table and selected close flag.

Nine fresh positive compilations and9 semantic negative controls passed in
76.895273490s, with unchanged hashes. The quantified root and concrete witness
both report exactly `propext`, `Classical.choice`, `Quot.sound`. This is LOCAL
Lean checking, not independent replay. Source:1271lines/104854bytes across9
ignored modules. Two earlier weaker header/body frame prototypes are preserved,
individually recompiled, and excluded from this stronger integration dependency
set. Mixed canonical/build imports were rejected by Lean; current prototypes
use the existing staged import graph consistently, with no duplicate-declaration
bypass. A slow proof-conversion development compile was interrupted after a
known proof-local type mismatch; explicit byte-region/address normalization made
the corrected Request composition compile normally. No audit was interrupted.

Next G3 edge: actual main PC`0x8000129a` constructs route futures, actual path
matcher PC`0x8000283a` and method branches select a handler, and the proof must
derive all `MainWriteInput.Ready`/`ReadAcquire.Pre` fields, including real relay
capture and separate Read actor/typed-command stores.220actual fetch expectations
for these named regions are locally checked in `MainRouterCode`; this alone is
not a routing contract. The reset theorem still takes pure consumed-head
acceptance/framing/schedule premises. G0 must derive those from its reviewed pure
domain. It does not reach a UART reply or discharge T1/G3 as a whole.

Observed application policy for the proposed pure router review: routes are
tried in registration order; a matched handler wins; HEAD uses GET but suppresses
its response body; a matched path with wrong method yields405 if no handler
wins, otherwise404. Literal segments compare exactly; `{...}` matches one
nonempty segment, with at most4 captured spans. This comes from the original
application's `Routes::dispatch` and `path::matches`, not from decoder path
contracts. The binary correspondence remains open; no spec document is edited.

## G4 — typed execution to committed state/response: reusable A, caller open

- `Engine.contract_inv`: real acquired-borrow engine body at `0x80000622`,
  ≤171 instructions, exact persisted commit/reply and invariant/free borrow.
  It assumes `Engine.Pre.borrowed=-1` and real typed/actor layouts.
- `Acquire.contract_inv`: actual acquisition from `0x80000614`, ≤175 including
  engine, deriving acquired borrow from zero. `Acquire.unavailable` covers the
  unavailable branch; the reset-to-T1 caller must derive availability from App.
- `ReadEngine.contract_inv`: separate actual Read call-site execution and RAM
  persistence/release; use `ReadAcquire.Pre`, not a write-layout Read command.
- `WriteSuccess.contract_inv`: authenticated fresh handler through response,
  complete caller ABI; `MainWriteSuccess.contract_quiet` and
  `MainWriteError.contract_quiet` include actual main-call handling.
- `Spec.commit_inv` is the pure invariant preservation theorem. Assertions
  about actual RAM require these persistence/frame joins as well.

No global atomic invariant follows between sequential field stores or borrow
release. T1 asserts it only at the transaction-complete boundary. Setpoint 422
and decoded relay 4..255→404 must be reached by the actual upstream decoder;
401/400/parameter-404 do not execute a fabricated typed kernel command.

## G5 — response to exact UART and completed boundary: OPEN, strong A suffixes

`Send.contract` and `Send.projection` cover actual send/RET and exact ordered
header/body UART writes under `SendInput.Pre` and finite per-byte readiness
slots. `ResponseHead.contract`, `UartWriteAll.contract`, `UartTxLoop.contract`
provide the underlying actual serializers/transmission. Status, MIME, payload,
object freshness, capacity, disjointness and ABI values must come from the
handler/route result, not be postulated in the reset theorem.

`MainWriteTransactions.success_exact` and `.error_exact` are strong existing A
suffixes: start `0x8000195a`, perform actual auth/decoding/kernel handling, exact
JSON **and complete HTTP/UART**, finish `0x800017be` on keep-alive or `0x80000978`
on close, preserving App/invariant/RX. But they require `hallow=true`,
`hdecode=.ok cmd` and the pure kernel result plus main future/metadata layouts.
These pure case facts must be derived/exhaustively split in the outer proof.

`ReadRound.contract_exact` covers separate Read acquisition through exact
HTTP/UART to the same completed main boundary. It still assumes the G3 Read
layout and main capacities/close/method fields.

New LOCAL connection for mandatory T1 failures:
`MainStatusAuth401.contract_exact` covers bad/missing auth (401), and
`MainStatusDecodeReply.contract_exact` covers authenticated decoder errors
(400/parameter404), from actual main call PC`0x8000195a` through handler RET,
actual empty-MIME/body response construction, full HTTP/UART emission and actual
completion PC`0x800017be`/`0x80000978`. `MainStatusDecodeReply.status_cases`
derives400/404 from the pure decoder result; valid status is not a new premise.
`MainStatusReply.contract_exact` is the shared concrete empty-status sender
composition. These reuse existing checked Quiet instruction and sender contracts;
no absence of MMIO reads is inferred from deterministic execution alone.

Nine fresh positive compilations and13 semantic negative controls passed in
124.845948386s; source hashes were checked unchanged. Concrete
`MainStatusAuth401Witness.execution` and `MainStatusDecode400Witness.execution`
establish satisfying call-boundary premises for valid POST /temp with bad/good
credentials and malformed `auto` body, respectively, for both close flags.
These are interior-call witnesses, not reset/router proofs. All nine sources
remain ignored build prototypes, unregistered and not independently replayed.
Both quantified suffixes still require `MainWriteInput.Ready`, main capacities,
close fields and auth/decode case facts. G3 must derive these from Request/router
execution; that is the next critical edge. JSON suffixes are not used for empty
refusals because they emit different Content-Type bytes.

T1 stops at `0x800017be`, after the last response write and actual completion
dispatch, before buffer compaction. It does not claim the next transaction.

## G6 — next transaction/serve: OPEN, deferred beyond T1

`MainCompletion.contract`, `MainCompletionKeep.contract` and
`MainCompletionClose.contract` cover the actual completion branches to
`0x800017be`/`0x80000978`. `MainWriteRound.contract_exact` and
`ReadRound.contract_exact` establish completed App/invariant data, not a next
receive precondition. `MainCloseSpec.mustClose` and D `MainCloseForced.contract`
address closure pieces, not the full serve/outer-loop induction.

Remaining: Request count/buffer reset at actual serve return, retained bytes,
App and borrow availability, bounded live frames, next Receive invariant and
inductive step. Actual overlapping `copy_within` at the keep-alive path calls
`memmove` (`0x800056a0`/`0x80005310`); existing non-overlapping memcpy contracts
cannot be substituted. For a reachable zero-length copy, `filled=used` must
first be derived for that path. T1's canonical single-request observation ends
before this call; T2 must close it or prove its zero-length specialization.

## G7 — full malformed/chunked/partial domain: OPEN, deferred beyond T1

A `HeadColdParser.contract` already covers arbitrary ≤2048-byte parser slices,
including rejects/incomplete heads. `MainHeaderResetStream.contract` connects
actual UART header prefixes. `MainChunkStreaming.contract` covers actual
in-place chunk-body streaming given `MainChunkLoopInvariant.At`, unread/decoded
views, finite RX validity and pure completion. Its input invariant is not yet
established from reset on the chunked branch; decoded RAM differs from raw
wire bytes, so the fixed-body whole-RX equality cannot be reused unchanged.

`MainHeaderWaitSafety.fragment_safety`, `MainLengthWaitSafety.fragment_safety`,
`MainChunkWaitSafety.fragment_safety` prove unconditional local wait safety.
`Blocking.no_response_from_reset` and `.arbitrarily_long_no_output` exhibit
why silence cannot imply unconditional progress. `Observed.reach_erase` and
`.reach_complete`, and `Observed.uart_erase`/`.uart_complete`, connect the
instrumented trace semantics to the original platform semantics.

Remaining: pure stream state machine with partial RX/TX, all parser rejection
response/restart branches, empty framing, chunk init/terminal/common Request
joins, oversized paths, router 404/405/HEAD, arbitrary Connection fields,
pipelined/retained bytes, and a global finite-prefix invariant excluding every
fault/unsupported/panic escape. IRQ exclusion alone does not close this gate.

## G8 — reproducible evidence: A baseline closed; T1 evidence OPEN

The pinned ELF remains
`bfb1bc620b30dc20aaa1090e91c327a0a86f1aa7de0c58e2043701ece8c45a18`.
Source identity and model/ISA/loader assumptions must accompany the final T1
statement. The current job/result cannot certify unregistered C/D declarations.
The active B audit is allowed to finish; no further audit chain is authorized
by this review. Historical same-ELF QEMU 8.2.2 evidence (336 persistent HTTP
cases plus 42 fresh cases) is retained but was not rerun for this review.

Final T1 validation must freeze its actual dependency closure; prove no
sorry/admit/new axioms; replay every proof/model module independently; pass
meaningful semantic negative controls including wrong refusal headers/RX/TX;
verify final `CURRENT` and source/ELF hashes; run the same-ELF UART HTTP oracle;
then commit/push a reviewed coherent milestone without ignored build products.
The spec-only remote commit is not a commit of these inherited proof changes.

## Proposed pure T1 domain — review decision D1

Use a structured **byte** request record, and define `T1Domain` as membership
in the following generated wire language. These are proposed names, not existing
Lean definitions. It is not a fixture list and contains no PC/register/RAM/enum
encoding or assumed parser/handler outcome.

1. Endpoint and exact method/path are one of GET `/state`, PUT `/setpoint`,
   POST `/temp`, PUT `/mode`, PUT `/relay/` ++ `parameter`. A relay parameter
   is any nonempty visible-ASCII segment excluding `/` and `?`; it need not be
   a number, fit u32/u8, or be 0–3. No query suffix in initial T1.
2. Body is **every** byte list of length 0..1024, including NUL, CR/LF,
   whitespace-only data and malformed commands. GET body bytes are consumed and
   ignored by Read. Every head includes explicit Content-Length, even zero.
3. Wire head is exactly `method SP path SP HTTP/1.1 CRLF`,
   `Host: thermostat CRLF`, `Content-Length: <canonical decimal body length> CRLF`,
   followed by an arbitrary ordered list of 0..14 `Authorization: <value> CRLF`
   fields, then CRLF. Values are arbitrary field bytes (HTAB or bytes ≥32 except
   DEL), subject to the head limit; they may be empty or have HTTP OWS at edges.
   The pure parser's OWS-normalized first matching value is authenticated.
4. Head length ≤1024 and total head+body ≤2048. The latter follows from the
   two limits but remains explicit in the byte-domain definition. Wire input is
   exactly this one request, with no appended pipelined bytes.
5. No Connection header, HTTP/1.0, HEAD, wrong method, unknown path, chunked
   framing, malformed head or incomplete request in initial T1. Those remain
   explicit T2/T3 obligations; they are not silently declared impossible.

This restriction keeps all five APIs, all body values under the buffer bound,
missing/bad credentials, duplicate-Authorization precedence, malformed commands,
parameter overflow, setpoint refusal and kernel relay refusal. It derives
first-request count=1, minor=1 and close=false, allowing T1 to avoid the general
Connection-token and post-response memmove work. General Connection helpers
remain preserved but deferred. Review D1 before implementing this restriction;
if arbitrary headers/queries/Connection are required in T1, G3's critical path
and cost must be revised explicitly.

The pure evaluator must parse its generated bytes and select headers/slices
using the pure definitions, then apply these decisions:

- Public `/state`: state unchanged, 200, JSON snapshot.
- Other routes: authenticate first; failure gives unchanged state, 401, `ct=[]`,
  `payload=[]`. Otherwise decode actual pure body/relay parameter; failure gives
  unchanged state, 400/404 and empty type/body. Otherwise evaluate
  `Spec.transition true`; success emits the committed snapshot with 200/JSON,
  kernel error emits `ReplyJson.errorStatus`/`.errorBody` with JSON type and no
  state change. Typed non-admin 403 remains covered at kernel level, but the
  fixed successful HTTP principal does not introduce that branch into T1.
- Complete reply is `ResponseHeadSpec.bytes status ct payload.length false ++
  ResponseHeadSpec.body status false payload`. No JSON-only result suffices.

Grammar-to-pure-parser acceptance and minimal complete head-prefix results are
**conclusions to prove**, not `accepted` hypotheses in T1.

## Proposed actual T1 statement — review decisions D2/D3

The following is the required mathematical interface, **not compilable Lean or
an existing theorem**. `T1Domain`, `T1Spec`, `ResetEnvelope`, `AllowedSchedule`,
`SchedulePrefix`, `SafeLiveAccesses` and `T1Budget` still need reviewed definitions.

```text
for every request r with T1Domain r,
for every finite per-byte RX/TX schedule sigma with AllowedSchedule r sigma,
for every initial core c and RAM ram with ResetEnvelope c ram:
  there exist n, d, after, reads, events such that
    n <= T1Budget r sigma
    and Observed.Steps UartPlatform.board img n <c,ram> <d,after> reads events
    and reads follow sigma
    and Observed.input reads = T1Spec.wire r
    and Observed.output events = T1Spec.replyBytes r Spec.initial
    and d.pc = 0x800017be
    and d.get 2 = 0x80ffeb90 and d.get 8 = 0x80fff814
    and AppState.At after (T1Spec.nextState r Spec.initial)
    and ramRead after 0x80ffebbc .w = 0
    and Engine.InvariantAt after 0x80ffebbc
    and d.mie_ = false
    and the completed filled/used counters equal (T1Spec.wire r).length
    and for every k < n and every actual Observed.Steps prefix of length k
        from <c,ram> whose device-read answers are a SchedulePrefix of sigma:
          not Escapes UartPlatform.board img at that prefix state
          and SafeLiveAccesses holds there.
```

`ResetEnvelope` is reset PC `0x80000000`, pinned image/board loading, legal
initial mpp and the checked 64KiB stack allocation. **D2:** explicitly accept
initial hardware-reset `MIE=false` (as existing safety roots require), while
proving the real CSR bootstrap and no re-enable theorem; or revise the initial
IRQ premise with a justified alternative. Do not require initialized App/RX,
interior borrow=-1, parser success, route selection, auth success, decoded
command, response, final state or final PC as premises. `SafeLiveAccesses`
concerns actual accesses/live allocations; a partially constructed SP during
bootstrap is not an assertion that every intermediate SP numerically denotes
an active allocated frame.

**D3:** schedules describe register-level UART observations. Each delivered RX
byte has an arbitrary finite list of LSR values with RX-ready bit clear, then
one with it set, then its specified RBR byte. Each transmitted byte has arbitrary
finite TX-not-ready polls followed by ready. Use total per-byte TX slot functions
so readiness is provided for any finite demanded prefix; do not assume desired
TX bytes or final PC to establish schedule validity. Schedule compatibility for
arbitrary execution prefixes constrains **read answers only**, never expected
writes or the absence of unsupported accesses. Ordered writes and safety are
conclusions. Existing `MainHeaderStreamPlan.Valid`, `MainLengthStreamPlan.Valid`
and `UartTxLoop.Slot` supply the concrete finite-plan vocabulary. A new universal
prefix result must be proved from the composed execution/semantics; existential
`Observed.Steps` alone is not that result.

Physical RBR/THR/FIFO interpretation additionally needs configured UART/DLAB and
external delivery assumptions; existing arbitrary-device semantics does not
establish them. This T1 proposes exact logical UART byte traces, with no FIFO,
wall-clock fairness, infinite-input progress or physical actuator claim. Provide
satisfying schedules and actual reset witnesses after the quantified theorem;
fixtures cannot replace it.

## Historical canonical-only critical-path proposal (NOT adopted)

1. **G0:** accept D1/D2/D3, define only the pure byte domain/evaluator/schedule
   interface, and prove grammar acceptance/minimal head prefix and outcome
   priority. Source-policy discrepancies must be reviewed, not patched into a
   convenient spec.
2. **G2:** reuse the existing C reset-to-Request chain and D input derivations;
   specialize them from the pure domain to remove accepted/framing premises.
   Validate the affected dependency closure, rather than restarting helper work.
3. **G3:** prove only canonical-header `wants_close=false` ABI traversal and the
   actual main method/path route/future/parameter joins. Derive Write/Read
   preconditions and exhaustively split pure auth/decode/kernel cases.
4. **G4/G5:** reuse success/kernel-error/Read suffixes; add only the specifically
   missing empty-401/400/404 main-send/Quiet adapters. Compose to `0x800017be`
   with exact UART reply and committed RAM state, then its prefix-safety result.
5. **G8:** one frozen integration audit/negative/QEMU milestone after review.
   Defer general close values, overlapping memmove, repeated serve, arbitrary
   malformed/chunked branches and broad proof-tree refactors to T2/T3.

The proposal above is retained only as history. The current critical path is:

1. G0: define/review the existing full fixed-length HTTP/1.1 API domain and pure
   evaluator, then derive accepted-head/framing/method/path cases from its bytes.
   No canonical-header/no-query/no-Connection narrowing has been accepted.
2. G1/G2 and the complete GET /state G3..G5 path are locally composed through
   exact response/committed state under explicit pure premises. Reuse these.
3. G3: close the other four actual route/mismatch/capture/method/future joins,
   derive `MainWriteInput.Ready`, reuse audited success/kernel-error suffixes and
   locally complete empty401/400/parameter404 adapters. General wants_close
   traversal is already locally complete and must not be restarted.
4. Freeze one coherent integrated dependency closure for G8 independent replay,
   semantic controls/freshness/same-ELF evidence. Local compilation is not replay.
5. G6: actual completion17be compaction/unread bytes and close978 outer restart,
   counters/App/borrow/live-stack invariant and induction for repeated requests.
6. G7: join already-scoped empty/chunk/reject/method/partial/pipelined paths into
   universal prefix refinement. No peripheral/timing/RFC scope expansion.

No completion percentage is assigned. The fixed finite buffers/code and reused
suffix contracts make remaining joins bounded in scope and plausibly tractable;
this is not an ETA or proof of eventual research success. No external blocker
has been demonstrated. G0/domain and universal prefix safety remain real work.

## Source fingerprints and review validation

Snapshot of the named root/pure sources used for this review; a hash is an
identity check, not proof that a C/D declaration was independently audited.
Paths below are under `verification/rv32/Projects/thermostat/` unless prefixed
`build/`, which means `verification/rv32/build/`.

| Source | Evidence | SHA-256 |
| --- | --- | --- |
| `Spec.lean` | A | `6f88bca22354a4fcc09f085c8a3ce0d5094066db69409262239a53ec3ebb4f77` |
| `HttpRequestSpec.lean` | A | `62970407f2153679822f54342b2cee7c595ebc8b7d4cfa15f9908d4e5a4dd18e` |
| `HeaderSpec.lean` | A | `7b9bff8adc25d3840ddd37b9085b21e445031271e5e2943573441479f7790d57` |
| `AuthSpec.lean` | A | `fd3ab4ae1ab6f80c268ceb9eacae33048becad221e848cfcb108394e2e032b2d` |
| `WireSpec.lean` | A | `ae0ac2d7723544f99e8c1110c1abc176e1c4e6f4bf3426b4f2b04747185bf649` |
| `ReplyJson.lean` | A | `f0b28d2e09b7f462c5a469114942cdd3cbd2488c2b71f1d99840c3c8010a979f` |
| `ResponseHeadSpec.lean` | A | `1bd17b1f0b01014e182603785cdee56cc16c83047d8341af1e22dd0456bef7ba` |
| `MainHeaderResetQuiet.lean` | A | `b24348229eb91e38aca0896604d125b98c0ca9f8a28f25b8a1b12e7589e2d5fc` |
| `HeadColdParser.lean` | A | `4bac19a3e959fe4772430a749dcc427204788f543a8ac6cc7bd263c8beb93380` |
| `MainWriteInput.lean` | A | `f8208ea0a8dfc67d8772998759f295ac4e56024e0b6c7d2e35c41c4ed7704c7c` |
| `MainWriteTransactionsExact.lean` | A | `2041f66cc79df3b017725e2a01e8b67758e193b1594c89797ec9469fbc38624b` |
| `ReadRoundExact.lean` | A | `6d03c2f1c9eace05adddc8e000bba2a1259128318b5765cc24a6d0ffc6a23dcb` |
| `WriteRefusal.lean` | A | `37bc1eeb78ff284cc056a1e0c7bb6391f7a7069f3bd63fc9ef90ad51c5023c3f` |
| `WriteDecodeRefusal.lean` | A | `0a22e5d8560ee42c17d689dcec251e7d6cf818d4daf8fa744ee02acc0e29869b` |
| `Send.lean` | A | `008bbc83cec839dfb13864b2de19738e34e3a914fdc7f722d2e87d394502513c` |
| `Interrupt.lean` | A | `8262d02f9870692fb4ec7a4fdb12fc9e50a36ed61740b6dcdb7e0188be395616` |
| `MainNextLengthReset.lean` | B | `63e34df25b277c82eade7f824cc7a0d5f427228a986c7ab55c6fde234eb5b210` |
| `build/MainRequestBuildReset.lean` | C | `f095a70b71ee50bf43668e6de3ed9fbef89dd843429165a87735305f3d37ce8c` |
| `build/MainRequestInputs.lean` | D | `51fb54b464e0bedad01e91e54793e5eb6253cee35254f30619064f6ade467b5c` |
| `build/MainCloseValueLoop.lean` | D | `0e7cafe1c33610fcf1c971bc8685a95c35345bfd534cd083f53e372940a323f3` |

Specification SHA-256:
`e781f2cf1c498e84ab4d55553040eab556b4df3f5aa611cc7345f8e9d276f0a4`.
Finalized A freeze-manifest SHA-256:
`55300d719367b9e0ff0a4b11fabd5abd068e5b9a80e33548ad890418cfec03a6`.
Active B freeze-manifest SHA-256:
`cff709b298565e8d238276bf436bc9d206f43e15c58ebb8feefbf4bd7af8d69d`.
All 2,154 active frozen inputs and the ELF pin were rechecked during this
review. No active audit input or specification content was edited.

Since the steering checkpoint: **zero new Lean helpers/lines and zero new audit
launches**. The preserved D group comprises 57 modules, 3,617 source lines,
286,792 bytes; it has not received an aggregate validation or audit. Inventory:
`verification/rv32/build/thermostat-closure-prototype-inventory.json`. Root source
inventory: `verification/rv32/build/thermostat-closure-source-inventory.json`.
These inventories are ignored local review records, not committed proof products.
The 147 staged C modules remain untouched. Only the already-running B audit and
its finalizer continue; four subsequent audit-start watchers were terminated
before promotion. The specification's pushed commit was verified locally and
left unchanged. No index/commit/push operations were performed for this review.

Validation: exact named declarations were checked against their source namespaces
and signatures; local Markdown target links and `git diff --check` pass. This
is documentation/source inspection, not a fresh Lean/kernel/QEMU verdict. No
reliable API token/spend telemetry is available in the workspace; CPU audit
runtime is not an estimate of API spend.


G3 live update: `MainStateMatchReset.contract` now locally connects reset through
actual UART/header/body/Request/close/initialized-table/future construction to
real matcher return PC0x800013d2. `MainPathState.contract` proves187Quiet steps,
including both memcmp calls and13actual saves/restores, result1/captures0.
`MainStateMatch.contract` DERIVES ROM/RAM path spans and stack separation from
`MainRouterEntry.At` plus pure parsed-path=/state, then retains App/RX/Request/
serve/table/close/fivefuturefields. It reuses existing packed-ROM and region
contracts; no model/ISA change. All individually compile;11positive/7negative
sweep running, controls PENDING, no independent replay. Actual GET continuation
`MainStateRouteSetup.contract` individually compiles28steps/13stores13d2->1f6e.
Its future/caller premises still need the adapter, real Wire decoder/command
stores and ReadAcquire.Pre derivation before the audited ReadRound can apply.
This does not discharge all G3 or T1. Pure accepted/framing/schedule premises
must still be derived from G0's reviewed domain; no domain narrowing accepted.


Current complete Read integration (local, not independently replayed):
`MainReadReset.contract` starts at actual reset, uses `MainCloseRequestReset.contract_routes`,
`MainRouterEntry.contract`, `MainStateMatch.contract`,
`MainReadRouteInput.contract`, `MainReadDecoded.contract`, then audited
`ReadRound.contract_exact`. It reaches17be/978 with the exact actual HTTP header
AND JSON UART events, exact RX byte projection, App(initial), persisted invariant,
SP/FP and interrupts masked. `MainReadReset.reply_capacity` derives the actual
main-stored832 output capacity; it is not assumed at reset. `MainReadDecoded`
uses the actual `Wire.contract_quiet` and9actual return/enum-store instructions,
retaining arbitrary inactive enum bytes; `WireSpec.read_body_independent` derives
Read for every body. The public actor byte0, borrow0, snapshot, stack and every
ReadAcquire.Pre field follow from the executed prefix.

The root quantifies over initial Core/RAM, arbitrary bounded accepted fixed body,
pure parsed GET/path=/state and finite RX/TX readiness plans; query and general
Connection scans are retained. It still explicitly assumes the PURE consumed-head
acceptance/framing facts, not a machine handler outcome. G0 must derive those
from the reviewed byte domain. Its Read-only interface is an integration case,
not an accepted narrowing or completion of T1. `MainReadResetWitness.execution`
uses4existing HTTP1.1 parsed requests with query and keep/close/mixed-case/near-
miss/duplicate Connection; fixture runs do not replace the quantified root.

Validation:7fresh positives/8semantic negatives PASS23.240661269s,
standard3axioms for quantified root AND complete witnesses, stable hashes;
source883lines/77108bytes across7ignored modules.
Prior matcher11/7 PASS165.976885358s; source3083lines/
415527bytes includes220fetch certificates and actual158-step body.
No controls pending; no new full audit. Latest finalized9047/2142/all874 result
rechecked CURRENT18:49:55; model/job/canonical/spec/ELF inputs unchanged. API
spend/token telemetry unavailable; these timings are local CPU wall time only.


Exact remaining write-call mismatch (18:54 inspection of this same ELF):

| Route | Actual call/RET | Existing contract mismatch |
| --- | --- | --- |
| PUT /setpoint |1624 ->4c6 ->1628 ->16e6/1704 ->1710 | Different future/RET; `MainWriteTransactions` starts195a. |
| POST /temp |1600 ->4c6 ->1604 ->16a6/1708 ->1710 | Different future/RET and flags. |
| PUT /mode |15dc ->4c6 ->15e0 ->16c6/1708 ->1710 | Different future/RET and flags. |
| PUT /relay/{i} |1968 ->4c6 ->196c ->1998 ->1710 | Matches195a call adapter, but its x18=1 premise is not the actual initial router value. |

Actual main12fe sets x18(s2)=2. Existing `MainWritePost.At.ready`,
`MainWriteReady.contract`, `MainWriteDispatch.contract`, `MainWriteResponse`
and `MainWriteReply/Transactions` interfaces require x18=1. Both1/2 correctly
branch on handler Response tag0, but the old premise must not be assumed at the
real caller. `WriteSuccessFrame.contract_inv`, generic `WriteInput.Pre`, and
`SharedWriteResponse.contract_quiet` can be reused. Named remaining edge needs
actual caller/future/RET dispatch adapters and a common1710 renderer join;
changing the runtime or forcing a fake195a/18=1 state is not authorized.


The four JSON return joins above are now locally closed by exact declaration
`MainWriteReturnJoin.contract_exact`, using `.extract` and
`MainSetpointReturn.contract`(13steps/3flagstores),
`MainTempReturn.contract`(13/2), `MainModeReturn.contract`(12/1),
`MainRelayReturn.contract`(12/0). Actual x18=2 is used to prove the real branch
on tag0; no ghost x18=1 state, fake195a entry or runtime change is introduced.
`MainWriteExtracted.contract` is the existing checked23instruction renderer
from actual1710, and `MainWriteExtractedReply.contract_exact` composes actual
MainSend/completion. It retains App/Inv/RX/SP/FP and exact HTTP header+JSON bytes.
Interior premises still include actual returned BodyMemory/JSON/App/metadata;
G3/G4 must derive them via the real distinct future/call sites and generic
WriteSuccessFrame/WriteInput contracts. Empty early-refusal MIME/body has not
been connected to these actual four return sites; old relay/x18=1 adapters must
not be advertised as that result.

Fresh8positive/8semantic-negative sweep PASS20.350337229s;
standard3axioms and stable hashes; source861lines/
79516bytes, no independent replay. A wrong-fetch-PC mutation hit
recursion depth before semantic rejection and was NOT counted; the completed
suite instead checks explicit wrong actual return-target/MIME conclusions.
`MainPathReturn.contract` individually compiles the real15instruction matcher
restore/RET for a caller-specified aligned return PC, needed by1422/146c/14b6/
1856; no fresh aggregate/negative/replay yet. The original verified /state ABI
contract is preserved. Next G3 input obligation: carry initialized25futurewords
from129a and prove actual non-/state matcher/caller chain, then generic handler.


Current POST successor (local, aggregate verification running): exact declarations
`MainTempChain.next/contract` compose all3actual matcher/caller paths in≤484steps
from actual first matcher283a to/temp return146c. `MainTempRouteReset.contract`
composes reset/UART/Request/generalclose/startupfutures into this route result.
`MainTempWriteSetup.contract` proves28actual method/future/call instructions and
7stores146c->4c6, actualfutureFA84/RA1604. `MainRouteInputs.headers/table` reuse
original header views under the preserved caller envelope; exact new
`HeaderFrame.header_fields` proves336sufficient bytes (count,rawptr/rawlength,
16headercells), instead of assuming params/count unchanged across its real store.
`MainTempWriteInput.contract` then derives EVERY generic WriteInput.Pre field,
App/key/principal/freeborrow/raw/body/path/captures/stack/alias/future/capacity,
withactuals2=2 and interrupts masked. `MainTempEntryReset.contract` derives this
fromactualreset without an interior caller precondition. CapacityF9fc is derived
fromthe existing checked MainReadReset.reply_capacity actualstores and retained
by the caller envelope; no fabricated interior layout premise is introduced.

`MainTempSuccess.contract` reuses audited WriteSuccessFrame.contract_inv_quiet
withactualfutureFA84, its generic saved ABI/frame, actual persistedcommit/borrow,
then MainWriteReturnJoin.contract_exact attempRET1604. Exact full header+JSONUART,
SP/FP/CSR/App/Inv/RX are composed. `MainTempSuccessReset.contract` starts atreset,
retains arbitrary bounded accepted rawbody/query/generalConnection, and ends
at17be/978 withSpec.commitinitial(.okres), exactRX/TX andmaskedinterrupts.
Its extra auth/decode/transition premises are independent PURE case facts, not
desired machine results; the actual header/auth/decoder/engine execute. This is
only the successful POST integration case, not allPOST/T1 or a reviewed grammar.
`MainTempSuccessWitness.execution` supplies bothkeep/close HTTP1.1 POST/temp?q,
validBearerkey andbody400, persistingtemperature200->400 andits exactreply.

The22-source freshpositive/12semanticnegative suite is RUNNING; no aggregate or
axiom verdict yet and NO independent replay. No registered/model/job/ELF/spec
inputs changed; no full audit or Git operation launched. Next named mismatch:
old MainStatusAuthHandler/DecodeHandler havefixedfutureFA2C and fixed
MainWritePost.Frame, while actualtempfutureFA84 differs. Prove the minimal
future-parametric refusal frame and common1710 MIME=[]/pointer1 response join,
reuse the actual underlying RequestRefusal/WireReject/ABI contracts, then split
all pure POST auth/body outcomes. Do not claim old relay/x18=1 refusal adapters
already cover this route. G0 and other3routes/G6/G7 remain.

2026-11-08 19:52:58 UTC POST /temp ALL-CASE LOCAL root MainTempReset.contract individually PASS. TempHttpSpec.run independent observable state/status/MIME/payload selects200/401/400 without outcome premises. Generic futureFA84 refusal frame/auth/WireReject/RET1604/actual MIME=[]pointer1 renderer/exact sender composed. New10sources individually PASS, aggregate/axioms PENDING, no independent replay. Prior22positive/12negative success integration completed PASS265.793952324s standard3axioms stablehashes. Front summaries refreshed; no frozen input/job/model/ELF/spec mutation or new full audit/Git action.


## Active T1 domain and top-level interface (current review proposal)

This replaces the **historical canonical-only proposal as the active candidate**;
it does not claim acceptance or a proved grammar lemma. No runtime, parser policy,
ELF or specification document is changed. Existing conditional reset roots are
integration lemmas; their pure parser-result premises are not the final interface.

The proposed `ApiRequestSpec.Fixed11` is a pure structured byte grammar:

- Request line: exact API method/path pair (GET `/state`, PUT `/setpoint`, POST
  `/temp`, PUT `/mode`, PUT `/relay/` followed by any nonempty visible single
  segment). The relay segment is not restricted to valid numbers or indices;
  decoding/kernel404 outcomes remain in scope. Optional first-`?` query has
  arbitrary bytes accepted by `isTargetByte`, including additional `?` bytes.
  Version is exactly HTTP/1.1; separators are SP and CRLF. Method/path variants
  and HEAD outside these API pairs remain T3 obligations, not silently accepted
  as the correct method by T1.
- Between2 and16 header fields in arbitrary order: nonempty `isTchar` names,
  colon, and any `isFieldByte` value bytes. Case variants, leading/trailing OWS
  and repeated ordinary/Authorization/Connection fields are retained. There is
  exactly one case-insensitive Host (its value may be empty) and exactly one
  Content-Length, and no Transfer-Encoding. Content-Length has optional leading
  OWS then a nonempty decimal spelling, with arbitrary leading zeroes, of the
  body length; its trailing OWS is forbidden by the existing parser policy.
  No valid/matching Authorization or command-body condition enters this grammar.
- Head ends in CRLF CRLF and has length≤1024. Body is **any** byte list of
  length≤1024, with the declared length and total≤2048. This includes empty,
  malformed, signed-i16 extrema, out-of-range setpoints, invalid mode/relay
  bodies and missing/bad credentials. It is a quantified domain, not fixtures.

The grammar must compute field offsets, method/path/query spans, head length,
and framing. Named G0 proof obligations: prove each proper head prefix parses
incomplete, the complete encoded head parses to these computed fields, first
`consume` stops exactly there, and fixed-body arrival appends exactly the body.
These properties are conclusions derived from byte classes and line/header
structure, not fields of `Fixed11` and not reset-theorem assumptions. The grammar
still needs Lean implementation and review against the pure parser policies.

Proposed actual T1 signature, not an existing declaration:

```text
Firmware.one_request
  (request : ApiRequestSpec.Fixed11)
  (initialCore, initialRam : loader/reset envelope)
  (rxSchedule : finite valid delivery of request.bytes)
  (txSchedule : finite valid readiness for pureReply.bytes) :
  exists steps finalCore finalRam observedReads,
    Observed.Steps pinnedBoard pinnedImage steps
      (initialCore, initialRam) (finalCore, finalRam)
      observedReads (TX events of pureReply.bytes)
    and acceptedRX(observedReads) = request.bytes
    and finalCore.pc = (if pureClose then 0x80000978 else 0x800017be)
    and finalCore.sp/fp = actual live serve-frame values
    and finalCore.mie = false
    and AppState.At finalRam pureReply.state
    and borrow(finalRam) = 0 and Spec.Inv pureReply.state.
```

Here `pureReply` must use a unified byte-only API evaluator (Header/Auth/Decimal/
Wire/Spec/ReplyJson/ResponseHead), not handler success facts, pointers or Rust tags.
`TempHttpSpec.run` is the current locally connected instance for POST `/temp`;
its full200/401/400 split and exact MIME/header/payload match `MainTempReset.contract`.
The common root must cover all five API pairs and derive every interior layout.
Bothclose choices are determined by `MainCloseSpec.mustClose` with served=1 and
actual parsed fields, not selected freely. Hardware-reset MIE/mpp/map/allocation
facts belong in the reset envelope; the actual bootstrap masking proof remains
in its derivation. Readiness assumes no eventual response under infinite silence.

T1 ends at the real complete boundary and does not claim next-request reception,
physical FIFO behavior or global prefix safety. The fixed final target remains
`Firmware.reset_stream_refines` from the operating CLOSURE map, with T2's concrete
recurrence and T3's all-branch stream invariant still required.

2026-11-08 19:57:20 UTC Full POST local validation completed:12positive/11semantic negatives PASS35.650115287s,1456lines116530bytes, standard3axioms, source hashes stable. `MainTempResetWitness.execution` supplies200/400/401 with both close flags through the unified all-case reset root. Missing credentials plus malformed body demonstrates401 priority. No independent replay/new audit; verify-result of frozen baseline CURRENT. Remaining G0/3other routes/G6/G7 unchanged.

2026-11-08 20:09:31 UTC PUT /setpoint all-case LOCAL reset root MainSetpointReset.contract PASS; no auth/decode/kernel-result/layout premise. Actual2matchers(≤408), method/future setup28instructions/7stores, futureFAB0/RET1628/x18=2 -> generic all-outcome handler and exact HTTP/UART/Spec.commit/Inv/borrow0. ApiWriteHttpSpec.run byte-only evaluator and MainApiWriteCaller.transaction shared with remaining write routes; existing WriteSuccessFrame/WriteErrorFrame and refusal/send reused. MainSetpointResetWitness.execution four200/400/422/401 actual reset executions PASS.20new sources individuallyPASS; fresh20positive/14semantic-negative suite RUNNINGsession65467, verdict/axioms PENDING, no independent replay/new full audit/Git.209-instruction matcher resource1500MiB failure, bounded1900MiB PASS; failed core-dump cleanup stopped only after exact PID/source/CoreDumping checks, no valid audit interrupted. G0,2routes,G6/G7 remain.

2026-11-08 20:13:34 UTC Setpoint20source fresh/14semantic-negative integration PASS217.160526651s, 5056lines/636555bytes, standard3axioms and unchanged hashes. Generic MainApiWriteCaller.success/error/refusal/transaction handles all actual return sites with x18=2; of_temp/of_setpoint derive its fields from actual caller proofs. MainSetpointReset.contract has no auth/decode/kernel-outcome premise; four actual reset witnesses supply200/400/422/401. Future/return, borrow, wrong JSON/status/state/auth-priority mutations rejected semantically. No independent replay/new full audit/Git. Next /mode requires preserving initializeds9=FA58 across its4matcher calls; helper envelope omits this register, so the new named chain must export actual ABI preservation rather than postulate it.

2026-11-08 20:19:51 UTC Mode ALL-CASE LOCAL root MainModeReset.contract PASS, four reset witnesses heat/auto200,400,401 PASS. MainModeChain.contract actual4matchers≤665 plus savedx25 initializedFA58 derived from MainRouterEntry.secondSlot, no reset pointer premise. Actual27instruction/7store method/future setup, futureFA58/RET15e0/x18=2 and MainApiWriteCaller.of_mode/transaction reused.18source freshpositive/12semantic-negative suite RUNNINGsession89879, verdict/axioms PENDING, no independent replay/new full audit/Git. Mode batch initial ROMliteral-copy error fixed and chain/root manually recompiled; old batch log stale, new local suite frozen. verify-resultCURRENT, spec/ELF hashes unchanged20:19:18; gitdiffcheckPASS. Remainingrelay variablecapture/all5caller join, G0, G6/G7. G6 first derive zero-leftover from real one-byte RX/exactbody and sender frames, do not add genericmemmove without need.

2026-11-08 20:24:41 UTC Mode18source/12semantic-negative integration PASS190.454820490s,6018lines706032bytes, standard3axioms/stable hashes. MainModeReset.contract and four reset witnesses checked; futurepointer/ABI/return/freshflag/admin/heater/state/wirestatus mutations rejected. No independent replay/new full audit. Relay remaining caller edge additionally needs preserving initializedx24 and dropping initialzero-params after the two real capture stores; HeaderFrame.header_fields exact336byte footprint is reusable.

2026-11-08 20:40:30 UTC Relay named G3 milestone LOCAL individuallyPASS: MainStateRelay.contract156steps, MainSetpointRelay.contract160, MainTempRelay.contract140, MainModeRelay.contract140 prove actual first4literal rejections for arbitrary suffix/pathSize≥8, full saved ABI andRET; size8 is only untrusted trace selection, every branch theorem quantifies all sizes≥8. MainRelayPrefix.contract181actualinstructions reaches finalsegment PC2894. MainRelaySegment.contract proves arbitrary nonempty no-slash RAM suffix scan by list induction, exactly5*len+1 steps, PC2894->28a8, unchangedRAM/noMMIO. MainRelayCapture.contract29instructions proves real guard/capture stores7/end and match1/count1 to293a; first_word/second_word/frame/region connect exactRAM. MainPathCapturedReturn.contract15actualinstructions uses only saved-stack96byteFrame, replacing inapplicable wholeRAM equality aftercapture. MainRelayBody.contract211+5*len and MainRelayMatch.contract240+5*len compose selectedmatcher actualsave/prefix/loop/twoStores/restore/RET for arbitrary param; no capture-result premise. MainThirdMatcherCall/MainFourthMatcherCall now allowactualvariablepathSize (same11instructioncalls). MainRelayRouterCode and MainRelayFifthCall11instructions individuallyPASS. No aggregatecontrols/independentreplay/new fullaudit/Git. RemainingG3: actual5caller chain preservinginitializedx24=FA2C; capturedRequest view must forget oldparamszero and retain336header bytes/Body/Path; actualmatchedmethod/futuresetup and genericWriteInput.Pre -> MainApiWriteCaller.transaction. Existinggenericall-outcome suffix reused. Old MainRelayCapture.log is failed firstPCnormalization history; correctedsource/currentolean PASS. Prefix181 bounded1900MiB PASS; otherliteral traces bounded1500MiB PASS. No external blocker, no canonical/job/model/spec/ELF mutation.

2026-11-08 20:58:35 UTC ALL5API LOCAL conditionalresetroots compile. MainRelayWriteInput.contract derives capture-aware Header336/Body/Path/ParamInput.Capture count1/start7/end and captured_slice=param, all genericWriteInput.Pre/freshFA2C/RA196c/832capacity/admin/borrow/layout. MainRelayEntryReset.contract bound5730+5len+head/RXcost derivesReadyfromactualreset; MainRelayReset.contract bound12775+5len+212headers+18body+head/RX/TXcost givesexactHTTP/UART+pureApiWriteHttpSpec.runcommit+Inv+borrow0+SPFPmask17be/978. Arbitraryparamnonempty/noSlash andpureaccepted-head/framing/method/path+finiteplans remain explicit; G0/T1stillOPEN. MainRelayResetWitness fivecases200/404JSON/404empty/400/401 COMPILINGsession29173, CPUactive/noerrorsseen, no aggregate/axiom/replay verdict yet. No newfullaudit/Git/canonicalproof/model/job/spec/ELF mutation. Nextfinishrelaycontrols thenG0structuralacceptance/unifiedT1; G6/G7 remain.

2026-11-08 21:07:14 UTC G0 current work: `build/ApiRequestSpec.lean` defines pure `ApiRequestSpec.Fixed11`, arbitrary header order/case/ordinary duplicates/query/Connection/body and all five API pairs. It has no parser-success or internal-machine field. `build/ApiRequestGrammar.lean` locally proves `request_line` and `header_line` from syntax/byte classes; full field classification/fold, proper-prefix incompleteness, exact consume and unified T1 remain OPEN. Relay16semantic negatives PASS32.557175034s; corrected five-case reset witness compiling, axiom/replay pending. Independent baseline unchanged. Concise current map: `/root/e5r-agent-runs/thermostat-proof/CLOSURE.md`.

2026-11-08 21:19:54 UTC T1 LOCAL root `E5R.Thermostat.Firmware.one_request` compiled, standard3axioms. `ApiRequestSpec.Fixed11` is the broad byte-only structural domain; `ApiFixedHead.accepted`, `ApiHeadPrefix.incomplete`, `ApiConsume.exact_head/delivered`, `ApiRouting.method_case/path` discharge all accepted-head/framing/method/path hypotheses of the5actual reset roots. Conclusion: exact full HTTP/UART and acceptedRX, pure committedApp, borrow0, Spec.Inv/actualRAM invariant, SPFPmask at pure-close-selected17be/0978. Loader/reset(MIEfalse/mpp/map64KiB) and finite UART readiness/delivery remain explicit; no desired parser/auth/decode/kernel/layout premise. Fresh10source/16semantic-negative validation RUNNING; independent replay pending, wholefirmware/G6/G7 OPEN. Relay26individual/current sources+5resetwitnesses,16negatives andstandard3axioms PASS, no repeatfresh26sweep. Baseline independently replayed report CURRENT21:13UTC with unchanged ELF/spec.

2026-11-08 21:28:28 UTC T1 dependency closure registered:364new canonical files, no existing proof overwritten, all old source hashes unchanged. One integrated audit/finalizer RUNNINGsession82716: expected2506independentreplays;1173controls andsameELFQEMU/finalCURRENT remain pending. Fresh10G0/T1+16negatives PASS40.519270638s; unified8case×bothclose domain witnesses andstandard3axioms PASS. Prior9047/2142/874 report archived before expansion and is STALE for the expanded job; no claim of current T1 audit success. G6 work proceeds only in ignored build files.
