import Projects.thermostat.MainRequestBuild
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeRequest
open E5R E5R.Thermostat HttpRequestSpec
abbrev sp := MainRequestBuild.sp
abbrev fp := MainRequestBuild.fp
abbrev rx := MainRequestBuild.rx

/-- Actual Request fields, with the encoded raw extent separated from the
    compacted body extent. Original Head framing is retained verbatim. -/
structure Fields (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) : Prop where
  path : ramRead ram (sp+3616#32) .w=rx+BitVec.ofNat 32 head.target.1
  pathLength : ramRead ram (sp+3620#32) .w=MainRequestBuild.pathLength input head
  query : ramRead ram (sp+3624#32) .w=MainRequestBuild.queryPtr input head
  queryLength : ramRead ram (sp+3628#32) .w=MainRequestBuild.queryLength input head
  body : ramRead ram (sp+3632#32) .w=BitVec.ofNat 32 head.len+rx
  bodyLength : ramRead ram (sp+3636#32) .w=BitVec.ofNat 32 amount
  raw : ramRead ram (sp+3640#32) .w=rx
  rawLength : ramRead ram (sp+3644#32) .w=BitVec.ofNat 32 rawUsed
  method : ram (sp+3684#32)=byteOf (MainRequestBuild.method input head) 0
  params : ∀ i : Fin 36, ram ((sp+3648#32)+BitVec.ofNat 32 i.val)=0#8

/-- A concrete successful Request boundary. The buffer is the actual current
    RAM view after any compaction; a later stream theorem must relate its head
    and decoded body to independent input bytes. No parser result or framing
    equivalence is inferred from this interior interface alone. -/
structure Ready (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (s : Spec.Snapshot)
    (head : Head) (amount rawUsed served : Nat) : Prop where
  pc : c.pc=0x80001246#32
  stable : MainTransactionStable.At c ram input s
  future : c.get 23=0x80fff9f0#32
  three : c.get 26=3#32
  serve : MainServeLayout.At ram served
  countBound : served≤100
  positive : 0<served
  countReg : c.get 18=BitVec.ofNat 32 served
  minorReg : c.get 9=BitVec.ofNat 32 head.minor
  usedWord : ramRead ram (fp+92#32) .w=BitVec.ofNat 32 rawUsed
  headView : HeadCompletedView.At ram (sp+3312#32) head
  request : Fields ram input head amount rawUsed
  methodByte : ram (sp+3684#32)=BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  bodyBound : amount≤1024
  usedBound : head.len+amount≤rawUsed ∧ rawUsed≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

theorem Ready.available {c ram input s head amount rawUsed served} (h : Ready c ram input s head amount rawUsed served) :
    head.len+amount≤input.length := Nat.le_trans h.usedBound.1 h.usedBound.2

/-- All previously proved fixed-length executions project to the broader
    view. No ELF, model or old contract is changed to add other framings. -/
theorem fromFixed {c ram input s head amount served} (h : MainRequestBuild.Ready c ram input s head amount served) :
    Ready c ram input s head amount (head.len+amount) served := by
  exact ⟨h.pc,h.stable,h.future,h.three,h.serve,h.countBound,h.positive,h.countReg,h.minorReg,h.usedWord,h.headView,
    ⟨h.request.path,h.request.pathLength,h.request.query,h.request.queryLength,h.request.body,h.request.bodyLength,
      h.request.raw,h.request.rawLength,h.request.method,h.request.params⟩,
    h.methodByte,h.bounds,h.bounds.content amount h.kind,⟨Nat.le_refl _,h.available⟩,h.contained⟩
end E5R.Thermostat.RuntimeRequest
