import Projects.thermostat.RuntimeRequest
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeStored
open E5R E5R.Thermostat HttpRequestSpec
abbrev sp := MainRequestBuild.sp
abbrev rx := MainRequestBuild.rx
abbrev req := sp+3312#32

/-- Initial Request RAM facts, independent of caller register roles. Params
    remain zero only until actual route matching writes them. -/
structure At (ram : Word → BitVec 8) (input : List (BitVec 8)) (head : Head) (amount rawUsed : Nat) : Prop where
  headView : HeadCompletedView.At ram req head
  request : RuntimeRequest.Fields ram input head amount rawUsed
  methodByte : ram (sp+3684#32)=BitVec.ofNat 8 (MainMethodSpec.tag (MainMethodSpec.decode (MainMethodBytes.token input head.method.2)))
  bounds : MainHeadAcceptedBounds.At 1024 1024 head
  bodyBound : amount≤1024
  usedBound : head.len+amount≤rawUsed ∧ rawUsed≤input.length
  contained : head.target.2<head.len ∧ (∀ entry∈head.headers, MainHeadBounds.FieldAt head.len entry)

theorem fromReady {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) : At ram input head amount rawUsed :=
  ⟨h.headView,h.request,h.methodByte,h.bounds,h.bodyBound,h.usedBound,h.contained⟩

theorem preserve {before after : Word → BitVec 8} {input : List (BitVec 8)} {head : Head} {amount rawUsed : Nat}
    (h : At before input head amount rawUsed) (frame : ViewFrame.Region before after req 376) : At after input head amount rawUsed := by
  have smallHead : MainCopyView.At before after req req 304 := by
    intro i
    exact frame ⟨i.val,by have := i.isLt;omega⟩
  have word (k : Nat) (bound : k+4≤376) : ramRead after (req+BitVec.ofNat 32 k) .w=ramRead before (req+BitVec.ofNat 32 k) .w := ViewFrame.word frame k bound
  have methodByte : after (sp+3684#32)=before (sp+3684#32) := by
    simpa only [req,BitVec.add_assoc,show 3312#32+372#32=3684#32 by decide +kernel] using frame ⟨372,by decide⟩
  refine ⟨MainCopyView.head smallHead head h.headView,?_,methodByte.trans h.methodByte,h.bounds,h.bodyBound,h.usedBound,h.contained⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,methodByte.trans h.request.method,?_⟩
  · have kept := word 304 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+304#32=3616#32 by decide +kernel] at kept
    exact kept.trans h.request.path
  · have kept := word 308 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+308#32=3620#32 by decide +kernel] at kept
    exact kept.trans h.request.pathLength
  · have kept := word 312 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+312#32=3624#32 by decide +kernel] at kept
    exact kept.trans h.request.query
  · have kept := word 316 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+316#32=3628#32 by decide +kernel] at kept
    exact kept.trans h.request.queryLength
  · have kept := word 320 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+320#32=3632#32 by decide +kernel] at kept
    exact kept.trans h.request.body
  · have kept := word 324 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+324#32=3636#32 by decide +kernel] at kept
    exact kept.trans h.request.bodyLength
  · have kept := word 328 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+328#32=3640#32 by decide +kernel] at kept
    exact kept.trans h.request.raw
  · have kept := word 332 (by decide)
    simp only [req,BitVec.add_assoc,show 3312#32+332#32=3644#32 by decide +kernel] at kept
    exact kept.trans h.request.rawLength
  · intro i
    have byte := frame ⟨336+i.val,by have := i.isLt;omega⟩
    have address : req+BitVec.ofNat 32 (336+i.val)=(sp+3648#32)+BitVec.ofNat 32 i.val := by
      rw [BitVec.ofNat_add,←BitVec.add_assoc,show req+336#32=sp+3648#32 by decide +kernel]
    rw [address] at byte
    exact byte.trans (h.request.params i)
end E5R.Thermostat.RuntimeStored
