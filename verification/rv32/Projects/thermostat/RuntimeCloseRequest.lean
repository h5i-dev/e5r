import Projects.thermostat.RuntimeCloseScanned
set_option autoImplicit false
namespace E5R.Thermostat.RuntimeCloseRequest
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual Request boundary to main router entry for all permitted versions,
    request counts, duplicate Connection fields and arbitrary bounded values.
    The selected close flag, stack availability, full saved-register ABI and
    actual Request/App/RX preservation all derive from Request construction. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat}
    (h : RuntimeRequest.Ready c ram input s head amount rawUsed served) :
    ∃ n d after close,
      n≤(77+86*(RuntimeRequestSpans.raw input rawUsed).length)*(RuntimeRequestInputs.entries head).length+71 ∧
      Quiet.Steps MainRequestBuild.B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      RuntimeCloseReady.At d after input s head amount rawUsed served (c.get 27) close ∧ d.sameCsr c ∧ ViewFrame.Region ram after MainRequestBuild.sp 3304 := by
  by_cases force : head.minor=0 ∨ 100≤served
  · obtain ⟨n,d,nb,trace,ready,csr,frame⟩ := RuntimeCloseForced.contract h force
    exact ⟨n,d,_,true,by omega,trace,ready,csr,frame⟩
  · obtain ⟨n,d,after,nb,trace,ready,csr,frame⟩ := RuntimeCloseScanned.contract h force
    exact ⟨n,d,after,_,nb,trace,ready,csr,frame⟩
end E5R.Thermostat.RuntimeCloseRequest
