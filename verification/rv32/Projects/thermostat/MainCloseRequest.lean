import Projects.thermostat.MainCloseScanned
set_option autoImplicit false
namespace E5R.Thermostat.MainCloseRequest
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual Request boundary to main router entry for all permitted versions,
    request counts, duplicate Connection fields and arbitrary bounded values.
    The selected close flag, stack availability, full saved-register ABI and
    actual Request/App/RX preservation all derive from Request construction. -/
theorem contract {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount served : Nat}
    (h : MainRequestBuild.Ready c ram input s head amount served) :
    ∃ n d after close,
      n≤(77+86*(MainRequestSpans.raw input head amount).length)*(MainRequestInputs.entries head).length+71 ∧
      Quiet.Steps MainRequestBuild.B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      MainCloseReady.At d after input s head amount served close ∧ d.sameCsr c := by
  by_cases force : head.minor=0 ∨ 100≤served
  · obtain ⟨n,d,nb,trace,ready,csr⟩ := MainCloseForced.contract h force
    exact ⟨n,d,_,true,by omega,trace,ready,csr⟩
  · obtain ⟨n,d,after,nb,trace,ready,csr⟩ := MainCloseScanned.contract h force
    exact ⟨n,d,after,_,nb,trace,ready,csr⟩
end E5R.Thermostat.MainCloseRequest
