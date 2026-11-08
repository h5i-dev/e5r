import Projects.thermostat.CopyTwoResult
import Projects.thermostat.CopyThreeResult
import Projects.thermostat.ForbiddenCopy
import Projects.thermostat.ErrorLiterals
namespace E5R.Thermostat.ErrorCopy
open E5R E5R.Thermostat

def bound : Spec.Error → Nat
  | .setpointOutOfRange => 137 | .noSuchRelay => 123 | .forbidden => 55

/-- Actual memcpy entry/optimized unaligned word loops/partial tail/return for
    all error literals. Stack/output separation is explicit. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (e : Spec.Error)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst)
    (h11 : c.get 11=ErrorLiterals.pointer e) (h12 : c.get 12=BitVec.ofNat 32 (ReplyJson.errorBody e).length)
    (hs : Memory.Block UartPlatform.board sp 16) (hsa : sp.toNat%4=0)
    (hd : Memory.Block UartPlatform.board dst (ReplyJson.errorBody e).length) (ha : dst.toNat%4=0)
    (hw : dst.toNat+(ReplyJson.errorBody e).length<2^32)
    (hsep : WordRegions.Disjoint dst (ReplyJson.errorBody e).length sp 16) :
    ∃ d n r, n≤bound e ∧ DetSteps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ FormatCursor.Returned c d ∧
      d.get 10=dst ∧ Bytes.Span UartPlatform.board r dst (ReplyJson.errorBody e) ∧
      (∀ x, (∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) →
        (∀ i : Fin (ReplyJson.errorBody e).length, x≠dst+BitVec.ofNat 32 i.val) → r x=ram x) := by
  cases e with
  | setpointOutOfRange =>
    obtain ⟨d,td,hr,hout⟩ := CopyTwoExecute.contract c ram sp dst hp hsp h10 h11 h12 hs hsa hd ha hw
    exact ⟨d,137,CopyTwoExecute.memory ram sp dst,Nat.le_refl _,td,hr,hout,
      CopyTwoResult.written ram sp dst hd hw (WordRegions.symm hsep),
      fun x hx hy => CopyTwoResult.frame ram sp dst x hx hy⟩
  | noSuchRelay =>
    obtain ⟨d,td,hr,hout⟩ := CopyThreeExecute.contract c ram sp dst hp hsp h10 h11 h12 hs hsa hd ha hw
    exact ⟨d,123,CopyThreeExecute.memory ram sp dst,Nat.le_refl _,td,hr,hout,
      CopyThreeResult.written ram sp dst hd hw (WordRegions.symm hsep),
      fun x hx hy => CopyThreeResult.frame ram sp dst x hx hy⟩
  | forbidden =>
    obtain ⟨d,n,r,hn,td,hr,hout,hbytes,hframe⟩ := ForbiddenCopy.contract c ram sp dst hp hsp h10 h11 h12 hd ha hw
    exact ⟨d,n,r,hn,td,hr,hout,hbytes,fun x _ hy => hframe x hy⟩
end E5R.Thermostat.ErrorCopy
