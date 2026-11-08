-- Generated stronger trace proofs; Lean checks every decoded-instruction side condition.
import Projects.thermostat.ErrorCopy
import Projects.thermostat.QuietDet
import Projects.thermostat.RamRunQuiet
import Projects.thermostat.CopyThreeExecuteQuiet
import Projects.thermostat.CopyTwoExecuteQuiet
import Projects.thermostat.ForbiddenCopyQuiet
open E5R E5R.Thermostat
namespace E5R.Thermostat.ErrorCopy
theorem contract_quiet (c : Core) (ram : Word → BitVec 8) (sp dst : Word) (e : Spec.Error)
    (hp : c.pc=0x80005182#32) (hsp : c.get 2=sp+16#32) (h10 : c.get 10=dst)
    (h11 : c.get 11=ErrorLiterals.pointer e) (h12 : c.get 12=BitVec.ofNat 32 (ReplyJson.errorBody e).length)
    (hs : Memory.Block UartPlatform.board sp 16) (hsa : sp.toNat%4=0)
    (hd : Memory.Block UartPlatform.board dst (ReplyJson.errorBody e).length) (ha : dst.toNat%4=0)
    (hw : dst.toNat+(ReplyJson.errorBody e).length<2^32)
    (hsep : WordRegions.Disjoint dst (ReplyJson.errorBody e).length sp 16) :
    ∃ d n r, n≤bound e ∧ Quiet.Steps UartPlatform.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧ FormatCursor.Returned c d ∧
      d.get 10=dst ∧ Bytes.Span UartPlatform.board r dst (ReplyJson.errorBody e) ∧
      (∀ x, (∀ i : Fin 16, x≠sp+BitVec.ofNat 32 i.val) →
        (∀ i : Fin (ReplyJson.errorBody e).length, x≠dst+BitVec.ofNat 32 i.val) → r x=ram x) := by
  cases e with
  | setpointOutOfRange =>
    obtain ⟨d,td,hr,hout⟩ := E5R.Thermostat.CopyTwoExecute.contract_quiet c ram sp dst hp hsp h10 h11 h12 hs hsa hd ha hw
    exact ⟨d,137,CopyTwoExecute.memory ram sp dst,Nat.le_refl _,td,hr,hout,
      CopyTwoResult.written ram sp dst hd hw (WordRegions.symm hsep),
      fun x hx hy => CopyTwoResult.frame ram sp dst x hx hy⟩
  | noSuchRelay =>
    obtain ⟨d,td,hr,hout⟩ := E5R.Thermostat.CopyThreeExecute.contract_quiet c ram sp dst hp hsp h10 h11 h12 hs hsa hd ha hw
    exact ⟨d,123,CopyThreeExecute.memory ram sp dst,Nat.le_refl _,td,hr,hout,
      CopyThreeResult.written ram sp dst hd hw (WordRegions.symm hsep),
      fun x hx hy => CopyThreeResult.frame ram sp dst x hx hy⟩
  | forbidden =>
    obtain ⟨d,n,r,hn,td,hr,hout,hbytes,hframe⟩ := E5R.Thermostat.ForbiddenCopy.contract_quiet c ram sp dst hp hsp h10 h11 h12 hd ha hw
    exact ⟨d,n,r,hn,td,hr,hout,hbytes,fun x _ hy => hframe x hy⟩

end E5R.Thermostat.ErrorCopy
