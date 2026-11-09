import Projects.thermostat.RuntimeApiWriteRefusalHandler
import Projects.thermostat.StackRuntimeApiWriteCaller
import Projects.thermostat.StackMainFutureAuthHandler
import Projects.thermostat.StackMainFutureDecodeHandler
set_option autoImplicit false
set_option maxRecDepth 6000
namespace E5R.Thermostat.StackRuntimeApiWriteRefusalHandler
open E5R E5R.Thermostat HttpRequestSpec RuntimeApiWriteCaller
abbrev B := StackBoard.board
theorem refusal_handler {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {close : Bool}
    (h : StackRuntimeApiWriteCaller.Ready kind future path first c ram input s head amount rawUsed served close) (status : Nat) (outcome : RefusalCase input head amount rawUsed path first status) :
    ∃ d n after, n≤212*(MainRequestInputs.entries head).length+18*(MainRequestSpans.body input head amount).length+514 ∧
      Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ WriteRefusal.Returned c d ∧ StatusMemory.At after 0x80fffd38#32 (BitVec.ofNat 32 status) ∧
      Encoding.SnapshotAt after 0x80ffebc0#32 s ∧ ramRead after 0x80ffebbc#32 .w=0#32 ∧
      Engine.InvariantAt after 0x80ffebbc#32 ∧ MainFutureFrame.At future ram after := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  have outBlock : Memory.Block B 0x80fffd38#32 15 := by
    have block := Memory.sub_block StackBoard.available (off := 64824) (m := 15) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    simpa only [show 0x80ff0000#32+64824#32=0x80fffd38#32 by decide +kernel] using block
  rcases outcome with ⟨denied,rfl⟩|⟨allowed,rejected⟩
  · obtain ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,_,_,frame⟩ := StackMainFutureAuthHandler.contract c ram future
      0x80fff880#32 0x80ffebbc#32 0x80ffec14#32 (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s
      h.pre denied h.invariant outBlock (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    exact ⟨d,n,after,by omega,trace,ret,response,snapshot,borrow,inv,frame⟩
  · obtain ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,_,_,frame⟩ := StackMainFutureDecodeHandler.contract c ram future
      0x80fff880#32 0x80ffebbc#32 0x80ffec14#32 (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s status
      h.pre allowed rejected h.invariant outBlock (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
      (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    exact ⟨d,n,after,bound,trace,ret,response,snapshot,borrow,inv,frame⟩

end E5R.Thermostat.StackRuntimeApiWriteRefusalHandler
