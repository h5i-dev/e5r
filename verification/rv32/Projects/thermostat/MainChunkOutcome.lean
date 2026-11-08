import Projects.thermostat.MainChunkCommit
import Projects.thermostat.MainChunkDispatch
namespace E5R.Thermostat.MainChunkOutcome
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual main entry through persisted state, cursor update and outcome
    dispatch. Data stops at its append path; Nothing has rejoined the loop. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp rx lim index maxBody : Word) (s : CState)
    (h : MainChunkInput.Ready B c ram sp rx lim index maxBody s)
    (hi : ramRead ram (sp+3656#32) .w=index) (h22 : c.get 22=1#32) :
    ∃ n d after, 76≤n ∧ n≤109 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=MainChunkDispatch.continuation (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2 ∧
      ChunkLayout.At after (sp+3680#32) (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      ChunkSpecInvariant.Inv maxBody.toNat (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      ramRead after (sp+3656#32) .w=index+1#32 ∧ d.get 24=index+1#32 ∧
      (∀ status, (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2=.reject status →
        status<65536 → d.get 27=BitVec.ofNat 32 status) ∧
      d.get 2=sp ∧ d.get 8=sp+3204#32 ∧ d.get 23=sp+3680#32 ∧
      d.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat ∧ d.get 22=1#32 ∧
      (∀ x, (∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 36, x≠(sp+4824#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x≠(sp+3656#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 32, x≠(sp+3680#32)+BitVec.ofNat 32 i.val) → after x=ram x) ∧ d.get 10=ChunkOutputView.tag (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2 ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨n,a,after,hlo,hn,commit,pc,st,inv,index2,cursor2,tag2,status2,sp2,fp2,state2,cache2,frame2,r22,stable2,csr2⟩ :=
    MainChunkCommit.contract B c ram sp rx lim index maxBody s h hi
  obtain ⟨k,d,hkl,hku,dispatch,pc3,saved3,csr3⟩ :=
    MainChunkDispatch.contract B a after _ pc tag2 (r22.trans h22)
  refine ⟨n+k,d,after,by omega,by omega,commit.trans dispatch,pc3,st,inv,index2,
    (saved3 24).trans cursor2,?_,(saved3 2).trans sp2,(saved3 8).trans fp2,
    (saved3 23).trans state2,(saved3 20).trans cache2,(saved3 22).trans (r22.trans h22),frame2,(saved3 10).trans tag2,(fun r hr => (saved3 r).trans (stable2 r hr)),csr3.trans csr2⟩
  intro code he hc
  exact (saved3 27).trans (status2 code he hc)

end E5R.Thermostat.MainChunkOutcome
