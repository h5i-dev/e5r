import Projects.thermostat.MainChunkInput
namespace E5R.Thermostat.MainChunkExecute
open E5R E5R.Thermostat HttpRequestSpec

/-- Actual main argument construction and the complete decoder. The next
    state is still in the return object; the following main stores persist it. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp rx lim index maxBody : Word) (s : CState)
    (h : MainChunkInput.Ready B c ram sp rx lim index maxBody s) :
    ∃ n d after, 54≤n ∧ n≤86 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x80000f10#32 ∧
      ChunkLayout.At after (sp+4824#32) (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      ChunkLayout.OutAt after (sp+4824#32) (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2 ∧
      ChunkSpecInvariant.Inv maxBody.toNat (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      d.get 2=sp ∧ d.get 8=sp+3204#32 ∧ d.get 23=sp+3680#32 ∧ d.get 24=index ∧
      d.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat ∧
      (∀ x, (∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 36, x≠(sp+4824#32)+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      d.get 22=c.get 22 ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨a,before,call,pre,ra,sp1,fp1,statePtr1,cursor1,cache1,frame1,r22,stable1,csr1⟩ :=
    MainChunkInput.call B c ram sp rx lim index maxBody s h
  obtain ⟨n,d,after,hlo,hn,trace,post,inv⟩ :=
    ChunkStep.contract B a before (sp+4864#32) (sp+4824#32) s (ram (rx+index)) maxBody.toNat pre
  have ret : d.pc=0x80000f10#32 := by
    simpa only [ra,show 0x80000f10#32 &&& ~~~1=0x80000f10#32 by decide +kernel] using post.1
  have saved := post.2.2.2.2.1
  refine ⟨30+n,d,after,by omega,by omega,call.trans trace,ret,post.2.1,post.2.2.1,inv,
    (saved 2 (by decide)).trans sp1,(saved 8 (by decide)).trans fp1,
    (saved 23 (by decide)).trans statePtr1,(saved 24 (by decide)).trans cursor1,
    (saved 20 (by decide)).trans cache1,?_,(saved 22 (by decide)).trans r22,(fun r hr => (saved r (MainChunkCoreFrame.callee_saved hr)).trans (stable1 r hr)),post.2.2.2.2.2.trans csr1⟩
  intro x hi ho
  exact (post.2.2.2.1 x ho).trans (frame1 x hi)

end E5R.Thermostat.MainChunkExecute
