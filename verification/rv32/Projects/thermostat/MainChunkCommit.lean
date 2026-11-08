import Projects.thermostat.MainChunkExecute
import Projects.thermostat.MainChunkStore
namespace E5R.Thermostat.MainChunkCommit
open E5R E5R.Thermostat HttpRequestSpec

/-- The actual call and subsequent stores establish the next decoder state
    in persisted main RAM. The outcome dispatch at 0x80000f62 follows next. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8)
    (sp rx lim index maxBody : Word) (s : CState)
    (h : MainChunkInput.Ready B c ram sp rx lim index maxBody s)
    (hi : ramRead ram (sp+3656#32) .w=index) :
    ∃ n d after, 75≤n ∧ n≤107 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=0x80000f62#32 ∧
      ChunkLayout.At after (sp+3680#32) (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      ChunkSpecInvariant.Inv maxBody.toNat (chunkStep s (ram (rx+index)).toNat maxBody.toNat).1 ∧
      ramRead after (sp+3656#32) .w=index+1#32 ∧ d.get 24=index+1#32 ∧
      d.get 10=ChunkOutputView.tag (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2 ∧
      (∀ status, (chunkStep s (ram (rx+index)).toNat maxBody.toNat).2=.reject status →
        status<65536 → d.get 27=BitVec.ofNat 32 status) ∧
      d.get 2=sp ∧ d.get 8=sp+3204#32 ∧ d.get 23=sp+3680#32 ∧
      d.get 20=BitVec.ofNat 32 (ram (rx+index)).toNat ∧
      (∀ x, (∀ i : Fin 32, x≠(sp+4864#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 36, x≠(sp+4824#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 4, x≠(sp+3656#32)+BitVec.ofNat 32 i.val) →
        (∀ i : Fin 32, x≠(sp+3680#32)+BitVec.ofNat 32 i.val) → after x=ram x) ∧
      d.get 22=c.get 22 ∧ MainChunkCoreFrame.At c d ∧ d.sameCsr c := by
  obtain ⟨n,a,before,hlo,hn,execute,pc,st,out,inv,sp1,fp1,statePtr1,cursor1,cache1,frame1,r22,stable1,csr1⟩ :=
    MainChunkExecute.contract B c ram sp rx lim index maxBody s h
  have index1 : ramRead before (sp+3656#32) .w=index := by
    calc
      ramRead before (sp+3656#32) .w=ramRead ram (sp+3656#32) .w := by
        apply ramRead_w_congr
        intro k hk
        apply frame1
        · intro j
          exact FrameOffsets.ne sp 3656 4864 k j.val (by omega)
            (by have := j.isLt;omega) (by have := j.isLt;omega)
        · intro j
          exact FrameOffsets.ne sp 3656 4824 k j.val (by omega)
            (by have := j.isLt;omega) (by have := j.isLt;omega)
      _=index := hi
  obtain ⟨d,after,persist,pc2,st2,index2,cursor2,tag2,status2,frame2,saved2,stable2,csr2⟩ :=
    MainChunkStore.contract B a before sp index _ _ pc fp1 statePtr1 h.stack h.align index1 st out
  refine ⟨n+21,d,after,by omega,by omega,execute.trans persist,pc2,st2,inv,index2,cursor2,tag2,status2,
    (saved2 2 (by decide)).trans sp1,(saved2 8 (by decide)).trans fp1,
    (saved2 23 (by decide)).trans statePtr1,(saved2 20 (by decide)).trans cache1,?_,(saved2 22 (by decide)).trans r22,MainChunkCoreFrame.trans stable1 stable2,csr2.trans csr1⟩
  intro x hinput houtput hcursor hstate
  exact (frame2 x hcursor hstate).trans (frame1 x hinput houtput)

end E5R.Thermostat.MainChunkCommit
