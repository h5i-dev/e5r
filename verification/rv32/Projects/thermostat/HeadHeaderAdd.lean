import Projects.thermostat.HeadHeaderDecision
import Projects.thermostat.HeadHeaderAddFrame
namespace E5R.Thermostat.HeadHeaderAdd
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def writes : List Reg := [1,10,13,31,30,19,12,29,11,14,20,9,23,21,24]

def Post (c : Core) (sp : Word) (le length cap minor : Nat) : Added → Prop
  | .bad status => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 status
  | .ok f => if le+2<cap then HeadFieldsRegs.At c sp (le+2) length minor f else c.pc=0x800033ea#32

theorem constants_safe : ∀ r : Reg, r∈HeadFieldsConstants.protectedRegs → r∉HeadHeaderDecision.writes := by decide +kernel

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields)
    (ns ne vs ve le length cap minor : Nat) (hp : c.pc=0x800030fa#32)
    (constants : HeadFieldsConstants.At c sp length minor) (h1 : c.get 1=400#32)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (h24 : c.get 24=BitVec.ofNat 32 ns) (h25 : c.get 25=BitVec.ofNat 32 ve) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h20 : c.get 20=(sp+516#32)+BitVec.ofNat 32 ns)
    (h15 : c.get 15=BitVec.ofNat 32 vs) (h26 : c.get 26=BitVec.ofNat 32 le) (h11 : c.get 11=BitVec.ofNat 32 le)
    (hname : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 ne)
    (metadata : HeadFieldsMeta.At ram sp length cap) (fields : HeadFieldsView.At ram sp f)
    (ordered : ns<ne ∧ ne<vs ∧ vs≤ve ∧ ve≤le ∧ le≤cap) (hcap : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let result := addHeader (bytes ram (sp+516#32)) f ns ne vs ve le minor 1024
    ∃ n d after, 4≤n ∧ n≤618+30*(le-ns) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post d sp le length cap minor result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadHeaderAddFrame.At ram after sp ∧
      HeadRegisterFrame.At c d writes ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  let entry : Field := ⟨ns,ne,vs,ve⟩
  obtain ⟨n,a,mid,lo,hi,decision,post,view,memoryFrame,frame,csr⟩ := HeadHeaderDecision.contract B c ram sp f ns ne vs ve le length cap minor hp constants h1 h9 h23 h24 h25 h21 h14 h20 h15 h26 h11 metadata fields ordered hcap bound version stack aligned clOutside teOutside
  change HeadHeaderActionView.At a (HeadHeaderDecisionSpec.result g f ns ne vs ve le minor) at post
  change HeadFieldsView.At mid sp (HeadHeaderActionView.stored f (HeadHeaderDecisionSpec.result g f ns ne vs ve le minor)) at view
  have metadataMid := HeadHeaderMemoryFrame.metadata memoryFrame metadata
  have spec := HeadHeaderDecisionSpec.addHeader g f ns ne vs ve le minor
  change ∃ n d after, _
  rw [show addHeader (bytes ram (sp+516#32)) f ns ne vs ve le minor 1024=
    HeadActionSpec.append f entry (HeadHeaderDecisionSpec.result g f ns ne vs ve le minor) from spec]
  cases selected : HeadHeaderDecisionSpec.result g f ns ne vs ve le minor with
  | bad status =>
    have got : a.pc=0x8000342c#32 ∧ a.get 1=BitVec.ofNat 32 status := by
      simpa only [HeadHeaderActionView.At,selected] using post
    have fieldsMid : HeadFieldsView.At mid sp f := by simpa only [HeadHeaderActionView.stored,selected] using view
    exact ⟨n,a,mid,lo,by omega,decision,got,fieldsMid,metadataMid,HeadHeaderAddFrame.of_decision memoryFrame,
      HeadRegisterFrame.mono frame (by decide +kernel),csr⟩
  | ok next =>
    have atCommit : a.pc=0x800033b6#32 := by simpa only [HeadHeaderActionView.At,selected] using post
    have fieldsMid : HeadFieldsView.At mid sp next := by simpa only [HeadHeaderActionView.stored,selected] using view
    obtain ⟨headersSame,room⟩ := HeadHeaderDecisionSpec.accepted g f next ns ne vs ve le minor selected
    have constantsMid : HeadFieldsConstants.At a sp length minor :=
      HeadFieldsConstants.preserve constants (fun r h => frame r (constants_safe r h))
    have count : a.get 9=BitVec.ofNat 32 next.headers.length := by
      rw [headersSame]
      exact (frame 9 (by decide)).trans h9
    have nameWord : ramRead mid (sp+4#32) .w=BitVec.ofNat 32 ne :=
      (HeadHeaderMemoryFrame.word memoryFrame 4 (by decide) (by decide) (by decide)).trans hname
    obtain ⟨d,commit,nextLoop,fieldsAfter,metadataAfter,countAfter,posAfter,teAfter,frame2,csr2⟩ := HeadHeaderCommit.contract B a mid sp entry le length cap minor next atCommit constantsMid fieldsMid metadataMid count
      ((frame 24 (by decide)).trans h24) ((frame 15 (by decide)).trans h15) ((frame 25 (by decide)).trans h25)
      ((frame 21 (by decide)).trans h21) nameWord room (by change ns≤le;omega) ordered.2.2.2.2 hcap bound stack aligned
    have f2 : HeadRegisterFrame.At a d [9,10,23,11,21,24] := by
      intro r safe
      have facts : ∀ r : Reg, r∉[9,10,23,11,21,24] → r≠9 ∧ r≠10 ∧ r≠23 ∧ r≠11 ∧ r≠21 ∧ r≠24 := by decide +kernel
      obtain ⟨h9,h10,h23,h11,h21,h24⟩ := facts r safe
      exact frame2 r h9 h10 h23 h11 h21 h24
    have finalFields : {next with headers := next.headers++[entry]}={next with headers := f.headers++[entry]} := by rw [headersSame]
    rw [finalFields] at fieldsAfter nextLoop
    exact ⟨n+18,d,HeadHeaderCommitMemory.memory mid sp next.headers.length entry,by omega,by omega,decision.trans commit,
      nextLoop,fieldsAfter,metadataAfter,HeadHeaderAddFrame.commit memoryFrame next.headers.length entry room,
      HeadRegisterFrame.mono (HeadRegisterFrame.trans frame f2) (by decide +kernel),csr2.trans csr⟩
end E5R.Thermostat.HeadHeaderAdd
