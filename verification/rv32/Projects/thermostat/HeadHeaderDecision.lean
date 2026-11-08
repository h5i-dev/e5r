import Projects.thermostat.HeadHeaderCapacity
import Projects.thermostat.HeadHeaderWidth
import Projects.thermostat.HeadHeaderTooMany
import Projects.thermostat.HeadHeaderDecisionSpec
import Projects.thermostat.HeadHeaderMemoryFrame
namespace E5R.Thermostat.HeadHeaderDecision
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def writes : List Reg := HeadHeaderAlt.writes

theorem constants_safe : ∀ r : Reg, r∈HeadFieldsConstants.protectedRegs → r∉[10] := by decide +kernel

/-- Actual complete add_header decision, including capacity, Host and all CL/TE
    value rules. The four header-array words are appended by the next block. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields)
    (ns ne vs ve le length cap minor : Nat) (hp : c.pc=0x800030fa#32)
    (constants : HeadFieldsConstants.At c sp length minor) (h1 : c.get 1=400#32)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (h24 : c.get 24=BitVec.ofNat 32 ns) (h25 : c.get 25=BitVec.ofNat 32 ve) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h20 : c.get 20=(sp+516#32)+BitVec.ofNat 32 ns)
    (h15 : c.get 15=BitVec.ofNat 32 vs) (h26 : c.get 26=BitVec.ofNat 32 le) (h11 : c.get 11=BitVec.ofNat 32 le)
    (metadata : HeadFieldsMeta.At ram sp length cap) (fields : HeadFieldsView.At ram sp f)
    (ordered : ns<ne ∧ ne<vs ∧ vs≤ve ∧ ve≤le ∧ le≤cap) (hcap : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let result := HeadHeaderDecisionSpec.result (bytes ram (sp+516#32)) f ns ne vs ve le minor
    ∃ n d after, 4≤n ∧ n≤600+30*(le-ns) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderActionView.At d result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      HeadHeaderMemoryFrame.At ram after sp ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c := by
  let g := bytes ram (sp+516#32)
  obtain ⟨a,capacity,pc,v10,frame,csr⟩ := HeadHeaderCapacity.contract B c ram f.headers.length hp h9 fields.count_bound
  have f0 : HeadRegisterFrame.At c a [10] := by
    intro r safe
    exact frame r (fun eq => safe (by simp [eq]))
  by_cases full : 16≤f.headers.length
  · have atFull : a.pc=0x800034d4#32 := by simpa only [full,ite_true] using pc
    obtain ⟨d,reject,pc2,status,frame2,csr2⟩ := HeadHeaderTooMany.contract B a ram atFull
    have f1 : HeadRegisterFrame.At a d [1] := by
      intro r safe
      exact frame2 r (fun eq => safe (by simp [eq]))
    have spec : HeadHeaderDecisionSpec.result g f ns ne vs ve le minor=.bad 431 := by
      simp only [HeadHeaderDecisionSpec.result,full,ite_true]
    change ∃ n d after, _
    rw [show HeadHeaderDecisionSpec.result (bytes ram (sp+516#32)) f ns ne vs ve le minor=.bad 431 from spec]
    exact ⟨4,d,ram,by decide,by omega,by simpa using capacity.trans reject,⟨pc2,status⟩,fields,
      HeadHeaderMemoryFrame.refl ram sp,HeadRegisterFrame.mono (HeadRegisterFrame.trans f0 f1) (by decide +kernel),csr2.trans csr⟩
  · have atWidth : a.pc=0x80003100#32 := by simpa only [full,ite_false] using pc
    obtain ⟨b,width,pc2,four,frame2,csr2⟩ := HeadHeaderWidth.contract B a ram (ne-ns) atWidth
      ((frame 14 (by decide)).trans h14) (by omega)
    have prefixFrame : HeadRegisterFrame.At c b [10] := by
      intro r safe
      have ne10 : r≠10 := fun eq => safe (by simp [eq])
      exact (frame2 r ne10).trans (frame r ne10)
    have constantsB : HeadFieldsConstants.At b sp length minor :=
      HeadFieldsConstants.preserve constants (fun r h => prefixFrame r (constants_safe r h))
    by_cases otherWidth : ne-ns≠4
    · have atAlt : b.pc=0x80003192#32 := by simpa [otherWidth] using pc2
      obtain ⟨n,d,after,lo,hi,alt,post,view,effect,frame3,csr3⟩ := HeadHeaderAlt.contract B b ram sp f ns ne vs ve le length cap minor atAlt constantsB
        ((prefixFrame 1 (by decide)).trans h1) ((prefixFrame 23 (by decide)).trans h23)
        ((prefixFrame 24 (by decide)).trans h24) ((prefixFrame 25 (by decide)).trans h25)
        ((prefixFrame 21 (by decide)).trans h21) ((prefixFrame 14 (by decide)).trans h14)
        ((prefixFrame 20 (by decide)).trans h20) ((prefixFrame 15 (by decide)).trans h15)
        ((prefixFrame 26 (by decide)).trans h26) ((prefixFrame 11 (by decide)).trans h11)
        metadata fields ⟨ordered.1,ordered.2.1,ordered.2.2.1,ordered.2.2.2.1,by omega⟩ bound version otherWidth stack aligned clOutside teOutside
      have spec : HeadHeaderDecisionSpec.result g f ns ne vs ve le minor=HeadActionSpec.action g f ns ne vs ve le minor 1024 := by
        simp only [HeadHeaderDecisionSpec.result,full,ite_false]
      change ∃ n d after, _
      rw [show HeadHeaderDecisionSpec.result (bytes ram (sp+516#32)) f ns ne vs ve le minor=HeadActionSpec.action (bytes ram (sp+516#32)) f ns ne vs ve le minor 1024 from spec]
      exact ⟨2+2+n,d,after,by omega,by omega,(capacity.trans width).trans alt,post,view,HeadHeaderMemoryFrame.alt ve le effect,
        HeadRegisterFrame.mono (HeadRegisterFrame.trans prefixFrame frame3) (by decide +kernel),csr3.trans (csr2.trans csr)⟩
    · have exactWidth : ne=ns+4 := by omega
      have atHost : b.pc=0x80003106#32 := by simpa [otherWidth] using pc2
      have mem : Memory.Block B (sp+516#32) length := Memory.sub_block stack (off := 516) (by omega) (by omega)
      obtain ⟨n,d,after,lo,hi,host,post,view,effect,frame3,csr3⟩ := HeadHeaderHost.contract B b ram sp (sp+516#32) ns vs ve le length minor f atHost
        ((prefixFrame 1 (by decide)).trans h1) constantsB.stack ((prefixFrame 24 (by decide)).trans h24)
        metadata.raw metadata.buffer fields (by omega) bound mem stack aligned
      have spec : HeadHeaderDecisionSpec.result g f ns ne vs ve le minor=HeadActionSpec.action g f ns (ns+4) vs ve le minor 1024 := by
        simp only [HeadHeaderDecisionSpec.result,full,ite_false,exactWidth]
      change ∃ n d after, _
      rw [show HeadHeaderDecisionSpec.result (bytes ram (sp+516#32)) f ns ne vs ve le minor=HeadActionSpec.action (bytes ram (sp+516#32)) f ns (ns+4) vs ve le minor 1024 from spec]
      exact ⟨2+2+n,d,after,by omega,by omega,(capacity.trans width).trans host,post,view,HeadHeaderMemoryFrame.host effect,
        HeadRegisterFrame.mono (HeadRegisterFrame.trans prefixFrame frame3) (by decide +kernel),csr3.trans (csr2.trans csr)⟩
end E5R.Thermostat.HeadHeaderDecision
