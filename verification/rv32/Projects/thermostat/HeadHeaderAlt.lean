import Projects.thermostat.HeadHeaderScratch
import Projects.thermostat.HeadHeaderValueDispatch
import Projects.thermostat.HeadActionCongr
import Projects.thermostat.HeadFieldsConstants
import Projects.thermostat.HeadRegisterFrame
namespace E5R.Thermostat.HeadHeaderAlt
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec

def nameWrites : List Reg := [10,13,31,30,19,12,29,11,14,20]
def valueWrites : List Reg := [1,30,12,29,14,13,11,10,31]
def writes : List Reg := [1,10,13,31,30,19,12,29,11,14,20]

theorem name_ne : ∀ r : Reg, r∉nameWrites →
    r≠10 ∧ r≠13 ∧ r≠31 ∧ r≠30 ∧ r≠19 ∧ r≠12 ∧ r≠29 ∧ r≠11 ∧ r≠14 ∧ r≠20 := by decide +kernel

theorem value_ne : ∀ r : Reg, r∉valueWrites →
    r≠1 ∧ r≠30 ∧ r≠12 ∧ r≠29 ∧ r≠14 ∧ r≠13 ∧ r≠11 ∧ r≠10 ∧ r≠31 := by decide +kernel

/-- Complete actual non-Host classification and value handling, including the
    real scratch-word store. The result uses the original receive bytes. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields)
    (ns ne vs ve le length cap minor : Nat) (hp : c.pc=0x80003192#32)
    (constants : HeadFieldsConstants.At c sp length minor) (h1 : c.get 1=400#32)
    (h23 : c.get 23=(if f.te then 1#32 else 0#32)) (h24 : c.get 24=BitVec.ofNat 32 ns)
    (h25 : c.get 25=BitVec.ofNat 32 ve) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (h14 : c.get 14=BitVec.ofNat 32 (ne-ns)) (h20 : c.get 20=(sp+516#32)+BitVec.ofNat 32 ns)
    (h15 : c.get 15=BitVec.ofNat 32 vs) (h26 : c.get 26=BitVec.ofNat 32 le) (h11 : c.get 11=BitVec.ofNat 32 le)
    (metadata : HeadFieldsMeta.At ram sp length cap) (fields : HeadFieldsView.At ram sp f)
    (ordered : ns<ne ∧ ne<vs ∧ vs≤ve ∧ ve≤le ∧ le≤length) (bound : length≤2048) (version : minor≤1)
    (notHost : ne-ns≠4) (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) :
    let result := HeadActionSpec.action (bytes ram (sp+516#32)) f ns ne vs ve le minor 1024
    ∃ n d after, 4≤n ∧ n≤539+30*(ve-vs) ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderActionView.At d result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      HeadHeaderActionView.Effect (HeadHeaderScratch.memory ram sp ve le) after sp ∧
      HeadRegisterFrame.At c d writes ∧ d.sameCsr c := by
  let buf := sp+516#32
  let mid := HeadHeaderScratch.memory ram sp ve le
  have mem : Memory.Block B buf length := Memory.sub_block stack (off := 516) (by omega) (by omega)
  have stack56 : Memory.Block B sp 56 := by
    simpa only [BitVec.add_zero] using (Memory.sub_block stack (off := 0) (m := 56) (by decide) (by decide))
  obtain ⟨s,scratch,pc0,v10,frame0,csr0⟩ := HeadHeaderScratch.contract B c ram sp ns ve le hp constants.stack h24 h25 h21
    (by omega) (by omega) (by omega) stack56 aligned
  have f0 : HeadRegisterFrame.At c s [10] := by
    intro r safe
    exact frame0 r (fun eq => safe (by simp [eq]))
  have raw : ramRead mid (sp+48#32) .w=BitVec.ofNat 32 length :=
    (HeadHeaderScratch.word_frame ram sp ve le 48 (by decide) (by decide)).trans metadata.raw
  have buffer : ramRead mid (sp+44#32) .w=buf :=
    (HeadHeaderScratch.word_frame ram sp ve le 44 (by decide) (by decide)).trans metadata.buffer
  have limit : ramRead mid (sp+8#32) .w=1024#32 :=
    (HeadHeaderScratch.word_frame ram sp ve le 8 (by decide) (by decide)).trans metadata.body
  obtain ⟨n,a,lo,hi,name,pc1,cache,frame1,csr1⟩ := HeadNameClassify.contract B s mid sp buf ns ne length pc0
    ((f0 2 (by decide)).trans constants.stack) ((f0 24 (by decide)).trans h24) ((f0 14 (by decide)).trans h14)
    ((f0 7 (by decide)).trans constants.maskWidth) ((f0 20 (by decide)).trans h20)
    raw buffer ⟨by omega,by omega⟩ bound notHost mem stack56 aligned clOutside teOutside
  have f1 : HeadRegisterFrame.At s a nameWrites := by
    intro r safe
    obtain ⟨h10,h13,h31,h30,h19,h12,h29,h11,h14,h20⟩ := name_ne r safe
    exact frame1 r h10 h13 h31 h30 h19 h12 h29 h11 h14 h20
  have prefixFrame : HeadRegisterFrame.At c a nameWrites :=
    HeadRegisterFrame.mono (HeadRegisterFrame.trans f0 f1) (by decide +kernel)
  obtain ⟨k,d,after,khi,value,post,view,effect,frame2,csr2⟩ := HeadHeaderValueDispatch.contract B a mid sp buf f ns ne vs ve le length minor pc1
    (HeadClassSpec.non_host_kinds (bytes mid buf) ns ne notHost)
    ((prefixFrame 1 (by decide)).trans h1) ((prefixFrame 2 (by decide)).trans constants.stack)
    ((prefixFrame 23 (by decide)).trans h23) ((prefixFrame 15 (by decide)).trans h15) ((prefixFrame 26 (by decide)).trans h26)
    (fun h => (cache h).trans ((f0 11 (by decide)).trans h11))
    ((prefixFrame 16 (by decide)).trans constants.lf) ((prefixFrame 18 (by decide)).trans constants.inverse)
    ((prefixFrame 24 (by decide)).trans h24) ((prefixFrame 21 (by decide)).trans h21)
    (HeadHeaderScratch.scratch_word ram sp ve le) buffer raw limit (HeadHeaderScratch.fields ve le fields)
    ⟨by omega,ordered.2.2.1,ordered.2.2.2.1,ordered.2.2.2.2⟩ bound version mem stack aligned
  have f2 : HeadRegisterFrame.At a d valueWrites := by
    intro r safe
    obtain ⟨h1,h30,h12,h29,h14,h13,h11,h10,h31⟩ := value_ne r safe
    exact frame2 r h1 h30 h12 h29 h14 h13 h11 h10 h31
  have spec : HeadActionSpec.action (bytes mid buf) f ns ne vs ve le minor 1024=
      HeadActionSpec.action (bytes ram buf) f ns ne vs ve le minor 1024 :=
    HeadActionCongr.action_congr (bytes mid buf) (bytes ram buf) f ns ne vs ve le minor 1024 2048
      (by omega) (by omega) (HeadHeaderScratch.rx ram sp ve le)
  rw [spec] at post view
  exact ⟨3+n+k,d,after,by omega,by omega,(scratch.trans name).trans value,post,view,effect,
    HeadRegisterFrame.mono (HeadRegisterFrame.trans prefixFrame f2) (by decide +kernel),csr2.trans (csr1.trans csr0)⟩
end E5R.Thermostat.HeadHeaderAlt
