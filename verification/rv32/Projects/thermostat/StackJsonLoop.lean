import Projects.thermostat.JsonLoopQuiet
import Projects.thermostat.StackAccess
import Projects.thermostat.StackFormatLayout
import Projects.thermostat.StackJsonArgument
import Projects.thermostat.StackJsonLiteral
set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.StackJsonLoop
open E5R E5R.Thermostat JsonLoop
theorem contract_quiet (count : Nat) (hcount : count ≤ 8) (c : Core) (ram : Word → BitVec 8) (p obj args dst : Word)
    (cap : Nat) (litPrefix : List (BitVec 8)) (values : Fin 8 → FormatValue.Value)
    (hr : FormatEngineReady.Ready c (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*(8-count),by omega⟩)
      (8-count) (JsonFormatData.tagByte ⟨2*(8-count),by omega⟩))
    (h : StackFormatLayout.Layout ram p obj args dst cap litPrefix.length values)
    (hx : Bytes.Span StackBoard.board ram dst litPrefix)
    (hf : litPrefix.length+(JsonSequence.suffix values count).length ≤ cap) :
    ∃ d n r, n ≤ 456*count+144 ∧ Quiet.Steps StackBoard.board img n ⟨c,ram⟩ ⟨d,r⟩ ∧
      d.pc = 0x80004b12#32 ∧ d.get 2 = p+160#32 ∧ d.get 27 = c.get 27 ∧ d.sameCsr c ∧
      StackFormatLayout.Layout r p obj args dst cap (litPrefix++JsonSequence.suffix values count).length values ∧
      Bytes.Span StackBoard.board r dst (litPrefix++JsonSequence.suffix values count) ∧
      FormatLoopFrame.Frame ram r p obj dst cap := by
  induction count generalizing c ram litPrefix with
  | zero =>
    obtain ⟨d,n,r,hb,td,hpc,hsp,_,h27,hc,hl,hs,hfr⟩ := E5R.Thermostat.StackJsonLiteral.contract_quiet c ram p obj args dst cap litPrefix values 8 hr h hx hf
    refine ⟨d,n,r,by omega,td,?_,hsp,h27,hc,hl,hs,hfr⟩
    change d.pc = FormatEngineNext.resultPc (0#8) at hpc
    exact hpc
  | succ count ih =>
    have hn : count ≤ 7 := by omega
    let i : Fin 8 := ⟨7-count,by omega⟩
    let j : Fin 9 := ⟨7-count,by omega⟩
    have hidx : 8-(count+1) = 7-count := by omega
    have hsucc : (7-count)+1 = 8-count := by omega
    have litmod : Fin.ofNat 9 (7-count) = j := by apply Fin.ext;change (7-count)%9 = 7-count;omega
    have argmod : Fin.ofNat 8 (7-count) = i := by apply Fin.ext;change (7-count)%8 = 7-count;omega
    have hseq : JsonSequence.suffix values (count+1) = JsonProgram.literal j ++ FormatValue.bytes (values i) ++ JsonSequence.suffix values count := by
      simp only [JsonSequence.suffix,litmod,argmod]
    have hrj : FormatEngineReady.Ready c (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*j.val,by have := j.isLt;omega⟩)
        j.val (JsonFormatData.tagByte ⟨2*j.val,by have := j.isLt;omega⟩) := by simpa only [hidx,j] using hr
    have hfl : litPrefix.length+(JsonProgram.literal j).length ≤ cap := by rw [hseq,List.length_append,List.length_append] at hf;omega
    obtain ⟨a,na,ra,hna,ta,_,_,har,ha27,hac,hla,hsa,hfa⟩ := E5R.Thermostat.StackJsonLiteral.contract_quiet c ram p obj args dst cap litPrefix values j hrj h hx hfl
    have harr : FormatEngineReady.Ready a (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*i.val+1,by have := i.isLt;omega⟩)
        i.val (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩) :=
      har (by change (JsonFormatData.tagByte ⟨2*i.val+1,by have := i.isLt;omega⟩).toNat ≠ 0;rw [JsonFormatData.argument_tag];decide)
    have hfb : (litPrefix++JsonProgram.literal j).length+(FormatValue.bytes (values i)).length ≤ cap := by
      rw [hseq,List.length_append,List.length_append] at hf;rw [List.length_append];omega
    obtain ⟨b,nb,rb,hnb,tb,hbr,hb27,hbc,hlb,hsb,hfbfr⟩ := E5R.Thermostat.StackJsonArgument.contract_quiet a ra p obj args dst cap
      (litPrefix++JsonProgram.literal j) values i harr hla hsa hfb
    have hbr' : FormatEngineReady.Ready b (p+160#32) obj args (JsonFormatData.tagPointer ⟨2*(8-count),by omega⟩)
        (8-count) (JsonFormatData.tagByte ⟨2*(8-count),by omega⟩) := by simpa only [i,hsucc] using hbr
    have hfc : ((litPrefix++JsonProgram.literal j)++FormatValue.bytes (values i)).length+(JsonSequence.suffix values count).length ≤ cap := by
      rw [hseq,List.length_append,List.length_append] at hf;rw [List.length_append,List.length_append];omega
    obtain ⟨d,nd,r,hnd,td,hpc,hsp,h27,hc,hl,hs,hfr⟩ := ih (by omega) b rb
      ((litPrefix++JsonProgram.literal j)++FormatValue.bytes (values i)) hbr' hlb hsb hfc
    refine ⟨d,na+nb+nd,r,by omega,(ta.trans tb).trans td,hpc,hsp,(h27.trans hb27).trans ha27,
      (hc.trans hbc).trans hac,?_,?_,FormatLoopFrame.trans (FormatLoopFrame.trans hfa hfbfr) hfr⟩
    · simpa only [hseq,List.append_assoc] using hl
    · simpa only [hseq,List.append_assoc] using hs

end E5R.Thermostat.StackJsonLoop
