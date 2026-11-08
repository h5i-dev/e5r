import Projects.thermostat.HeadFieldLine
import Projects.thermostat.HeadFieldsStart
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadFieldLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (hi : i<cap) (hn : cap≤length) (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 10≤n ∧ n≤44+78*(cap-i) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadFieldLineSpec.At d after sp i (HeadFieldLineSpec.next g i cap) ∧
      ViewFrame.Region ram after (sp+8#32) 5304 ∧ HeadFieldsMeta.At after sp length cap ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → r≠30 → r≠15 → r≠26 → r≠1 → r≠20 → r≠12 → r≠31 → r≠19 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,result,region,metadataAfter,frame,csr⟩ := contract B c ram sp i cap length minor f regs metadata hi hn hlen hm ha
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,result,region,metadataAfter,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldLine
namespace E5R.Thermostat.HeadFieldsStart
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hn : cap≤1024)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) (masked : c.mie_=false) :
    ∃ n d after, 239≤n ∧ n≤257 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      (if cap≤j+2 then d.pc=0x800033ea#32 else HeadFieldsRegs.At d sp (j+2) length minor Fields.empty) ∧
      HeadFieldsView.At after sp Fields.empty ∧ ViewFrame.Region ram after (sp+20#32) 36 ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧ ViewFrame.Region ram after (sp+428#32) 25 ∧
      HeadSaved.At after sp values ∧ d.get 2=sp ∧ d.sameCsr c ∧ (j+2<cap → HeadFieldsMeta.At after sp length cap) ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,next,view,metadata,rx,app,saved,stack,csr,scratch⟩ := contract B c ram sp m te j minor length cap values ready hbody hj hn hm ha stored
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,next,view,metadata,rx,app,saved,stack,csr,scratch,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsStart
