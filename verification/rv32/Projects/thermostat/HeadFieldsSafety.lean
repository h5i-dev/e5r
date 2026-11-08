import Projects.thermostat.HeadHeaderAdd
import Projects.thermostat.HeadFieldsStep
import Projects.thermostat.HeadFieldsLoop
import Projects.thermostat.HeadFieldsInitialized
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadHeaderAdd
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (f : Fields)
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
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) (masked : c.mie_=false) :
    let result := addHeader (bytes ram (sp+516#32)) f ns ne vs ve le minor 1024
    ∃ n d after, 4≤n ∧ n≤618+30*(le-ns) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post d sp le length cap minor result ∧ HeadFieldsView.At after sp (HeadHeaderActionView.stored f result) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadHeaderAddFrame.At ram after sp ∧
      HeadRegisterFrame.At c d writes ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,view,metadataAfter,memoryFrame,regFrame,csr⟩ := contract B c ram sp f ns ne vs ve le length cap minor hp constants h1 h9 h23 h24 h25 h21 h14 h20 h15 h26 h11 hname metadata fields ordered hcap bound version stack aligned clOutside teOutside
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,view,metadataAfter,memoryFrame,regFrame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHeaderAdd
namespace E5R.Thermostat.HeadFieldsStep
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (fields : HeadFieldsView.At ram sp f) (inside : i<cap) (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) (masked : c.mie_=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 10≤n ∧ n≤662+108*(cap-i) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp length minor (HeadFieldsStepSpec.one g i cap minor f) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadFieldsConstants.At d sp length minor ∧
      HeadFieldsStepFrame.At ram after sp ∧ HeadRegisterFrame.At c d writes ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,metadataAfter,constantsAfter,memoryFrame,regFrame,csr⟩ := contract B c ram sp i cap length minor f regs metadata fields inside upper bound version stack aligned clOutside teOutside
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,metadataAfter,constantsAfter,memoryFrame,regFrame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsStep
namespace E5R.Thermostat.HeadFieldsLoop
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (g : Nat → Nat)
    (i cap length minor : Nat) (f : Fields)
    (regs : HeadFieldsRegs.At c sp i length minor f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (fields : HeadFieldsView.At ram sp f) (agree : ∀ k, k<cap → bytes ram (sp+516#32) k=g k)
    (inside : i<cap) (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) (masked : c.mie_=false) :
    ∃ n d after, 10≤n ∧ n≤budget cap f.headers.length ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      At d after sp length minor (HttpRequestSpec.fields g cap minor 1024 i f) ∧
      HeadFieldsMeta.At after sp length cap ∧ HeadFieldsConstants.At d sp length minor ∧
      HeadFieldsStepFrame.At ram after sp ∧ HeadRegisterFrame.At c d HeadFieldsStep.writes ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,metadataAfter,constantsAfter,memoryFrame,regFrame,csr⟩ := contract B c ram sp g i cap length minor f regs metadata fields agree inside upper bound version stack aligned clOutside teOutside
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,metadataAfter,constantsAfter,memoryFrame,regFrame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsLoop
namespace E5R.Thermostat.HeadFieldsInitialized
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word)
    (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hc : cap≤1024)
    (upper : cap≤length) (bound : length≤2048) (version : minor≤1)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (stored : HeadSaved.At ram sp values)
    (clOutside : ∀ q : Fin 14, B.inRam (BitVec.ofNat 32 (0x80005de0+q.val)) 1=false)
    (teOutside : ∀ q : Fin 17, B.inRam (BitVec.ofNat 32 (0x80005dee+q.val)) 1=false) (masked : c.mie_=false) :
    let g := bytes ram (sp+516#32)
    ∃ n d after, 239≤n ∧ n≤257+HeadFieldsLoop.budget cap 0 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadFieldsLoop.At d after sp length minor (fields g cap minor 1024 (j+2) Fields.empty) ∧
      ViewFrame.Region ram after (sp+20#32) 36 ∧ ViewFrame.Region ram after (sp+327#32) 4985 ∧
      HeadSaved.At after sp values ∧ d.get 2=sp ∧ d.sameCsr c ∧
      (j+2<cap → HeadFieldsMeta.At after sp length cap) ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,scratchFrame,tailFrame,saved,stackAfter,csr,metadataAfter⟩ := contract B c ram sp m te j minor length cap values ready hbody hj hc upper bound version stack aligned stored clOutside teOutside
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,scratchFrame,tailFrame,saved,stackAfter,csr,metadataAfter,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsInitialized
