import Projects.thermostat.HeadHostCompare
import Projects.thermostat.HeadHost
import Projects.thermostat.HeadHeaderClass4
import Projects.thermostat.HeadColdLineOnly
import Projects.thermostat.HeadHeaderCommit
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadHostCompare
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat)
    (hp : c.pc=0x8000310a#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start) (h10 : c.get 10=buf+BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (width : start+4≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    ∃ n d, 7≤n ∧ n≤36 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if HeadHostSpec.Prefix g start then 0x80003182#32 else 0x800033b6#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,frame,csr⟩ := contract B c ram sp buf start length hp h2 h24 h10 hraw width hlen mem stack ha
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHostCompare
namespace E5R.Thermostat.HeadHost
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start length : Nat) (f : Fields)
    (hp : c.pc=0x80003106#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (fields : HeadFieldsView.At ram sp f) (width : start+4≤length) (hlen : length≤2048) (mem : Memory.Block B buf length)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    ∃ n d after, 9≤n ∧ n≤43 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if classify g start (start+4)=1 ∧ f.host then 0x8000342c#32 else 0x800033b6#32) ∧
      HeadFieldsView.At after sp (updated g start f) ∧ (after=ram ∨ after=HeadHostFlagStore.memory ram sp) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,pc,view,effect,frame,csr⟩ := contract B c ram sp buf start length f hp h2 h24 hraw hbuf fields width hlen mem hm ha
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,pc,view,effect,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHost
namespace E5R.Thermostat.HeadHeaderClass4
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start ne length : Nat) (f : Fields)
    (hp : c.pc=0x800030fa#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h14 : c.get 14=BitVec.ofNat 32 (ne-start))
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (fields : HeadFieldsView.At ram sp f) (lower : start≤ne) (upper : ne≤length) (hlen : length≤2048)
    (mem : Memory.Block B buf length) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    ∃ n d after, 4≤n ∧ n≤47 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ d.pc=endpoint g start ne f ∧
      (d.pc=0x8000342c#32 → d.get 1=(if 16≤f.headers.length then 431#32 else 400#32)) ∧
      HeadFieldsView.At after sp (updated g start ne f) ∧ (after=ram ∨ after=HeadHostFlagStore.memory ram sp) ∧
      (ne-start≠4 → d.get 14=BitVec.ofNat 32 (ne-start) ∧ d.get 11=c.get 11) ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,pc,status,view,effect,widthCache,frame,csr⟩ := contract B c ram sp buf start ne length f hp h1 h2 h24 h9 h14 hraw hbuf fields lower upper hlen mem hm ha
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,pc,status,view,effect,widthCache,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHeaderClass4
namespace E5R.Thermostat.HeadColdLineOnly
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (input : List (BitVec 8))
    (hp : c.pc=0x80002c46#32) (h2 : c.get 2=sp+384#32) (h10 : c.get 10=sp+4904#32)
    (h11 : c.get 11=sp+516#32) (h12 : c.get 12=BitVec.ofNat 32 input.length) (h13 : c.get 13=sp+3664#32)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (hlen : input.length≤2048)
    (hmax : ramRead ram (sp+3664#32) .w=1024#32) (bytesAt : Bytes.At ram (sp+516#32) input)
    (complete : HeadByteInput.term input=0)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (noHeader : min input.length 1024≤HeadRequestInputStorage.line input+2) (masked : c.mie_=false) :
    ∃ steps d after, 19≤steps ∧ steps≤435+36*min input.length 1024 ∧ Trace.Closed B img steps ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=c.get 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d c.get ∧
      HeadResultView.At after (sp+4904#32) (HttpRequestBytes.parse input 1024 1024) ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧
      (sp=0x80ffea10#32 → ∀ state, AppState.At ram state → AppState.At after state) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<steps → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨steps,d,after,hlo,hi,trace,pc,stack,abi,result,rx,app,csr⟩ := contract B c ram sp input hp h2 h10 h11 h12 h13 hm ha hlen hmax bytesAt complete hbody noHeader
  exact ⟨steps,d,after,hlo,hi,Interrupt.close trace.det masked,pc,stack,abi,result,rx,app,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadColdLineOnly
namespace E5R.Thermostat.HeadHeaderCommit
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (entry : Field) (le length cap minor : Nat) (f : Fields)
    (hp : c.pc=0x800033b6#32) (constants : HeadFieldsConstants.At c sp length minor)
    (fields : HeadFieldsView.At ram sp f) (metadata : HeadFieldsMeta.At ram sp length cap)
    (h9 : c.get 9=BitVec.ofNat 32 f.headers.length) (h24 : c.get 24=BitVec.ofNat 32 entry.ns)
    (h15 : c.get 15=BitVec.ofNat 32 entry.vs) (h25 : c.get 25=BitVec.ofNat 32 entry.ve)
    (h21 : c.get 21=BitVec.ofNat 32 (le-entry.ns)) (hname : ramRead ram (sp+4#32) .w=BitVec.ofNat 32 entry.ne)
    (room : f.headers.length<16) (lower : entry.ns≤le) (upper : le≤cap) (hcap : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let after := HeadHeaderCommitMemory.memory ram sp f.headers.length entry
    let nextFields := {f with headers := f.headers++[entry]}
    ∃ d, Trace.Closed B img 18 ⟨c,ram⟩ ⟨d,after⟩ ∧
      (if le+2<cap then HeadFieldsRegs.At d sp (le+2) length minor nextFields else d.pc=0x800033ea#32) ∧
      HeadFieldsView.At after sp nextFields ∧ HeadFieldsMeta.At after sp length cap ∧
      d.get 9=BitVec.ofNat 32 nextFields.headers.length ∧ d.get 24=BitVec.ofNat 32 (le+2) ∧
      d.get 23=(if f.te then 1#32 else 0#32) ∧
      (∀ r : Reg, r≠9 → r≠10 → r≠23 → r≠11 → r≠21 → r≠24 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<18 → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨d,trace,next,view,metadataAfter,count,position,te,frame,csr⟩ := contract B c ram sp entry le length cap minor f hp constants fields metadata h9 h24 h15 h25 h21 hname room lower upper hcap hlen hm ha
  exact ⟨d,Interrupt.close trace.det masked,next,view,metadataAfter,count,position,te,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHeaderCommit
