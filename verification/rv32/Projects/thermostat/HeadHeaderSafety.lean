import Projects.thermostat.HeadFieldsBegin
import Projects.thermostat.HeadFieldsLine
import Projects.thermostat.HeadFieldsMore
import Projects.thermostat.HeadName
import Projects.thermostat.HeadFieldsReject
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadFieldsBegin
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (m te j minor length cap : Nat) (values : Reg → Word)
    (ready : HeadLineReady.At c ram sp m te j minor length cap)
    (hbody : ramRead ram (sp+3668#32) .w=1024#32) (hj : j≤1024) (hn : cap≤1024)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) (masked : c.mie_=false) :
    ∃ n d after, 239≤n ∧ n≤257 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      (if cap≤j+2 then d.pc=0x800033ea#32 else HeadFieldsRegs.At d sp (j+2) length minor Fields.empty) ∧
      HeadFieldsView.At after sp Fields.empty ∧ ViewFrame.Region ram after (sp+20#32) 36 ∧
      ViewFrame.Region ram after (sp+516#32) 2048 ∧ ViewFrame.Region ram after (sp+428#32) 25 ∧
      HeadSaved.At after sp values ∧ d.get 2=sp ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,next,view,metadata,rx,app,saved,stack,csr⟩ := contract B c ram sp m te j minor length cap values ready hbody hj hn hm ha stored
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,next,view,metadata,rx,app,saved,stack,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsBegin
namespace E5R.Thermostat.HeadFieldsLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (i cap length : Nat)
    (hp : c.pc=0x80002f58#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 i)
    (h16 : c.get 16=10#32) (h17 : c.get 17=13#32)
    (hcap : ramRead ram (sp+40#32) .w=BitVec.ofNat 32 cap)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : i<cap) (hn : cap≤length) (hlen : length≤2048)
    (hm : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    let k := lineEnd g i cap
    ∃ n d, 10≤n ∧ n≤18+14*(cap-i) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint g i k cap ∧
      d.get 21=BitVec.ofNat 32 (k-i) ∧ d.get 25=BitVec.ofNat 32 (k-i)+0xffffffff#32 ∧ d.get 11=BitVec.ofNat 32 k ∧
      (lineTerm g k cap=0 → d.get 26=BitVec.ofNat 32 k) ∧ (lineTerm g k cap≠1 → d.get 1=400#32) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠21 → r≠13 → r≠25 → r≠14 → r≠30 → r≠15 → r≠26 → r≠1 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,count,inverse,cursor,last,status,frame,csr⟩ := contract B c ram sp buf i cap length hp h2 h24 h16 h17 hcap hraw hbuf hi hn hlen hm stack ha
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,count,inverse,cursor,last,status,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsLine
namespace E5R.Thermostat.HeadFieldsMore
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (length : Nat) (values : Reg → Word)
    (hp : c.pc=0x800033ea#32) (h2 : c.get 2=sp)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hmax : ramRead ram (sp+36#32) .w=1024#32)
    (hdst : ramRead ram (sp+52#32) .w=sp+4904#32)
    (hlen : length≤2048) (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (stored : HeadSaved.At ram sp values) (masked : c.mie_=false) :
    ∃ n d, 23≤n ∧ n≤25 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,memory ram sp length⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (memory ram sp length) (sp+4904#32) (out length) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,stack,abi,result,csr⟩ := contract B c ram sp length values hp h2 hraw hmax hdst hlen hm ha stored
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,stack,abi,result,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsMore
namespace E5R.Thermostat.HeadName
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start finish length : Nat)
    (hp : c.pc=0x80002fbc#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h21 : c.get 21=BitVec.ofNat 32 (finish-start)) (h22 : c.get 22=0#32-BitVec.ofNat 32 length)
    (h25 : c.get 25=BitVec.ofNat 32 (finish-start)+0xffffffff#32) (hc : HeadNameClass.Constants c)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hnext : ramRead ram (sp+16#32) .w=buf+1#32) (hbefore : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) (masked : c.mie_=false) :
    let g := bytes ram buf
    let k := scan isTchar g start finish
    ∃ n d after, 12<n ∧ n≤17+25*(finish-start) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      d.pc=(if HeadNameChecked.good g start k finish then 0x80003068#32 else 0x8000342c#32) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (HeadNameChecked.good g start k finish → ramRead after (sp+4#32) .w=BitVec.ofNat 32 k ∧ HeadNameState.At d sp buf start k finish length) ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → r≠30 → r≠19 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,pc,effect,good,frame,csr⟩ := contract B c ram sp buf start finish length hp h2 h24 h21 h22 h25 hc hraw hbuf hnext hbefore hmask h26 mem stack ha hi hn hlen
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,pc,effect,good,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadName
namespace E5R.Thermostat.HeadFieldsReject
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (values : Reg → Word) (status : Nat)
    (hp : c.pc=0x8000342c#32) (h2 : c.get 2=sp) (hdst : ramRead ram (sp+52#32) .w=sp+4904#32)
    (h1 : c.get 1=BitVec.ofNat 32 status) (hs : status<65536)
    (hm : Memory.Block B sp 5312) (ha : sp.toNat%4=0) (saved : HeadSaved.At ram sp values) (masked : c.mie_=false) :
    ∃ d, Trace.Closed B img 21 ⟨c,ram⟩ ⟨d,HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)⟩ ∧
      d.pc=values 1 &&& ~~~1 ∧ d.get 2=sp+384#32 ∧ HeadSaved.CoreAt d values ∧
      HeadResultView.At (HeadResultStore.memory ram (sp+4904#32) 4#32 (BitVec.ofNat 32 status)) (sp+4904#32) (.reject status) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<21 → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨d,trace,pc,stack,abi,result,csr⟩ := contract B c ram sp values status hp h2 hdst h1 hs hm ha saved
  exact ⟨d,Interrupt.close trace.det masked,pc,stack,abi,result,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadFieldsReject
