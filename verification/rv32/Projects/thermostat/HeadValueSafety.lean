import Projects.thermostat.HeadValueScan
import Projects.thermostat.HeadOwsForwardScan
import Projects.thermostat.HeadOwsBackScan
import Projects.thermostat.HeadHeaderLine
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadValueScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x8000307c#32) (state : HeadValueState.At c buf pos finish length)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (masked : c.mie_=false) :
    let g := bytes ram buf
    ∃ n d, 0<n ∧ n≤13*(finish-pos) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      d.pc=(if allIn isFieldByte g pos finish then 0x800030a4#32 else 0x8000342c#32) ∧
      (allIn isFieldByte g pos finish=true → HeadValueState.At d buf finish finish length) ∧
      (∀ r : Reg, r≠30 → r≠12 → r≠13 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,state,frame,csr⟩ := contract B c ram buf pos finish length hp state hi hn hlen mem
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,state,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadValueScan
namespace E5R.Thermostat.HeadOwsForwardScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length : Nat)
    (hp : c.pc=0x800030a4#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 pos) (h25 : c.get 25=BitVec.ofNat 32 (finish-pos))
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : pos<finish) (hn : finish≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    let k := scan isOws g pos finish
    ∃ n d, 0<n ∧ n≤12*(finish-pos) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=endpoint k finish ∧
      d.get 15=BitVec.ofNat 32 k ∧ d.get 25=BitVec.ofNat 32 (finish-k) ∧
      (∀ r : Reg, r≠10 → r≠12 → r≠25 → r≠15 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,index,remaining,frame,csr⟩ := contract B c ram sp buf pos finish length hp h2 h15 h25 hraw hbuf hi hn hlen mem stack ha
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,index,remaining,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadOwsForwardScan
namespace E5R.Thermostat.HeadOwsBackScan
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (start pos length : Nat)
    (hp : c.pc=0x800030d0#32) (h2 : c.get 2=sp) (h15 : c.get 15=BitVec.ofNat 32 start) (h25 : c.get 25=BitVec.ofNat 32 pos)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=buf)
    (hi : start<pos) (hn : pos≤length) (hlen : length≤2048) (mem : Memory.Block B buf length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (masked : c.mie_=false) :
    let g := bytes ram buf
    ∃ n d, 0<n ∧ n≤14*(pos-start) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x800030fa#32 ∧
      d.get 25=BitVec.ofNat 32 (trimEnd g start pos) ∧
      (∀ r : Reg, r≠10 → r≠13 → r≠12 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,hlo,hi,trace,pc,result,frame,csr⟩ := contract B c ram sp buf start pos length hp h2 h15 h25 hraw hbuf hi hn hlen mem stack ha
  exact ⟨n,d,hlo,hi,Interrupt.close trace.det masked,pc,result,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadOwsBackScan
namespace E5R.Thermostat.HeadHeaderLine
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp : Word) (start finish length : Nat)
    (hp : c.pc=0x80002fbc#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp) (h24 : c.get 24=BitVec.ofNat 32 start)
    (h21 : c.get 21=BitVec.ofNat 32 (finish-start)) (h22 : c.get 22=0#32-BitVec.ofNat 32 length)
    (h25 : c.get 25=BitVec.ofNat 32 (finish-start)+0xffffffff#32) (hc : HeadNameClass.Constants c)
    (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length) (hbuf : ramRead ram (sp+44#32) .w=(sp+516#32))
    (hnext : ramRead ram (sp+16#32) .w=(sp+516#32)+1#32) (hbefore : ramRead ram (sp+12#32) .w=BitVec.ofNat 32 length+0xffffffff#32)
    (hmask : ramRead ram (sp+32#32) .w=9409#32) (h26 : c.get 26=BitVec.ofNat 32 finish)
    (mem : Memory.Block B (sp+516#32) length) (stack : Memory.Block B sp 56) (ha : sp.toNat%4=0) (hi : start<finish) (hn : finish≤length) (hlen : length≤2048) (masked : c.mie_=false) :
    let g := bytes ram (sp+516#32)
    let k := scan isTchar g start finish
    ∃ n d after, 12<n ∧ n≤26+64*(finish-start) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadHeaderLineView.At d after sp (sp+516#32) start finish (headerLine g start finish) ∧
      (after=ram ∨ after=ramWrite ram (sp+4#32) (BitVec.ofNat 32 k) .w) ∧
      (∀ r : Reg, r≠10 → r≠14 → r≠15 → r≠13 → r≠20 → r≠12 → r≠31 → r≠30 → r≠19 → r≠25 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,hlo,hi,trace,result,effect,frame,csr⟩ := contract B c ram sp start finish length hp h1 h2 h24 h21 h22 h25 hc hraw hbuf hnext hbefore hmask h26 mem stack ha hi hn hlen
  exact ⟨n,d,after,hlo,hi,Interrupt.close trace.det masked,result,effect,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadHeaderLine
