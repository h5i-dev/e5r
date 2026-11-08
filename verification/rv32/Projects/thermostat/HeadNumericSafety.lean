import Projects.thermostat.HeadClNumberLoop
import Projects.thermostat.HeadClNumber
import Projects.thermostat.HeadClValue
import Projects.thermostat.HeadTeValue
import Projects.thermostat.QuietPrefix
namespace E5R.Thermostat.HeadClNumberLoop
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length acc : Nat)
    (hp : c.pc=0x80003206#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (h11 : c.get 11=BitVec.ofNat 32 (finish-pos))
    (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32) (h16 : c.get 16=10#32)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (inside : pos<finish) (upper : finish≤length)
    (bound : length≤2048) (accepted : acc≤1024) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 56) (aligned : sp.toNat%4=0) (masked : c.mie_=false) :
    ∃ n d, 0<n ∧ n≤30*(finish-pos) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧
      Post d (clLoop (bytes ram buf) finish 1024 acc pos) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,lo,hi,trace,result,frame,csr⟩ := contract B c ram sp buf pos finish length acc hp h1 h2 h10 h31 h11 h14 h13 h16 hlimit inside upper bound accepted memory stack aligned
  exact ⟨n,d,lo,hi,Interrupt.close trace.det masked,result,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadClNumberLoop
namespace E5R.Thermostat.HeadClNumber
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (pos finish length acc : Nat) (f : Fields)
    (hp : c.pc=0x80003206#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h10 : c.get 10=buf+BitVec.ofNat 32 pos) (h31 : c.get 31=BitVec.ofNat 32 (length-pos))
    (h11 : c.get 11=BitVec.ofNat 32 (finish-pos))
    (h14 : c.get 14=BitVec.ofNat 32 acc) (h13 : c.get 13=0#32) (h16 : c.get 16=10#32)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (inside : pos<finish) (upper : finish≤length)
    (bound : length≤2048) (accepted : acc≤1024) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (fields : HeadFieldsView.At ram sp f) (masked : c.mie_=false) :
    let result := clLoop (bytes ram buf) finish 1024 acc pos
    ∃ n d after, 0<n ∧ n≤5+30*(finish-pos) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      Post ram after sp d result ∧ HeadFieldsView.At after sp (updated f result) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,view,frame,csr⟩ := contract B c ram sp buf pos finish length acc f hp h1 h2 h10 h31 h11 h14 h13 h16 hlimit inside upper bound accepted memory stack aligned fields
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,view,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadClNumber
namespace E5R.Thermostat.HeadClValue
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word) (vs ve le length : Nat) (f : Fields)
    (hp : c.pc=0x800031dc#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h23 : c.get 23=(if f.te then 1#32 else 0#32)) (h15 : c.get 15=BitVec.ofNat 32 vs)
    (h26 : c.get 26=BitVec.ofNat 32 le) (h11 : c.get 11=BitVec.ofNat 32 le) (h16 : c.get 16=10#32)
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (hlimit : ramRead ram (sp+8#32) .w=1024#32) (fields : HeadFieldsView.At ram sp f)
    (ordered : vs≤ve ∧ ve≤le ∧ le≤length) (bound : length≤2048) (memory : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (masked : c.mie_=false) :
    let result := outcome (bytes ram buf) f vs ve le
    ∃ n d after, 7≤n ∧ n≤20+30*(ve-vs) ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      HeadClNumber.Post ram after sp d result ∧ HeadFieldsView.At after sp (HeadClNumber.updated f result) ∧
      (∀ r : Reg, r≠1 → r≠30 → r≠12 → r≠29 → r≠14 → r≠13 → r≠11 → r≠10 → r≠31 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,view,frame,csr⟩ := contract B c ram sp buf vs ve le length f hp h1 h2 h23 h15 h26 h11 h16 scratch hbuf hraw hlimit fields ordered bound memory stack aligned
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,view,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadClValue
namespace E5R.Thermostat.HeadTeValue
open E5R E5R.Thermostat HttpRequestSpec HeadLineScanSpec
theorem safe_contract (B : Board) (c : Core) (ram : Word → BitVec 8) (sp buf : Word)
    (f : Fields) (ns vs ve le length minor : Nat)
    (hp : c.pc=0x800032ae#32) (h1 : c.get 1=400#32) (h2 : c.get 2=sp)
    (h18 : c.get 18=BitVec.ofNat 32 (1-minor)) (h23 : c.get 23=(if f.te then 1#32 else 0#32))
    (h24 : c.get 24=BitVec.ofNat 32 ns) (h15 : c.get 15=BitVec.ofNat 32 vs)
    (h26 : c.get 26=BitVec.ofNat 32 le) (h21 : c.get 21=BitVec.ofNat 32 (le-ns))
    (scratch : ramRead ram (sp+0#32) .w=BitVec.ofNat 32 le-BitVec.ofNat 32 ve)
    (hbuf : ramRead ram (sp+44#32) .w=buf) (hraw : ramRead ram (sp+48#32) .w=BitVec.ofNat 32 length)
    (fields : HeadFieldsView.At ram sp f) (ordered : ns≤vs ∧ vs≤ve ∧ ve≤le ∧ le≤length)
    (bound : length≤2048) (version : minor≤1) (mem : Memory.Block B buf length)
    (stack : Memory.Block B sp 5312) (aligned : sp.toNat%4=0) (masked : c.mie_=false) :
    let result := outcome (bytes ram buf) f vs ve le minor
    ∃ n d after, 2≤n ∧ n≤81 ∧ Trace.Closed B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ Post ram after sp d result ∧
      HeadFieldsView.At after sp (if result=none then {f with te := true} else f) ∧
      (∀ r : Reg, r≠1 → r≠10 → r≠11 → r≠12 → r≠13 → r≠14 → d.get r=c.get r) ∧ d.sameCsr c ∧
      (∀ count e reads evs, count<n → Observed.Steps B img count ⟨c,ram⟩ e reads evs →
        reads=[] ∧ evs=[] ∧ ¬Escapes B img e) := by
  obtain ⟨n,d,after,lo,hi,trace,result,view,frame,csr⟩ := contract B c ram sp buf f ns vs ve le length minor hp h1 h2 h18 h23 h24 h15 h26 h21 scratch hbuf hraw fields ordered bound version mem stack aligned
  exact ⟨n,d,after,lo,hi,Interrupt.close trace.det masked,result,view,frame,csr,fun _ _ _ _ hk actual => QuietPrefix.safe trace masked hk actual⟩
end E5R.Thermostat.HeadTeValue
