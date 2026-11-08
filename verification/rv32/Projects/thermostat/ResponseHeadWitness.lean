import Projects.thermostat.ResponseHead
import Projects.thermostat.UartWriteWitness
import Projects.thermostat.ResponseLiterals
namespace E5R.Thermostat.ResponseHeadWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board
abbrev ram := UartWriteWitness.ram

def ct (mime : Bool) := if mime then WireSpec.ascii "application/json" else []
def ptr (mime : Bool) : Word := if mime then 0x800056a8#32 else 1#32

def core (status body : Nat) (close mime : Bool) : Core :=
  ⟨0x80003e4e#32,(fun r => if r=2 then 0x80040060#32
  else if r=10 then 0x80020000#32 else if r=11 then 192#32 else if r=12 then BitVec.ofNat 32 status
  else if r=13 then ptr mime else if r=14 then BitVec.ofNat 32 (ct mime).length
  else if r=15 then BitVec.ofNat 32 body else if r=16 then ResponseHeadBodyMath.boolWord close
  else UartWriteWitness.core.get r),false,false,3,0,0,0,0,0,false⟩

/-- Nonzero incoming saved registers and checked disjoint arenas give concrete
    satisfiable complete header transactions for every bounded status/body. -/
theorem execution (status body : Nat) (close mime : Bool) (hlo : 100≤status) (hhi : status≤599) (hb : body≤832) :
    ∃ d n after, n≤2247 ∧ Quiet.Steps B img n ⟨core status body close mime,ram⟩ ⟨d,after⟩ ∧
      FormatCursor.Returned (core status body close mime) d ∧ d.pc=0x80000abc#32 ∧ d.get 10=1#32 ∧
      d.get 11=BitVec.ofNat 32 (ResponseHeadSpec.bytes status (ct mime) body close).length ∧
      Bytes.Span B after 0x80020000#32 (ResponseHeadSpec.bytes status (ct mime) body close) := by
  have hs : ReadBytes.Span B img ram (ptr mime) (ct mime) := by
    cases mime
    · exact ResponseHeadSources.empty ram _
    · exact ResponseLiterals.json ram
  have sepStack : WordRegions.Disjoint (ptr mime) (ct mime).length 0x80040000#32 96 := by
    cases mime
    · exact WordRegions.shrink (ResponseHeadSources.disjoint_empty _ _) (by change 0≤0;decide) (by decide)
    · exact WordRegions.before _ _ _ _ (by decide) (by decide)
  have sepOut : WordRegions.Disjoint (ptr mime) (ct mime).length 0x80020000#32 192 := by
    cases mime
    · exact ResponseHeadSources.disjoint_empty _ _
    · exact WordRegions.before _ _ _ _ (by decide) (by decide)
  obtain ⟨d,n,after,hn,td,hr,d10,d11,hbytes,_⟩ := ResponseHead.contract (core status body close mime) ram
    0x80040000#32 0x80020000#32 (ptr mime) status body (ct mime) close hlo hhi hb
    (by cases mime <;> decide +kernel) (by cases mime <;> decide +kernel)
    (by change Memory.Block B 0x80040000#32 96;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel) (by decide)
    (by change Memory.Block B 0x80020000#32 192;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel)
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    hs sepStack sepOut rfl rfl rfl rfl rfl rfl rfl rfl rfl
  refine ⟨d,n,after,hn,td,hr,?_,d10,d11,hbytes⟩
  rw [hr.pc]
  change (0x80000abc#32 &&& ~~~1)=0x80000abc#32
  decide +kernel

theorem json_maximum : ∃ d n after, n≤2247 ∧ Quiet.Steps B img n ⟨core 200 832 true true,ram⟩ ⟨d,after⟩ ∧
    FormatCursor.Returned (core 200 832 true true) d ∧ Bytes.Span B after 0x80020000#32
      (WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n") := by
  obtain ⟨d,n,after,hn,td,hr,_,_,_,hbytes⟩ := execution 200 832 true true (by decide) (by decide) (by decide)
  exact ⟨d,n,after,hn,td,hr,by simpa only [show ResponseHeadSpec.bytes 200 (ct true) 832 true=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n" by decide +kernel] using hbytes⟩

theorem no_content : ∃ d n after, n≤2247 ∧ Quiet.Steps B img n ⟨core 204 77 false false,ram⟩ ⟨d,after⟩ ∧
    FormatCursor.Returned (core 204 77 false false) d ∧ Bytes.Span B after 0x80020000#32 (WireSpec.ascii "HTTP/1.1 204 No Content\r\n\r\n") := by
  obtain ⟨d,n,after,hn,td,hr,_,_,_,hbytes⟩ := execution 204 77 false false (by decide) (by decide) (by decide)
  exact ⟨d,n,after,hn,td,hr,by simpa only [show ResponseHeadSpec.bytes 204 (ct false) 77 false=WireSpec.ascii "HTTP/1.1 204 No Content\r\n\r\n" by decide +kernel] using hbytes⟩

theorem not_modified : ∃ d n after, n≤2247 ∧ Quiet.Steps B img n ⟨core 304 77 false false,ram⟩ ⟨d,after⟩ ∧
    FormatCursor.Returned (core 304 77 false false) d ∧ Bytes.Span B after 0x80020000#32 (WireSpec.ascii "HTTP/1.1 304 \r\n\r\n") := by
  obtain ⟨d,n,after,hn,td,hr,_,_,_,hbytes⟩ := execution 304 77 false false (by decide) (by decide) (by decide)
  exact ⟨d,n,after,hn,td,hr,by simpa only [show ResponseHeadSpec.bytes 304 (ct false) 77 false=WireSpec.ascii "HTTP/1.1 304 \r\n\r\n" by decide +kernel] using hbytes⟩
end E5R.Thermostat.ResponseHeadWitness
