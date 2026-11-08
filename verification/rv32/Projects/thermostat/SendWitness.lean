import Projects.thermostat.Send
import Projects.thermostat.UartWriteWitness
import Projects.thermostat.ResponseLiterals
set_option maxRecDepth 5000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.SendWitness
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

def raw (clip : Bool) : Nat := if clip then 1024 else 2
def payload (clip : Bool) := List.replicate (if clip then 832 else 2) 65#8

def objectByte (status : Nat) (close head clip : Bool) (off : Nat) : BitVec 8 :=
  if 8≤off ∧ off<12 then byteOf 0x80020000#32 (off-8)
  else if 12≤off ∧ off<16 then byteOf 1024#32 (off-12)
  else if 24≤off ∧ off<28 then byteOf 0x80032000#32 (off-24)
  else if 28≤off ∧ off<32 then byteOf 0x800056a8#32 (off-28)
  else if 32≤off ∧ off<36 then byteOf 16#32 (off-32)
  else if 36≤off ∧ off<40 then byteOf (BitVec.ofNat 32 (raw clip)) (off-36)
  else if 40≤off ∧ off<42 then byteOf (BitVec.ofNat 32 status) (off-40)
  else if off=42 then if close then 1#8 else 0#8
  else if off=46 then if head then 1#8 else 0#8
  else 0#8

def ram (status : Nat) (close head clip : Bool) (a : Word) : BitVec 8 :=
  if 0x80030000≤a.toNat ∧ a.toNat<0x80030059 then objectByte status close head clip (a.toNat-0x80030000) else 65#8

def core : Core := ⟨0x8000030e#32,(fun r => if r=2 then 0x80040090#32
  else if r=10 then 0x80031000#32 else if r=11 then 0x80030000#32 else UartWriteWitness.core.get r),false,false,3,0,0,0,0,0,false⟩

theorem payload_span (status : Nat) (close head clip : Bool) :
    ReadBytes.Span B img (ram status close head clip) 0x800200c0#32 (payload clip) := by
  apply ReadBytes.of_ram
  apply Bytes.of_block
  · cases clip <;> unfold Memory.Block B UartPlatform.board <;> rw [ThermostatImage.image_rwBase] <;> decide +kernel
  · cases clip <;> decide +kernel
  · intro i
    have hi : i.val<832 := by have hh := i.isLt;cases clip <;> simp [payload] at hh <;> omega
    have ha : (0x800200c0#32+BitVec.ofNat 32 i.val).toNat=0x800200c0+i.val := by
      simp only [BitVec.toNat_add,show (0x800200c0#32).toNat=2147614912 by decide +kernel,BitVec.toNat_ofNat]
      omega
    change ram status close head clip (0x800200c0#32+BitVec.ofNat 32 i.val)=(payload clip)[i.val]
    rw [show (payload clip)[i.val]=65#8 from List.getElem_replicate i.isLt]
    simp only [ram,ha]
    rw [if_neg (by omega)]

theorem ram_at (status : Nat) (close head clip : Bool) (off : Nat) (ho : off<89) :
    ram status close head clip (0x80030000#32+BitVec.ofNat 32 off)=objectByte status close head clip off := by
  have ht : (0x80030000#32+BitVec.ofNat 32 off).toNat=2147680256+off := by
    simp only [BitVec.toNat_add,show (0x80030000#32).toNat=2147680256 by decide +kernel,BitVec.toNat_ofNat]
    omega
  simp only [ram,ht]
  rw [if_pos (by omega),show 2147680256+off-2147680256=off by omega]

theorem word_at (status : Nat) (close head clip : Bool) (off : Nat) (ho : off+4≤89) :
    ramRead (ram status close head clip) (0x80030000#32+BitVec.ofNat 32 off) .w=BitVec.ofNat 32 ((objectByte status close head clip (off+0)).toNat+256*(objectByte status close head clip (off+1)).toNat+65536*(objectByte status close head clip (off+2)).toNat+16777216*(objectByte status close head clip (off+3)).toNat) := by
  unfold ramRead
  rw [show (0x80030000#32+BitVec.ofNat 32 off)+1=0x80030000#32+BitVec.ofNat 32 (off+1) by simp only [BitVec.ofNat_eq_ofNat];rw [BitVec.add_assoc,BitVec.ofNat_add]]
  rw [show (0x80030000#32+BitVec.ofNat 32 off)+2=0x80030000#32+BitVec.ofNat 32 (off+2) by simp only [BitVec.ofNat_eq_ofNat];rw [BitVec.add_assoc,BitVec.ofNat_add]]
  rw [show (0x80030000#32+BitVec.ofNat 32 off)+3=0x80030000#32+BitVec.ofNat 32 (off+3) by simp only [BitVec.ofNat_eq_ofNat];rw [BitVec.add_assoc,BitVec.ofNat_add]]
  rw [ram_at status close head clip off (by omega),ram_at status close head clip (off+1) (by omega),ram_at status close head clip (off+2) (by omega),ram_at status close head clip (off+3) (by omega)]
  rfl

theorem half_at (status : Nat) (close head clip : Bool) (off : Nat) (ho : off+2≤89) :
    ramRead (ram status close head clip) (0x80030000#32+BitVec.ofNat 32 off) .h=BitVec.ofNat 32 ((objectByte status close head clip (off+0)).toNat+256*(objectByte status close head clip (off+1)).toNat) := by
  unfold ramRead
  rw [show (0x80030000#32+BitVec.ofNat 32 off)+1=0x80030000#32+BitVec.ofNat 32 (off+1) by simp only [BitVec.ofNat_eq_ofNat];rw [BitVec.add_assoc,BitVec.ofNat_add]]
  rw [ram_at status close head clip off (by omega),ram_at status close head clip (off+1) (by omega)]
  rfl

theorem meta_fresh (status : Nat) (close head clip : Bool) :
    ram status close head clip (0x80030000#32+45#32)=0#8 := by rw [ram_at status close head clip 45 (by decide)];rfl

theorem meta_capacity (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+12#32) .w=1024#32 := by rw [word_at status close head clip 12 (by decide)];rfl

theorem meta_ioWord (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+24#32) .w=0x80032000#32 := by
  rw [word_at status close head clip 24 (by decide)]
  change BitVec.ofNat 32 ((byteOf 0x80032000#32 0).toNat+256*(byteOf 0x80032000#32 1).toNat+65536*(byteOf 0x80032000#32 2).toNat+16777216*(byteOf 0x80032000#32 3).toNat)=0x80032000#32
  decide +kernel

theorem meta_txWord (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+8#32) .w=0x80020000#32 := by
  rw [word_at status close head clip 8 (by decide)]
  change BitVec.ofNat 32 ((byteOf 0x80020000#32 0).toNat+256*(byteOf 0x80020000#32 1).toNat+65536*(byteOf 0x80020000#32 2).toNat+16777216*(byteOf 0x80020000#32 3).toNat)=0x80020000#32
  decide +kernel

theorem meta_ctWord (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+28#32) .w=0x800056a8#32 := by
  rw [word_at status close head clip 28 (by decide)]
  change BitVec.ofNat 32 ((byteOf 0x800056a8#32 0).toNat+256*(byteOf 0x800056a8#32 1).toNat+65536*(byteOf 0x800056a8#32 2).toNat+16777216*(byteOf 0x800056a8#32 3).toNat)=0x800056a8#32
  decide +kernel

theorem meta_ctLength (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+32#32) .w=16#32 := by rw [word_at status close head clip 32 (by decide)];rfl

theorem meta_bodyLength (status : Nat) (close head clip : Bool) :
    ramRead (ram status close head clip) (0x80030000#32+36#32) .w=BitVec.ofNat 32 (raw clip) := by rw [word_at status close head clip 36 (by decide)];cases clip <;> rfl

theorem meta_statusWord (status : Nat) (close head clip : Bool) (hs : status=200 ∨ status=204 ∨ status=304) :
    extend .h false (ramRead (ram status close head clip) (0x80030000#32+40#32) .h)=BitVec.ofNat 32 status := by rw [half_at status close head clip 40 (by decide)];rcases hs with rfl|rfl|rfl <;> simp [objectByte] <;> decide +kernel

theorem meta_closeWord (status : Nat) (close head clip : Bool) :
    extend .b false (ramRead (ram status close head clip) (0x80030000#32+42#32) .b)=ResponseHeadBodyMath.boolWord close := by rw [Memory.load_byte,ram_at status close head clip 42 (by decide)];cases close <;> rfl

theorem meta_headWord (status : Nat) (close head clip : Bool) :
    extend .b false (ramRead (ram status close head clip) (0x80030000#32+46#32) .b)=ResponseHeadBodyMath.boolWord head := by rw [Memory.load_byte,ram_at status close head clip 46 (by decide)];cases head <;> rfl

theorem pre (status : Nat) (close head clip : Bool) (hs : status=200 ∨ status=204 ∨ status=304) :
    SendInput.Pre core (ram status close head clip) 0x80040000#32 0x80030000#32 0x80031000#32
      0x80020000#32 0x80032000#32 0x800056a8#32 (raw clip) status (WireSpec.ascii "application/json") (payload clip) close head := by
  exact {
    pc := rfl
    sp := rfl
    resultArg := rfl
    objectArg := rfl
    stack := by change Memory.Block B 0x80040000#32 144;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    object := by change Memory.Block B 0x80030000#32 89;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    result := by change Memory.Block B 0x80031000#32 8;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    txBlock := by change Memory.Block B 0x80020000#32 1024;unfold Memory.Block B UartPlatform.board;rw [ThermostatImage.image_rwBase];decide +kernel
    stackAligned := by decide +kernel
    objectAligned := by decide +kernel
    resultAligned := by decide +kernel
    txStrict := by decide +kernel
    objectStack := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    txStack := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    ctStack := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    ctObject := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    ctTx := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    objectTx := WordRegions.symm (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    resultObject := WordRegions.symm (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    resultTx := WordRegions.symm (WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel))
    resultStack := WordRegions.before _ _ _ _ (by decide +kernel) (by decide +kernel)
    source := ResponseLiterals.json _
    payloadBytes := payload_span status close head clip
    rawBound := by cases clip <;> decide +kernel
    statusLo := by rcases hs with rfl|rfl|rfl <;> decide +kernel
    statusHi := by rcases hs with rfl|rfl|rfl <;> decide +kernel
    ctBound := by decide +kernel
    field := by decide +kernel
    clipped := by cases clip <;> simp [payload,raw]
    fresh := meta_fresh status close head clip
    capacity := meta_capacity status close head clip
    ioWord := meta_ioWord status close head clip
    txWord := meta_txWord status close head clip
    ctWord := meta_ctWord status close head clip
    ctLength := meta_ctLength status close head clip
    bodyLength := meta_bodyLength status close head clip
    statusWord := meta_statusWord status close head clip hs
    closeWord := meta_closeWord status close head clip
    headWord := meta_headWord status close head clip
  }

def headerSlots (status : Nat) (close clip : Bool) :=
  List.replicate (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") (payload clip).length close).length UartWriteWitness.slot1

def bodySlots (status : Nat) (head clip : Bool) :=
  List.replicate (ResponseHeadSpec.body status head (payload clip)).length UartWriteWitness.slot1

/-- Every byte in these concrete complete calls waits through one not-ready
    poll before readiness. The 1024 requested-byte case clips to832 source bytes. -/
theorem execution (status : Nat) (close head clip : Bool) (hstatus : status=200 ∨ status=204 ∨ status=304) :
    ∃ d n after reads events,
      n≤2400+UartWriteAll.time (ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") (payload clip).length close) (headerSlots status close clip)+
        UartWriteAll.time (ResponseHeadSpec.body status head (payload clip)) (bodySlots status head clip) ∧
      Observed.Steps B img n ⟨core,ram status close head clip⟩ ⟨d,after⟩ reads events ∧ FormatCursor.Returned core d ∧
      d.pc=0x80000abc#32 ∧ Observed.input reads=[] ∧
      Observed.output events=ResponseHeadSpec.bytes status (WireSpec.ascii "application/json") (payload clip).length close++ResponseHeadSpec.body status head (payload clip) ∧
      ramRead after (0x80031000#32+4#32) .w=ResponseHeadBodyMath.boolWord close ∧ after (0x80030000#32+45#32)=1#8 := by
  obtain ⟨d,n,after,hn,td,hr,_,hclose,hdone,_,_⟩ := Send.contract core (ram status close head clip)
    0x80040000#32 0x80030000#32 0x80031000#32 0x80020000#32 0x80032000#32 0x800056a8#32
    (raw clip) status (WireSpec.ascii "application/json") (payload clip) close head (pre status close head clip hstatus)
    (headerSlots status close clip) (bodySlots status head clip)
    (by exact List.length_replicate) (by exact List.length_replicate)
  have projection := Send.projection status (WireSpec.ascii "application/json") (payload clip) close head (headerSlots status close clip) (bodySlots status head clip)
  refine ⟨d,n,after,_,_,hn,td,hr,?_,projection.1,projection.2,hclose,hdone⟩
  rw [hr.pc]
  change (0x80000abc#32 &&& ~~~1)=0x80000abc#32
  decide +kernel

theorem clipped_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram 200 true false true⟩ ⟨d,after⟩ reads events ∧ FormatCursor.Returned core d ∧
    Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n"++List.replicate 832 65#8 := by
  obtain ⟨d,n,after,reads,events,_,td,hr,_,_,ho,_,_⟩ := execution 200 true false true (by decide)
  refine ⟨d,n,after,reads,events,td,hr,?_⟩
  rw [show ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (payload true).length true=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n" by decide +kernel] at ho
  exact ho

theorem head_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram 200 true true true⟩ ⟨d,after⟩ reads events ∧ FormatCursor.Returned core d ∧
    Observed.output events=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n" := by
  obtain ⟨d,n,after,reads,events,_,td,hr,_,_,ho,_,_⟩ := execution 200 true true true (by decide)
  refine ⟨d,n,after,reads,events,td,hr,?_⟩
  rw [ResponseHeadSpec.head_empty,List.append_nil] at ho
  rw [show ResponseHeadSpec.bytes 200 (WireSpec.ascii "application/json") (payload true).length true=WireSpec.ascii "HTTP/1.1 200 OK\r\nContent-Type: application/json\r\nContent-Length: 832\r\nConnection: close\r\n\r\n" by decide +kernel] at ho
  exact ho

theorem no_content_packet : ∃ d n after reads events,
    Observed.Steps B img n ⟨core,ram 204 false false false⟩ ⟨d,after⟩ reads events ∧ FormatCursor.Returned core d ∧
    Observed.output events=WireSpec.ascii "HTTP/1.1 204 No Content\r\nContent-Type: application/json\r\n\r\n" := by
  obtain ⟨d,n,after,reads,events,_,td,hr,_,_,ho,_,_⟩ := execution 204 false false false (by decide)
  refine ⟨d,n,after,reads,events,td,hr,?_⟩
  rw [show ResponseHeadSpec.body 204 false (payload false)=[] by decide +kernel,List.append_nil] at ho
  rw [show ResponseHeadSpec.bytes 204 (WireSpec.ascii "application/json") (payload false).length false=WireSpec.ascii "HTTP/1.1 204 No Content\r\nContent-Type: application/json\r\n\r\n" by decide +kernel] at ho
  exact ho
end E5R.Thermostat.SendWitness
