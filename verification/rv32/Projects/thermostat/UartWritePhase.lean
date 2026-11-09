import Projects.thermostat.UartTxPhase
import Projects.thermostat.ReactiveEnvelope
import Projects.thermostat.UartWriteAll
set_option autoImplicit false
namespace E5R.Thermostat.UartWritePhase
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- Actual fresh write_all arguments and borrowed source, supplied by the
    real Send caller. Readiness and eventual completion are absent. -/
structure Input (c : Core) (ram : Word → BitVec 8) (obj io src : Word) (bs : List (BitVec 8)) : Prop where
  pc : c.pc=0x80000786#32
  objectArg : c.get 10=obj
  object : Memory.Block B obj 41
  aligned : obj.toNat%4=0
  fresh : ram (obj+40#32)=0#8
  ioWord : ramRead ram obj .w=io
  sourceWord : ramRead ram (obj+4#32) .w=src
  lengthWord : ramRead ram (obj+8#32) .w=BitVec.ofNat 32 bs.length
  source : ReadBytes.Span B img ram src bs
  nowrap : src.toNat+bs.length<2^32
  apart : WordRegions.Disjoint src bs.length obj 41
  masked : c.mie_=false

def Active (original : Core) (before : Word → BitVec 8) (obj io src : Word) (bs suffix : List (BitVec 8))
    (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  bs≠[] ∧ ram=UartWritePrepare.memory before obj io src (BitVec.ofNat 32 bs.length) ∧
    UartTxPhase.At c ram g suffix ∧ UartWriteRegs.Frame original c ∧
    c.get 11=BitVec.ofNat 32 bs.length ∧ c.sameCsr original

def Returned (original : Core) (before : Word → BitVec 8) (obj io src : Word) (bs suffix : List (BitVec 8))
    (c : Core) (ram : Word → BitVec 8) (g : State) : Prop :=
  FormatCursor.Returned original c ∧ ram=UartWriteAll.memory before obj io src bs ∧
    ∃ p,g.phase=.reply p ∧ p.remaining=suffix

def Cut (original : Core) (before : Word → BitVec 8) (obj io src : Word) (bs suffix : List (BitVec 8))
    (m : Machine) (g : State) : Prop :=
  Active original before obj io src bs suffix m.core m.ram g ∨ Returned original before obj io src bs suffix m.core m.ram g

theorem finish {original before obj io src bs suffix c ram g}
    (h : Input original before obj io src bs) (nonempty : bs≠[])
    (memory : ram=UartWritePrepare.memory before obj io src (BitVec.ofNat 32 bs.length))
    (post : UartTxPhase.Returned c ram g suffix) (frame : UartWriteRegs.Frame original c)
    (length : c.get 11=BitVec.ofNat 32 bs.length) (csr : c.sameCsr original) :
    ReactiveEnvelope.Envelope (Cut original before obj io src bs suffix) ⟨c,ram⟩ g := by
  obtain ⟨finish,p,phase,queue,pc,context,pointer⟩ := post
  have objectArg := (frame 10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans h.objectArg
  have sourceWord : ramRead ram (obj+16#32) .w=src := by rw [memory];exact UartWritePrepare.source _ _ _ _ _
  have lengthWord : ramRead ram (obj+20#32) .w=BitVec.ofNat 32 bs.length := by rw [memory];exact UartWritePrepare.length _ _ _ _ _
  obtain ⟨d,quiet,ret,regs,lastCsr⟩ := UartWriteComplete.contract B c ram obj src (BitVec.ofNat 32 bs.length)
    pc objectArg length h.object h.aligned lengthWord sourceWord
  have finalFrame : UartWriteRegs.Frame original d := UartWriteRegs.trans frame
    (fun r a b e f k q w => regs r a b f)
  have retPc : d.pc=original.get 1 &&& ~~~1 := by
    rw [ret,frame 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
  have same : UartWriteComplete.memory ram obj src (BitVec.ofNat 32 bs.length)=UartWriteAll.memory before obj io src bs := by
    rw [memory]
    simp only [UartWriteAll.memory,nonempty,ite_false,UartWriteNonzero.memory]
  exact ⟨context.masked,14,⟨d,UartWriteComplete.memory ram obj src (BitVec.ofNat 32 bs.length)⟩,quiet,
    Or.inr ⟨UartWriteRegs.returned retPc (lastCsr.trans csr) finalFrame,same,p,phase,queue⟩⟩

theorem next {original before obj io src bs suffix c ram g}
    (h : Input original before obj io src bs) (live : Active original before obj io src bs suffix c ram g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img ⟨c,ram⟩ o=⟨.ok d ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧
      ReactiveEnvelope.Envelope (Cut original before obj io src bs suffix) ⟨d,ram⟩ next := by
  obtain ⟨nonempty,memory,txAt,frame,length,csr⟩ := live
  obtain ⟨d,reads,evs,next,step,trace,post,regs,lastCsr⟩ := UartTxPhase.next txAt o
  have finalFrame := UartWriteRegs.trans frame (fun r a b e f k q w => regs r b q w)
  have finalLength := (regs 11 (by decide) (by decide) (by decide)).trans length
  have finalCsr := lastCsr.trans csr
  refine ⟨d,reads,evs,next,step,trace,?_⟩
  rcases post with active|returned
  · exact ⟨UartTxPhase.masked active,0,⟨d,ram⟩,.refl _,Or.inl ⟨nonempty,memory,active,finalFrame,finalLength,finalCsr⟩⟩
  · exact finish h nonempty memory returned finalFrame finalLength finalCsr

theorem safe {original before obj io src bs suffix c ram g}
    (h : Active original before obj io src bs suffix c ram g) : ¬Escapes B img ⟨c,ram⟩ := UartTxPhase.safe h.2.2.1

/-- The actual fresh future enters a reactive byte loop or returns quietly
    for an empty slice. Queue suffixes survive header/body call boundaries. -/
theorem start {original before obj io src bs suffix} {g : State} {p : Pending}
    (h : Input original before obj io src bs) (phase : g.phase=.reply p) (queue : p.remaining=bs++suffix) :
    ReactiveEnvelope.Envelope (Cut original before obj io src bs suffix) ⟨original,before⟩ g := by
  cases bs with
  | nil =>
    obtain ⟨d,quiet,ret⟩ := UartWriteZero.contract B original before obj io src h.pc h.objectArg h.object h.aligned h.fresh h.ioWord h.sourceWord h.lengthWord
    exact ⟨h.masked,14,⟨d,UartWriteZero.memory before obj io src⟩,quiet,Or.inr ⟨ret,rfl,p,phase,by simpa only [List.nil_append] using queue⟩⟩
  | cons byte rest =>
    let len := BitVec.ofNat 32 (byte::rest).length
    have nonzero : len≠0#32 := by
      intro eq
      have value := congrArg BitVec.toNat eq
      change (byte::rest).length%2^32=0 at value
      rw [Nat.mod_eq_of_lt h.source.length] at value
      simp only [List.length_cons] at value
      omega
    obtain ⟨d,quiet,pc,r10,r11,r12,r13,r14,r15,regs,csr⟩ := UartWritePrepare.contract B original before obj io src len
      h.pc h.objectArg h.object h.aligned h.fresh h.ioWord h.sourceWord h.lengthWord nonzero
    let ram := UartWritePrepare.memory before obj io src len
    have source : ReadBytes.Span B img ram src (byte::rest) :=
      ⟨h.source.length,h.source.nowrap,fun i => (h.source.bytes i).frame (UartWritePrepare.frame before obj io src len _ (h.apart i))⟩
    have frame : UartWriteRegs.Frame original d := fun r a b e f k q w => regs r a b e f k
    have tx : UartTxReactive.Loading d ram src byte rest :=
      ⟨pc,⟨r14,r13,r15,source,h.nowrap,(congrArg Prod.fst csr).trans h.masked⟩,r12⟩
    exact ⟨h.masked,22,⟨d,ram⟩,quiet,Or.inl ⟨List.cons_ne_nil _ _,rfl,.loading phase queue tx,frame,r11,csr⟩⟩
end E5R.Thermostat.UartWritePhase
