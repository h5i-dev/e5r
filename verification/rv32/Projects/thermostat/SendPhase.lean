import Projects.thermostat.SendUartReactive
import Projects.thermostat.ReactiveEnvelopeComposition
import Projects.thermostat.SendTransfer
set_option autoImplicit false
namespace E5R.Thermostat.SendPhase
open E5R E5R.Thermostat ProtocolStreamSpec
abbrev B := UartPlatform.board

/-- A real fresh Send call. The caller separately supplies the pure queued
    bytes and later proves its concrete main-loop continuation. -/
structure Call where
  original : Core
  before : Word → BitVec 8
  frame : Word
  obj : Word
  res : Word
  tx : Word
  io : Word
  ctptr : Word
  raw : Nat
  status : Nat
  ct : List (BitVec 8)
  payload : List (BitVec 8)
  close : Bool
  headOnly : Bool
  input : SendInput.Pre original before frame obj res tx io ctptr raw status ct payload close headOnly
  masked : original.mie_=false

def header (a : Call) := ResponseHeadSpec.bytes a.status a.ct a.payload.length a.close

def body (a : Call) := ResponseHeadSpec.body a.status a.headOnly a.payload

def headPre (a : Call) (ram : Word → BitVec 8) := SendHeadUart.prepared ram a.obj a.io a.tx
  (BitVec.ofNat 32 (body a).length) (ResponseHeadBodyMath.boolWord a.close) (header a)

def headMemory (a : Call) (ram : Word → BitVec 8) := SendHeadUart.memory ram a.obj a.io a.tx
  (BitVec.ofNat 32 (body a).length) (ResponseHeadBodyMath.boolWord a.close) (header a)

def bodyPre (a : Call) (ram : Word → BitVec 8) := SendBodyUart.prepared ram a.obj a.io (a.tx+192#32) (body a)

def bodyMemory (a : Call) (ram : Word → BitVec 8) := SendBodyUart.memory ram a.obj a.io (a.tx+192#32) (body a)

structure Selected (a : Call) where
  headerCore : Core
  ram : Word → BitVec 8
  core : Core
  post : SendHeader.Post a.original headerCore a.before ram a.frame a.obj a.res a.tx a.io a.status a.ct a.payload a.close a.headOnly
  pc : core.pc=0x80000408#32
  bodyLength : core.get 10=BitVec.ofNat 32 (body a).length
  headerLength : core.get 11=BitVec.ofNat 32 (header a).length
  keep : ResponseHeadCallee.Keep headerCore core []
  csr : core.sameCsr headerCore

structure HeadDone (a : Call) (s : Selected a) (c : Core) (ram : Word → BitVec 8) : Prop where
  pc : c.pc=0x8000042e#32
  keep : ResponseHeadCallee.Keep s.core c []
  csr : c.sameCsr s.core
  lower : ViewFrame.Region (headPre a s.ram) ram a.obj 48
  outside : ∀ x,(∀ i : Fin 89,x≠a.obj+BitVec.ofNat 32 i.val) → ram x=s.ram x
  memory : ram=headMemory a s.ram

inductive Active (a : Call) (m : Machine) (g : State) : Prop where
  | head (s : Selected a) (anchor : Core) :
      SendUartReactive.Prepared s.core anchor s.ram (headPre a s.ram) a.obj a.io a.tx (header a) 0x8000042e#32 →
      UartWritePhase.Active anchor (headPre a s.ram) (a.obj+48#32) a.io a.tx (header a) (body a) m.core m.ram g → Active a m g
  | body (s : Selected a) (headCore : Core) (headRam : Word → BitVec 8) (anchor : Core) :
      HeadDone a s headCore headRam →
      SendUartReactive.Prepared headCore anchor headRam (bodyPre a headRam) a.obj a.io (a.tx+192#32) (body a) 0x8000044e#32 →
      UartWritePhase.Active anchor (bodyPre a headRam) (a.obj+48#32) a.io (a.tx+192#32) (body a) [] m.core m.ram g → Active a m g

/-- Full actual Send return, preserving the original caller and all RAM
    outside its declared stack/object/result/header regions. -/
def Returned (a : Call) (m : Machine) (g : State) : Prop :=
  FormatCursor.Returned a.original m.core ∧ ramRead m.ram (a.res+0#32) .w=0xffffffff#32 ∧
    ramRead m.ram (a.res+4#32) .w=ResponseHeadBodyMath.boolWord a.close ∧ m.ram (a.obj+45#32)=1#8 ∧
    Bytes.Span B m.ram a.tx (header a) ∧
    (∀ x,(∀ i : Fin 144,x≠a.frame+BitVec.ofNat 32 i.val) → (∀ i : Fin 89,x≠a.obj+BitVec.ofNat 32 i.val) →
      (∀ i : Fin 8,x≠a.res+BitVec.ofNat 32 i.val) → (∀ i : Fin 192,x≠a.tx+BitVec.ofNat 32 i.val) → m.ram x=a.before x) ∧
    ∃ p,g.phase=.reply p ∧ p.remaining=[]

def Cut (a : Call) (m : Machine) (g : State) := Active a m g ∨ Returned a m g

/-- The second actual UART return, then flush/result stores and Send RET.
    The logical queue is empty only after both actual byte loops. -/
theorem after_body {call : Call} (stage : Selected call) {headCore headRam anchor c ram g}
    (headDone : HeadDone call stage headCore headRam)
    (prepared : SendUartReactive.Prepared headCore anchor headRam (bodyPre call headRam) call.obj call.io
      (call.tx+192#32) (body call) 0x8000044e#32)
    (returned : UartWritePhase.Returned anchor (bodyPre call headRam) (call.obj+48#32) call.io
      (call.tx+192#32) (body call) [] c ram g) : ReactiveEnvelope.Envelope (Cut call) ⟨c,ram⟩ g := by
  let h := call.input
  let q := stage.post
  obtain ⟨pc,keep,csr,lower2,frame2,memory2,queue⟩ := SendUartReactive.finish prepared returned
  have objKeep : c.get 8=call.obj := (keep 8 (by decide) (by simp)).trans
    ((headDone.keep 8 (by decide) (by simp)).trans ((stage.keep 8 (by decide) (by simp)).trans q.x8))
  have resKeep : c.get 9=call.res := (keep 9 (by decide) (by simp)).trans
    ((headDone.keep 9 (by decide) (by simp)).trans ((stage.keep 9 (by decide) (by simp)).trans q.x9))
  have spKeep : c.get 2=call.frame+96#32 := (keep 2 (by decide) (by simp)).trans
    ((headDone.keep 2 (by decide) (by simp)).trans ((stage.keep 2 (by decide) (by simp)).trans q.x2))
  have headerLimit : (header call).length≤120 := by
    have bound := (ResponseHeadPlan.bounds call.status call.ct call.payload.length call.close
      (by have := h.statusLo;omega) h.statusHi h.ctBound (SendInput.payload_bound h)).1 ⟨11,by decide⟩
    rw [ResponseHeadPlan.all] at bound
    exact bound
  have headerObj : WordRegions.Disjoint call.tx (header call).length call.obj 89 :=
    WordRegions.shrink (WordRegions.symm h.objectTx) (by omega) (by decide)
  have savedObj := Subregion.left (WordRegions.symm h.objectStack) 108 36 (by decide)
  have savedRes := Subregion.left (WordRegions.symm h.resultStack) 108 36 (by decide)
  have prefix1 : ViewFrame.Region stage.ram (headPre call stage.ram) call.obj 20 := SendHeadUartCallData.prefixRegion _ _ _ _ _ _ _
  have io1 := (ViewFrame.word headDone.lower 16 (by decide)).trans ((ViewFrame.word prefix1 16 (by decide)).trans q.cachedIo)
  have flagP1 : extend .b false (ramRead (headPre call stage.ram) (call.obj+44#32) .b)=ResponseHeadBodyMath.boolWord call.close := by
    have word : headPre call stage.ram (call.obj+44#32)=byteOf (ResponseHeadBodyMath.boolWord call.close) 0 := SendHeadUartCallData.slot44 _ _ _ _ _ _ _
    rw [Memory.load_byte,word]
    cases call.close <;> rfl
  have flag1 := (congrArg (extend .b false) (ReadRegion.read headDone.lower 44 .b (by decide))).trans flagP1
  have prefix2 : ViewFrame.Region headRam (bodyPre call headRam) call.obj 48 := SendBodyUartCallData.prefixRegion _ _ _ _ _
  have io2 := (ViewFrame.word lower2 16 (by decide)).trans ((ViewFrame.word prefix2 16 (by decide)).trans io1)
  have flag2 := (congrArg (extend .b false) (ReadRegion.read lower2 44 .b (by decide))).trans
    ((congrArg (extend .b false) (ReadRegion.read prefix2 44 .b (by decide))).trans flag1)
  obtain ⟨e,finish,epc,e10,e22,e11,regs,csrE⟩ := SendFinish.contract B c ram call.obj call.res call.io (ResponseHeadBodyMath.boolWord call.close)
    objKeep resKeep h.object h.objectAligned h.result h.resultAligned io2 flag2 pc
  let final := SendFinish.memory ram call.obj call.res call.io (ResponseHeadBodyMath.boolWord call.close)
  have allFrame (x : Word) (ho : ∀ i : Fin 89,x≠call.obj+BitVec.ofNat 32 i.val) (hr : ∀ i : Fin 8,x≠call.res+BitVec.ofNat 32 i.val) : final x=stage.ram x :=
    (SendFinishData.frame ram call.obj call.res call.io (ResponseHeadBodyMath.boolWord call.close) x ho hr).trans
      ((frame2 x ho).trans (headDone.outside x ho))
  have saved : SendSaved.At final call.frame call.original := SendSaved.region q.saved (fun i => allFrame _ (savedObj i) (savedRes i))
  have e2 := (regs 2 (by decide) (by decide) (by decide)).trans spKeep
  obtain ⟨f,restore,fpc,f1,f8,f9,f18,f19,f20,f21,f22,f23,f2,restRegs,csrF⟩ := SendRestore.contract B e final call.frame e2 h.stack h.stackAligned epc
  have completeCsr : f.sameCsr call.original := csrF.trans (csrE.trans (csr.trans (headDone.csr.trans (stage.csr.trans q.csr))))
  have extra (rr : Reg) (member : rr∈[24,25,26,27]) : f.get rr=call.original.get rr := by
    have neq : ∀ rr : Reg,rr∈[24,25,26,27] → rr≠10 ∧ rr≠22 ∧ rr≠11 ∧ rr≠1 ∧ rr≠8 ∧ rr≠9 ∧ rr≠18 ∧ rr≠19 ∧ rr≠20 ∧ rr≠21 ∧ rr≠23 ∧ rr≠2 ∧ ResponseHeadCallee.Registers rr := by decide +kernel
    obtain ⟨n10,n22,n11,n1,n8,n9,n18,n19,n20,n21,n23,n2,callee⟩ := neq rr member
    have back := (restRegs rr n1 n8 n9 n18 n19 n20 n21 n22 n23 n2).trans
      ((regs rr n10 n22 n11).trans ((keep rr callee (by simp)).trans
        ((headDone.keep rr callee (by simp)).trans (stage.keep rr callee (by simp)))))
    have initial : stage.headerCore.get rr=call.original.get rr := by
      have casesReg : rr=24 ∨ rr=25 ∨ rr=26 ∨ rr=27 := by simpa only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using member
      rcases casesReg with rfl|rfl|rfl|rfl
      · exact q.x24
      · exact q.x25
      · exact q.x26
      · exact q.x27
    exact back.trans initial
  have returnedCaller : FormatCursor.Returned call.original f :=
    ⟨by rw [fpc,saved.x1],f2.trans h.sp.symm,completeCsr,f1.trans saved.x1,f8.trans saved.x8,f9.trans saved.x9,
      f18.trans saved.x18,f19.trans saved.x19,f20.trans saved.x20,f21.trans saved.x21,f22.trans saved.x22,f23.trans saved.x23,
      extra 24 (by decide),extra 25 (by decide),extra 26 (by decide),extra 27 (by decide)⟩
  have headerBytes : Bytes.Span B final call.tx (header call) := by
    apply ViewFrame.span q.headerBytes
    intro i
    exact allFrame _ (headerObj i) (WordRegions.symm (WordRegions.shrink h.resultTx (by decide) (by change (header call).length≤1024;omega)) i)
  have frame (x : Word) (hs : ∀ i : Fin 144,x≠call.frame+BitVec.ofNat 32 i.val)
      (ho : ∀ i : Fin 89,x≠call.obj+BitVec.ofNat 32 i.val) (hr : ∀ i : Fin 8,x≠call.res+BitVec.ofNat 32 i.val)
      (ht : ∀ i : Fin 192,x≠call.tx+BitVec.ofNat 32 i.val) : final x=call.before x :=
    (allFrame x ho hr).trans (q.memoryFrame x hs ho ht)
  have masked : c.mie_=false := (congrArg Prod.fst (csr.trans (headDone.csr.trans (stage.csr.trans q.csr)))).trans call.masked
  exact ⟨masked,11+11,⟨f,final⟩,finish.trans restore,Or.inr ⟨returnedCaller,
    SendFinishData.result_value _ _ _ _ _ (WordRegions.symm h.resultObject),
    SendFinishData.close_value _ _ _ _ _ (WordRegions.symm h.resultObject),
    SendFinishData.done_value _ _ _ _ _ (WordRegions.symm h.resultObject),headerBytes,frame,queue⟩⟩

theorem body_boundary {call : Call} (stage : Selected call) {headCore headRam anchor m g}
    (headDone : HeadDone call stage headCore headRam)
    (prepared : SendUartReactive.Prepared headCore anchor headRam (bodyPre call headRam) call.obj call.io
      (call.tx+192#32) (body call) 0x8000044e#32)
    (post : UartWritePhase.Cut anchor (bodyPre call headRam) (call.obj+48#32) call.io
      (call.tx+192#32) (body call) [] m g) : ReactiveEnvelope.Envelope (Cut call) m g := by
  rcases post with active|returned
  · exact ⟨UartTxPhase.masked active.2.2.1,0,m,.refl _,Or.inl (.body stage headCore headRam anchor headDone prepared active)⟩
  · exact after_body stage headDone prepared returned

/-- First UART return selects the actual body slice and constructs the second
    real UART future. Its queue is the header call's remaining suffix. -/
theorem after_head {call : Call} (stage : Selected call) {anchor c ram g}
    (prepared : SendUartReactive.Prepared stage.core anchor stage.ram (headPre call stage.ram) call.obj call.io
      call.tx (header call) 0x8000042e#32)
    (returned : UartWritePhase.Returned anchor (headPre call stage.ram) (call.obj+48#32) call.io
      call.tx (header call) (body call) c ram g) : ReactiveEnvelope.Envelope (Cut call) ⟨c,ram⟩ g := by
  let h := call.input
  let q := stage.post
  obtain ⟨pc,keep,csr,lower,frame,memory,queue⟩ := SendUartReactive.finish prepared returned
  have headDone : HeadDone call stage c ram := ⟨pc,keep,csr,lower,frame,memory⟩
  have objKeep : c.get 8=call.obj := (keep 8 (by decide) (by simp)).trans ((stage.keep 8 (by decide) (by simp)).trans q.x8)
  have futureKeep : c.get 18=call.obj+48#32 := (keep 18 (by decide) (by simp)).trans ((stage.keep 18 (by decide) (by simp)).trans q.x18)
  have prefix1 : ViewFrame.Region stage.ram (headPre call stage.ram) call.obj 20 := SendHeadUartCallData.prefixRegion _ _ _ _ _ _ _
  have ptr := (ViewFrame.word lower 0 (by decide)).trans ((ViewFrame.word prefix1 0 (by decide)).trans q.bodyPointer)
  have cap := (ViewFrame.word lower 4 (by decide)).trans ((ViewFrame.word prefix1 4 (by decide)).trans q.bodyCapacity)
  have io := (ViewFrame.word lower 16 (by decide)).trans ((ViewFrame.word prefix1 16 (by decide)).trans q.cachedIo)
  have len := (ViewFrame.word lower 20 (by decide)).trans (SendHeadUartCallData.slot20 stage.ram call.obj call.io call.tx
    (BitVec.ofNat 32 (body call).length) (ResponseHeadBodyMath.boolWord call.close) (header call).length)
  have payloadBound := SendInput.payload_bound h
  have bodyBound : (body call).length≤832 := Nat.le_trans (SendSelect.length call.payload call.status call.headOnly) payloadBound
  have bodyApart := Subregion.left (WordRegions.symm h.objectTx) 192 (body call).length (by omega)
  have sourcePayload : ReadBytes.Span B img ram (call.tx+192#32) call.payload := ReadFrame.span q.payloadBytes
    (fun i => frame _ (Subregion.left (WordRegions.symm h.objectTx) 192 call.payload.length (by omega) i))
  have source : ReadBytes.Span B img ram (call.tx+192#32) (body call) := SendSelect.span sourcePayload
  have masked : c.mie_=false := (congrArg Prod.fst (csr.trans (stage.csr.trans q.csr))).trans call.masked
  obtain ⟨b,setup,pre⟩ := SendUartReactive.body c ram call.obj call.io (call.tx+192#32) (body call) bodyBound
    objKeep futureKeep h.object h.objectAligned cap len ptr io source (Subregion.nowrap h.txStrict 192 (body call).length (by omega)) bodyApart masked pc
  obtain ⟨pending,phase,remaining⟩ := queue
  have pendingQueue : pending.remaining=body call++[] := by simpa only [List.append_nil] using remaining
  have uart := UartWritePhase.start pre.input phase pendingQueue
  have envelope := ReactiveEnvelope.bind uart (fun _ post => body_boundary stage headDone pre post)
  obtain ⟨mask,n,last,quiet,final⟩ := envelope
  exact ⟨masked,12+n,last,setup.trans quiet,final⟩

theorem head_boundary {call : Call} (stage : Selected call) {anchor m g}
    (prepared : SendUartReactive.Prepared stage.core anchor stage.ram (headPre call stage.ram) call.obj call.io
      call.tx (header call) 0x8000042e#32)
    (post : UartWritePhase.Cut anchor (headPre call stage.ram) (call.obj+48#32) call.io
      call.tx (header call) (body call) m g) : ReactiveEnvelope.Envelope (Cut call) m g := by
  rcases post with active|returned
  · exact ⟨UartTxPhase.masked active.2.2.1,0,m,.refl _,Or.inl (.head stage anchor prepared active)⟩
  · exact after_head stage prepared returned

theorem start_selected {call : Call} (stage : Selected call) {g : State} {p : Pending}
    (phase : g.phase=.reply p) (queue : p.remaining=header call++body call) :
    ReactiveEnvelope.Envelope (Cut call) ⟨stage.core,stage.ram⟩ g := by
  let h := call.input
  let q := stage.post
  have headerLimit : (header call).length≤120 := by
    have bound := (ResponseHeadPlan.bounds call.status call.ct call.payload.length call.close
      (by have := h.statusLo;omega) h.statusHi h.ctBound (SendInput.payload_bound h)).1 ⟨11,by decide⟩
    rw [ResponseHeadPlan.all] at bound
    exact bound
  have obj := (stage.keep 8 (by decide) (by simp)).trans q.x8
  have future := (stage.keep 18 (by decide) (by simp)).trans q.x18
  have tx := (stage.keep 19 (by decide) (by simp)).trans q.x19
  have close := (stage.keep 22 (by decide) (by simp)).trans q.x22
  have masked : stage.core.mie_=false := (congrArg Prod.fst (stage.csr.trans q.csr)).trans call.masked
  obtain ⟨anchor,setup,pre⟩ := SendUartReactive.head stage.core stage.ram call.obj call.io call.tx
    (BitVec.ofNat 32 (body call).length) (ResponseHeadBodyMath.boolWord call.close) (header call) headerLimit
    obj future tx stage.bodyLength stage.headerLength close h.object h.objectAligned q.cachedIo
    (ReadBytes.of_ram q.headerBytes) (by have := h.txStrict;omega)
    (WordRegions.shrink (WordRegions.symm h.objectTx) (by omega) (by decide)) masked stage.pc
  have envelope := ReactiveEnvelope.bind (UartWritePhase.start pre.input phase queue)
    (fun _ post => head_boundary stage pre post)
  obtain ⟨mask,n,last,quiet,final⟩ := envelope
  exact ⟨masked,12+n,last,setup.trans quiet,final⟩

/-- Real header rendering, body selection, and both reactive UART calls.
    Every oracle prefix refines the queued bytes; readiness is never assumed. -/
theorem start (call : Call) {g : State} {p : Pending}
    (phase : g.phase=.reply p) (queue : p.remaining=header call++body call) :
    ReactiveEnvelope.Envelope (Cut call) ⟨call.original,call.before⟩ g := by
  obtain ⟨c,n,ram,bound,render,q⟩ := SendHeader.contract call.original call.before call.frame call.obj call.res call.tx call.io call.ctptr
    call.raw call.status call.ct call.payload call.close call.headOnly call.input
  obtain ⟨d,k,limit,select,pc,bodyLength,regs,csr⟩ := SendSelect.contract B c ram call.payload call.status call.headOnly
    call.input.statusLo call.input.statusHi q.resultTag q.x20 q.x21 q.x23 q.pc
  have keep : ResponseHeadCallee.Keep c d [] := by
    intro r kept safe
    apply regs r
    all_goals intro eq;subst r;simp [ResponseHeadCallee.Registers] at kept
  let stage : Selected call := ⟨c,ram,d,q,pc,bodyLength,(regs 11 (by decide) (by decide)).trans q.resultLength,keep,csr⟩
  obtain ⟨mask,rest,last,quiet,final⟩ := start_selected stage phase queue
  exact ⟨call.masked,n+k+rest,last,(render.trans select).trans quiet,final⟩

theorem next {call : Call} {m g} (h : Active call m g) (o : Oracle) :
    ∃ d reads evs next,Observed.stepInstr B img m o=⟨.ok d m.ram evs,reads⟩ ∧
      ProtocolStreamTrace.Trace g (Observed.input reads) (Observed.output evs) next ∧
      ReactiveEnvelope.Envelope (Cut call) ⟨d,m.ram⟩ next := by
  cases h with
  | head stage anchor prepared active =>
    obtain ⟨d,reads,evs,next,step,trace,post⟩ := UartWritePhase.next prepared.input active o
    exact ⟨d,reads,evs,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => head_boundary stage prepared cut)⟩
  | body stage headCore headRam anchor headDone prepared active =>
    obtain ⟨d,reads,evs,next,step,trace,post⟩ := UartWritePhase.next prepared.input active o
    exact ⟨d,reads,evs,next,step,trace,ReactiveEnvelope.bind post (fun _ cut => body_boundary stage headDone prepared cut)⟩

theorem safe {call : Call} {m g} (h : Active call m g) : ¬Escapes B img m := by
  cases h with
  | head _ _ _ active => exact UartWritePhase.safe active
  | body _ _ _ _ _ _ active => exact UartWritePhase.safe active

/-- A Send UART instruction observes only LSR, source memory, or THR; it
    never accepts an RBR byte. This supplies the output-only stream join. -/
theorem uart_no_input {c ram g suffix} (h : UartTxPhase.At c ram g suffix) (o : Oracle) :
    Observed.input (Observed.stepInstr B img ⟨c,ram⟩ o).reads=[] := by
  cases h with
  | loading _ _ live =>
    obtain ⟨step,post⟩ := UartTxReactive.load live
    rw [step o];rfl
  | polling _ _ live =>
    obtain ⟨d,reads,step,post,only,regs,csr⟩ := UartTxReactive.polling_next live o
    rw [step]
    rcases only with nil|⟨value,single⟩
    · rw [nil];rfl
    · rw [single];rfl
  | before _ _ live =>
    obtain ⟨step,post⟩ := UartTxReactive.increment live
    rw [step o];rfl
  | emitting _ _ live =>
    obtain ⟨step,post⟩ := UartTxReactive.emit live o
    rw [step];rfl
  | branch _ _ live =>
    obtain ⟨d,step,pc,context,pointer,regs,csr⟩ := UartTxReactive.branch live
    rw [step o];rfl

theorem no_input {call : Call} {m g} (h : Active call m g) (o : Oracle) :
    Observed.input (Observed.stepInstr B img m o).reads=[] := by
  cases h with
  | head _ _ _ active => exact uart_no_input active.2.2.1 o
  | body _ _ _ _ _ _ active => exact uart_no_input active.2.2.1 o

end E5R.Thermostat.SendPhase
