import Projects.thermostat.WriteHandlerPrepare
import Projects.thermostat.StackRuntimeApiWriteCaller
import Projects.thermostat.StackWriteSuccessFrame
import Projects.thermostat.StackWriteErrorFrame
import Projects.thermostat.StackRuntimeApiWriteRefusalHandler
import Projects.thermostat.StackWriteReturnPrepare
set_option autoImplicit false
set_option maxRecDepth 6000
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.StackWriteHandlerPrepare
open E5R E5R.Thermostat HttpRequestSpec RuntimeApiWriteCaller WriteHandlerPrepare
abbrev B := StackBoard.board
abbrev fp := WriteHandlerPrepare.fp
theorem success {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {close : Bool} {used : Word}
    (h : StackRuntimeApiWriteCaller.Ready kind future path first c ram input s head amount rawUsed served close) (cmd : Spec.Command) (res : Spec.Success)
    (allow : AuthSpec.authorized (HeaderSpec.lookup (RuntimeRequestSpans.raw input rawUsed) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true)
    (decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first=.ok cmd)
    (result : Spec.transition true s cmd=.ok res)
    (loopMetadata : LoopTransactionMemory.At ram used) (uart : c.get 19=0x10000000#32)
    (futureReg : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (masked : c.mie_=false) :
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (successReply s res) served used true close false := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address]
    exact Memory.sub_block StackBoard.available positive bound
  have pre : WriteInput.Pre B c ram (0x80ffe9f0#32+240#32) future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
      (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s := by
    simpa only [show 0x80ffe9f0#32+240#32=0x80ffeae0#32 by decide +kernel] using h.pre
  obtain ⟨a,na,mid,ba,ta,ret,response,bytes,state,borrow,inv,_,_,_,memory⟩ := StackWriteSuccessFrame.contract_inv_quiet c ram
    0x80ffe9f0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len) 0x80fff4d4#32
    (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first 832 true s cmd res pre allow decoded result h.invariant
    (block _ 59888 416 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) h.capacity h.pointer (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (block _ 62676 832 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (block _ 64824 15 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have region (obj : Word) (size : Nat)
      (hs : WordRegions.Disjoint obj size 0x80ffe9f0#32 416)
      (hd : WordRegions.Disjoint obj size 0x80fff4d4#32 832)
      (ho : WordRegions.Disjoint obj size 0x80fffd38#32 15)
      (hf : WordRegions.Disjoint obj size future 41)
      (he : WordRegions.Disjoint obj size 0x80ffebbc#32 14) : ViewFrame.Region ram mid obj size :=
    fun i => memory _ (hs i) (hd i) (ho i) (hf i) (he i)
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have app : AppState.At mid (Spec.commit s (.ok res)) := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.app.keyLen
  have nextInvariant : Spec.Inv (Spec.commit s (.ok res)) := by
    simpa only [result] using Spec.commit_inv true s cmd h.invariant
  have metadata : ViewFrame.Region ram mid fp 532 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have notHead : MainMethod.head (mid 0x80fff9f4#32)=false := by
    have byte := metadata ⟨480,by decide⟩
    have preserved : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by
      simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [preserved];exact h.notHead
  have body : ResponseHeadSpec.body 200 (MainMethod.head (mid 0x80fff9f4#32)) (ReplyJson.snapshot res.reply)=ReplyJson.snapshot res.reply := by rw [notHead];rfl
  have pc : a.pc=MainWriteReturnJoin.entry kind := by
    have masks : ∀ k : Fin 4, MainWriteReturnJoin.entry k &&& ~~~1=MainWriteReturnJoin.entry k := by decide +kernel
    rw [ret.pc,h.ret,masks]
  have capacityFrame : ViewFrame.Region ram mid 0x80ffeba0#32 4 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (MainRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  have nextMetadata := LoopTransactionMemory.preserve loopMetadata (ViewFrame.shrink metadata (by decide)) capacityFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink metadata (by decide))) h.serve
  have returnReady : WriteReturnPrepare.Ready kind a mid (successReply s res) served used true close false :=
    ⟨pc,ret.sp.trans h.sp,ret.x8.trans h.fp,ret.x19.trans uart,ret.x22.trans h.one,ret.x18.trans h.two,
      ret.x23.trans futureReg,ret.x26.trans three,(congrArg Prod.fst ret.csr).trans masked,h.stack,app,nextInvariant,serve,room,nextMetadata,rfl,
      (by exact Nat.le_trans (JsonCapacity.snapshot_length res.reply) (by decide)),(by change 200≤200;decide),(by change 200≤599;decide),(response),(StackAccess.span bytes),cap,flag,notHead⟩
  obtain ⟨nb,d,after,bound,prepare,ready⟩ := StackWriteReturnPrepare.contract returnReady
  exact ⟨na+nb,d,after,ta.trans prepare,ready⟩

theorem error {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {close : Bool} {used : Word}
    (h : StackRuntimeApiWriteCaller.Ready kind future path first c ram input s head amount rawUsed served close) (cmd : Spec.Command) (err : Spec.Error)
    (allow : AuthSpec.authorized (HeaderSpec.lookup (RuntimeRequestSpans.raw input rawUsed) (WireSpec.ascii "authorization") (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key")=true)
    (decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first=.ok cmd)
    (result : Spec.transition true s cmd=.error err)
    (loopMetadata : LoopTransactionMemory.At ram used) (uart : c.get 19=0x10000000#32)
    (futureReg : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (masked : c.mie_=false) :
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (errorReply s err) served used true close false := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  have block (p : Word) (off n : Nat) (positive : 0<n) (address : 0x80ff0000#32+BitVec.ofNat 32 off=p) (bound : off+n≤65536) : Memory.Block B p n := by
    rw [←address]
    exact Memory.sub_block StackBoard.available positive bound
  have pre : WriteInput.Pre B c ram (0x80ffe9f0#32+240#32) future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
      (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len)
      (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first true s := by
    simpa only [show 0x80ffe9f0#32+240#32=0x80ffeae0#32 by decide +kernel] using h.pre
  obtain ⟨a,na,mid,ba,ta,ret,response,bytes,state,borrow,inv,_,_,_,memory⟩ := StackWriteErrorFrame.contract_inv_quiet c ram
    0x80ffe9f0#32 future 0x80fffd38#32 0x80fff880#32 0x80ffebbc#32 0x80ffec14#32
    (0x80ffec14#32+BitVec.ofNat 32 head.target.1) (0x80ffec14#32+BitVec.ofNat 32 head.len) 0x80fff4d4#32
    (RuntimeRequestSpans.raw input rawUsed) path (MainRequestSpans.body input head amount) (MainRequestInputs.entries head) first 832 true s cmd err pre allow decoded result h.invariant
    (block _ 59888 416 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) h.capacity h.pointer (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (block _ 62676 832 (by decide) (by decide +kernel) (by decide)) (by decide) (by decide)
    (block _ 64824 15 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by decide +kernel) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have region (obj : Word) (size : Nat)
      (hs : WordRegions.Disjoint obj size 0x80ffe9f0#32 416)
      (hd : WordRegions.Disjoint obj size 0x80fff4d4#32 832)
      (ho : WordRegions.Disjoint obj size 0x80fffd38#32 15)
      (hf : WordRegions.Disjoint obj size future 41)
      (he : WordRegions.Disjoint obj size 0x80ffebbc#32 14) : ViewFrame.Region ram mid obj size :=
    fun i => memory _ (hs i) (hd i) (ho i) (hf i) (he i)
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have app : AppState.At mid (Spec.commit s (.error err)) := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.app.keyLen
  have nextInvariant : Spec.Inv (Spec.commit s (.error err)) := by
    simpa only [result] using Spec.commit_inv true s cmd h.invariant
  have metadata : ViewFrame.Region ram mid fp 532 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have notHead : MainMethod.head (mid 0x80fff9f4#32)=false := by
    have byte := metadata ⟨480,by decide⟩
    have preserved : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by
      simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [preserved];exact h.notHead
  have body : ResponseHeadSpec.body (ReplyJson.errorStatus err) (MainMethod.head (mid 0x80fff9f4#32)) (ReplyJson.errorBody err)=ReplyJson.errorBody err := by rw [notHead];cases err <;> rfl
  have pc : a.pc=MainWriteReturnJoin.entry kind := by
    have masks : ∀ k : Fin 4, MainWriteReturnJoin.entry k &&& ~~~1=MainWriteReturnJoin.entry k := by decide +kernel
    rw [ret.pc,h.ret,masks]
  have capacityFrame : ViewFrame.Region ram mid 0x80ffeba0#32 4 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := region _ _
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (MainRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  have nextMetadata := LoopTransactionMemory.preserve loopMetadata (ViewFrame.shrink metadata (by decide)) capacityFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink metadata (by decide))) h.serve
  have returnReady : WriteReturnPrepare.Ready kind a mid (errorReply s err) served used true close false :=
    ⟨pc,ret.sp.trans h.sp,ret.x8.trans h.fp,ret.x19.trans uart,ret.x22.trans h.one,ret.x18.trans h.two,
      ret.x23.trans futureReg,ret.x26.trans three,(congrArg Prod.fst ret.csr).trans masked,h.stack,app,nextInvariant,serve,room,nextMetadata,rfl,
      (by dsimp only [errorReply];cases err <;> decide +kernel),(by dsimp only [errorReply];cases err <;> decide +kernel),(by dsimp only [errorReply];cases err <;> decide +kernel),(by cases err <;> exact response),(StackAccess.span bytes),cap,flag,notHead⟩
  obtain ⟨nb,d,after,bound,prepare,ready⟩ := StackWriteReturnPrepare.contract returnReady
  exact ⟨na+nb,d,after,ta.trans prepare,ready⟩

theorem refusal {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))} {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head} {amount rawUsed served : Nat} {close : Bool} {used : Word}
    (h : StackRuntimeApiWriteCaller.Ready kind future path first c ram input s head amount rawUsed served close) (status : Nat) (outcome : RefusalCase input head amount rawUsed path first status)
    (hlo : 200≤status) (hst : status≤599)
    (loopMetadata : LoopTransactionMemory.At ram used) (uart : c.get 19=0x10000000#32)
    (futureReg : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (masked : c.mie_=false) :
    ∃ n d after,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (refusalReply s status) served used false close false := by
  have ⟨futureLow,futureHigh⟩ := h.futureBounds
  obtain ⟨a,na,mid,ba,ta,ret,response,state,borrow,inv,memory⟩ := StackRuntimeApiWriteRefusalHandler.refusal_handler h status outcome
  have keys : ViewFrame.Region ram mid 0x80ffebcc#32 9 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have app : AppState.At mid s := by
    refine ⟨state,borrow,?_,?_,(keys ⟨8,by decide⟩).trans h.app.principal⟩
    · have word := ViewFrame.word keys 0 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
      simpa only [BitVec.add_zero] using word.trans h.app.keyPtr
    · exact (ViewFrame.word keys 4 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))).trans h.app.keyLen
  have metadata : ViewFrame.Region ram mid fp 532 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))) (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have word (off : Nat) (bound : off+4≤532) := ViewFrame.word metadata off bound
  have cap : ramRead mid 0x80fff9fc#32 .w=832#32 := by
    have value := word 488 (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))
    simpa only [show fp+BitVec.ofNat 32 (488 : Nat)=0x80fff9fc#32 by decide +kernel] using value.trans h.replyCapacity
  have flag : mid 0x80fff878#32=Encoding.boolByte close := by
    have byte := metadata ⟨100,by decide⟩
    simpa only [show fp+100#32=0x80fff878#32 by decide +kernel] using byte.trans h.closeByte
  have pc : a.pc=MainWriteReturnJoin.entry kind := by
    have masks : ∀ k : Fin 4, MainWriteReturnJoin.entry k &&& ~~~1=MainWriteReturnJoin.entry k := by decide +kernel
    rw [ret.pc,h.ret,masks]
  have capacityFrame : ViewFrame.Region ram mid 0x80ffeba0#32 4 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
  have routeFrame : ViewFrame.Region ram mid 0x80ffebd8#32 60 := MainFutureFrame.region memory
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega)) (by first | decide +kernel | ((try simp only [fp,BitVec.toNat_ofNat,Nat.reduceMod]) <;> omega))))
  have room : close=false → served<100 := by
    intro kept
    by_cases reached : 100≤served
    · have forced := MainCloseSpec.limit head.minor served reached (RuntimeRequestSpans.raw input rawUsed) (MainRequestInputs.entries head)
      have contradiction := h.closeSpec.trans forced
      rw [kept] at contradiction;cases contradiction
    · omega
  have nextMetadata := LoopTransactionMemory.preserve loopMetadata (ViewFrame.shrink metadata (by decide)) capacityFrame routeFrame
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink metadata (by decide))) h.serve
  have notHead : MainMethod.head (mid 0x80fff9f4#32)=false := by
    have byte := metadata ⟨480,by decide⟩
    have same : mid 0x80fff9f4#32=ram 0x80fff9f4#32 := by simpa only [show fp+480#32=0x80fff9f4#32 by decide +kernel] using byte
    rw [same];exact h.notHead
  have returnReady : WriteReturnPrepare.Ready kind a mid (refusalReply s status) served used false close false :=
    ⟨pc,ret.sp.trans h.sp,ret.x8.trans h.fp,ret.x19.trans uart,ret.x22.trans h.one,ret.x18.trans h.two,
      ret.x23.trans futureReg,ret.x26.trans three,(congrArg Prod.fst ret.csr).trans masked,h.stack,app,h.invariant,serve,room,nextMetadata,rfl,
      (by change (0 : Nat)≤832;decide),(hlo),(hst),(MainStatusResponse.as_body response),(Bytes.empty UartPlatform.board mid _),cap,flag,notHead⟩
  obtain ⟨nb,d,after,bound,prepare,ready⟩ := StackWriteReturnPrepare.contract returnReady
  exact ⟨na+nb,d,after,ta.trans prepare,ready⟩

/-- Every authentication, typed-decode and kernel outcome reaches actual
    common Send preparation. No selected outcome or completed UART run is a
    premise of this exhaustive handler theorem. -/
theorem prepare {kind : Fin 4} {future : Word} {path : List (BitVec 8)} {first : Option (List (BitVec 8))}
    {c : Core} {ram : Word → BitVec 8} {input : List (BitVec 8)} {s : Spec.Snapshot} {head : Head}
    {amount rawUsed served : Nat} {close : Bool} {used : Word}
    (h : StackRuntimeApiWriteCaller.Ready kind future path first c ram input s head amount rawUsed served close)
    (metadata : LoopTransactionMemory.At ram used) (uart : c.get 19=0x10000000#32)
    (futureReg : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32) (masked : c.mie_=false) :
    let response := ApiWriteHttpSpec.run s path first (RuntimeRequestSpans.raw input rawUsed)
      (MainRequestSpans.body input head amount) (MainRequestInputs.entries head)
    ∃ n d after json,Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧ NormalSendPhase.Ready d after response served used json close false := by
  dsimp only
  cases allowed : AuthSpec.authorized (HeaderSpec.lookup (RuntimeRequestSpans.raw input rawUsed) (WireSpec.ascii "authorization")
      (MainRequestInputs.entries head)) (WireSpec.ascii "dev-key") with
  | false =>
    simp only [ApiWriteHttpSpec.run,allowed,Bool.false_eq_true,ite_false]
    obtain ⟨n,d,after,quiet,ready⟩ := refusal h 401 (Or.inl ⟨allowed,rfl⟩) (by decide) (by decide) metadata uart futureReg three masked
    exact ⟨n,d,after,false,quiet,ready⟩
  | true =>
    cases decoded : WireSpec.decode path (MainRequestSpans.body input head amount) first with
    | error status =>
      simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded]
      have statuses := ApiWriteHttpSpec.decode_errors path (MainRequestSpans.body input head amount) first status decoded
      obtain ⟨n,d,after,quiet,ready⟩ := refusal h status (Or.inr ⟨allowed,decoded⟩) (by omega) (by omega) metadata uart futureReg three masked
      exact ⟨n,d,after,false,quiet,ready⟩
    | ok cmd =>
      cases result : Spec.transition true s cmd with
      | error err =>
        simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded,result]
        obtain ⟨n,d,after,quiet,ready⟩ := error h cmd err allowed decoded result metadata uart futureReg three masked
        exact ⟨n,d,after,true,quiet,ready⟩
      | ok res =>
        simp only [ApiWriteHttpSpec.run,allowed,ite_true,decoded,result]
        obtain ⟨n,d,after,quiet,ready⟩ := success h cmd res allowed decoded result metadata uart futureReg three masked
        exact ⟨n,d,after,true,quiet,ready⟩

end E5R.Thermostat.StackWriteHandlerPrepare
