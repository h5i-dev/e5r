import Projects.thermostat.ReadHandlerPrepare
import Projects.thermostat.StackRuntimeReadViews
import Projects.thermostat.StackLoopReadResponse
set_option autoImplicit false
set_option maxRecDepth 6000
set_option maxHeartbeats 3000000
namespace E5R.Thermostat.StackReadHandlerPrepare
open E5R E5R.Thermostat HttpRequestSpec ReadHandlerPrepare
abbrev B := StackBoard.board
theorem contract {c ram input state served close isHead used}
    (ready : StackRuntimeReadViews.DecodedReady c ram input state served close isHead)
    (metadata : LoopTransactionMemory.At ram used) (future : c.get 23=0x80fff9f0#32) (three : c.get 26=3#32)
    (room : close=false → served<100) :
    ∃ n d after,n≤4144 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,after⟩ ∧
      NormalSendPhase.Ready d after (reply state) served used true close isHead := by
  let h := ready.acquiredInput
  let hi := ready.stable.invariant
  let happ := ready.stable.app
  let hm := ready.stable.stack
  let h24 := ready.payload
  let h20 := ready.capacity
  let h22 := ready.stable.one
  let hcap := ready.replyCapacity
  let htx := ready.serve.tx
  let htxcap := ready.serve.txCapacity
  have hclose : ram 0x80fff878#32=(if close then 1#8 else 0#8) := by cases close <;> exact ready.closeByte
  let io := 0x80ffffc7#32
  obtain ⟨a,na,ra,ba,ta,pa,a2,a8,ka,_,hbytes,hstate,hborrow,_,a9,hdesc,hkeys,a24,lowA,capA,routesA,a19,a22,a18,a23,a26⟩ := StackLoopReadResponse.contract_inv_quiet c ram 0x80fff4d4#32 832 state
    0x80fff414#32 io close htx htxcap ready.serve.uart hclose h hi StackBoard.available h24 h20 h22 (by decide) (by decide)
    (by change Memory.Block StackBoard.board 0x80fff4d4#32 832;unfold Memory.Block StackBoard.board;decide +kernel)
    (by decide) hcap
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.symm (WordRegions.before _ _ _ _ (by decide) (by decide)))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have appRead : AppState.At ra state := by
    refine ⟨hstate,hborrow,?_,?_,?_⟩
    · have hh := ViewFrame.word hkeys 0 (by decide)
      simpa only [BitVec.add_zero] using hh.trans happ.keyPtr
    · have hh := ViewFrame.word hkeys 4 (by decide)
      rw [show 0x80ffebcc#32+4#32=0x80ffebd0#32 by decide +kernel] at hh
      exact hh.trans happ.keyLen
    · have hh := hkeys ⟨8,by decide⟩
      rw [show 0x80ffebcc#32+8#32=0x80ffebd4#32 by decide +kernel] at hh
      exact hh.trans happ.principal
  have hl : (ReplyJson.snapshot state).length≤832 := Nat.le_trans (JsonCapacity.snapshot_length state) (by decide)
  obtain ⟨d,call,pc,resultArg,objArg,returnAddress,regs,csr⟩ := SendCaller.contract B a ra sp 0x80fff878#32 a2 a9 pa
  have finalSp := (regs 2 (by decide) (by decide) (by decide)).trans a2
  have result : d.get 10=0x80fffd38#32 := by simpa only [show sp+4520#32=0x80fffd38#32 by decide +kernel] using resultArg
  have desc : SharedResponseView.Descriptor ra 0x80fff878#32 0x80fff414#32 0x80ffffc7#32 0x800056a8#32
      (ReplyJson.snapshot state).length 200 (WireSpec.ascii "application/json") close isHead := by
    have method : MainMethod.head (ram 0x80fff9f4#32)=isHead := by rw [ready.method];cases isHead <;> rfl
    simpa only [method] using hdesc
  have pre := MainSend.input d ra 0x80ffffc7#32 0x800056a8#32 200 (WireSpec.ascii "application/json") (ReplyJson.snapshot state) close isHead
    pc finalSp result objArg hm hl (by decide) (by decide) (by decide) ResponseHeadSpec.json_field desc (StackAccess.span hbytes) (ResponseLiterals.json _)
    (WordRegions.before _ _ _ _ (by decide) (by decide)) (WordRegions.before _ _ _ _ (by decide) (by decide))
    (WordRegions.before _ _ _ _ (by decide) (by decide))
  have memory := LoopTransactionMemory.preserve metadata lowA capA routesA
  have serve := MainServeLayout.preserve (MainServeLayout.region (ViewFrame.shrink lowA (by decide))) ready.serve
  exact ⟨na+6,d,ra,by omega,ta.trans call,pre,finalSp,(regs 8 (by decide) (by decide) (by decide)).trans a8,
    (regs 19 (by decide) (by decide) (by decide)).trans (a19.trans ready.stable.uart),
    (regs 22 (by decide) (by decide) (by decide)).trans a22,(regs 18 (by decide) (by decide) (by decide)).trans a18,
    (regs 24 (by decide) (by decide) (by decide)).trans a24,
    (regs 23 (by decide) (by decide) (by decide)).trans (a23.trans future),
    (regs 26 (by decide) (by decide) (by decide)).trans (a26.trans three),returnAddress,
    (congrArg Prod.fst (csr.trans ka)).trans ready.stable.masked,appRead,hi,hm,serve,room,memory⟩
end E5R.Thermostat.StackReadHandlerPrepare
