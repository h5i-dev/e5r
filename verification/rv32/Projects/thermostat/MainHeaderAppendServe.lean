import Projects.thermostat.MainHeaderRefill
import Projects.thermostat.MainServeMemoryFrames
namespace E5R.Thermostat.MainHeaderAppendServe
open E5R E5R.Thermostat

/-- Pointwise buffer append, with the new slot and all previous bytes proved
    separately by the actual receive/store theorem. -/
theorem bytes {before after : Word → BitVec 8} {p : Word} {xs : List (BitVec 8)} {b : BitVec 8}
    (old : Bytes.At before p xs) (value : after (p+BitVec.ofNat 32 xs.length)=b)
    (frame : ∀ i : Fin xs.length, after (p+BitVec.ofNat 32 i.val)=before (p+BitVec.ofNat 32 i.val)) :
    Bytes.At after p (xs++[b]) := by
  intro i
  change after (p+BitVec.ofNat 32 i.val)=(xs++[b])[i.val]'i.isLt
  have hi : i.val<xs.length+1 := by have := i.isLt;simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using this
  by_cases previous : i.val<xs.length
  · rw [List.getElem_append_left previous]
    exact (frame ⟨i.val,previous⟩).trans (old ⟨i.val,previous⟩)
  · have index : i.val=xs.length := by omega
    rw [List.getElem_append_right (by omega)]
    simpa only [index,Nat.sub_self,List.getElem_cons_zero] using value

/-- A byte received under an explicit finite schedule extends the real RX
    slice and returns to the real main parse-call site. App state is framed. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (input : List (BitVec 8)) (pending : List Word) (ready datum : Word)
    (hp : c.pc=0x80000ba2#32) (h8 : c.get 8=MainHeaderRefill.fp) (h19 : c.get 19=0x10000000#32) (h22 : c.get 22=1#32)
    (h12 : c.get 12=MainHeaderRefill.rx+BitVec.ofNat 32 input.length)
    (layout : MainHeaderLayout.At ram input.length) (room : input.length<2048) (inputAt : Bytes.At ram MainHeaderRefill.rx input)
    (stack : Memory.Block MainHeaderRefill.B 0x80ff0000#32 65536)
    (notReady : ∀ status ∈ pending, UartPoll.byte status &&& 1#32=0#32) (isReady : UartPoll.byte ready &&& 1#32≠0#32) :
    ∃ d after, Observed.Steps MainHeaderRefill.B img (14+4*pending.length) ⟨c,ram⟩ ⟨d,after⟩ (MainHeaderWait.reads pending ready datum) [] ∧
      d.pc=0x80000a10#32 ∧ d.get 12=BitVec.ofNat 32 (input++[(UartPoll.byte datum).setWidth 8]).length ∧
      MainHeaderLayout.At after (input++[(UartPoll.byte datum).setWidth 8]).length ∧
      Bytes.At after MainHeaderRefill.rx (input++[(UartPoll.byte datum).setWidth 8]) ∧
      (∀ state, AppState.At ram state → AppState.At after state) ∧
      (∀ r : Reg, r≠10 → r≠11 → r≠14 → r≠12 → d.get r=c.get r) ∧ d.sameCsr c ∧ MainServeLayout.Frame ram after := by
  obtain ⟨d,after,trace,pc,count,layoutAfter,value,frame,regs,csr⟩ := MainHeaderRefill.contract c ram input.length pending ready datum hp h8 h19 h22 h12 layout room stack notReady isReady
  have inputAfter : Bytes.At after MainHeaderRefill.rx (input++[(UartPoll.byte datum).setWidth 8]) := by
    apply bytes inputAt value
    intro i
    exact frame _ (Bytes.offset_ne MainHeaderRefill.rx i.val input.length (by have := i.isLt;omega) (by omega) (by have := i.isLt;omega))
      (fun j => WordZero.separated MainHeaderRefill.rx (MainHeaderRefill.fp+84#32) 2048 4 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ j)
      (by simpa only [BitVec.add_zero] using WordZero.separated MainHeaderRefill.rx (MainHeaderRefill.fp+464#32) 2048 1 (by decide +kernel) (by decide +kernel) ⟨i.val,by have := i.isLt;omega⟩ ⟨0,by decide⟩)
  have appFrame : ∀ state, AppState.At ram state → AppState.At after state := by
    intro state app
    apply AppState.preserve ram after state app
    intro i
    exact frame _
      (WordZero.separated 0x80ffebbc#32 MainHeaderRefill.rx 25 2048 (by decide +kernel) (by decide +kernel) i ⟨input.length,room⟩)
      (fun j => WordZero.separated 0x80ffebbc#32 (MainHeaderRefill.fp+84#32) 25 4 (by decide +kernel) (by decide +kernel) i j)
      (by simpa only [BitVec.add_zero] using WordZero.separated 0x80ffebbc#32 (MainHeaderRefill.fp+464#32) 25 1 (by decide +kernel) (by decide +kernel) i ⟨0,by decide⟩)
  refine ⟨d,after,trace,pc,?_,?_,inputAfter,appFrame,regs,csr,MainServeMemoryFrames.received (flag := 464) room (by decide) (by decide) frame⟩
  · simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using count
  · simpa only [List.length_append,List.length_cons,List.length_nil,Nat.zero_add] using layoutAfter
end E5R.Thermostat.MainHeaderAppendServe
