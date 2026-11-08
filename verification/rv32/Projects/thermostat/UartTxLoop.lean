import Projects.thermostat.UartTxTurn
import Projects.thermostat.WordZero
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.UartTxLoop
open E5R E5R.Thermostat
abbrev B := UartPlatform.board

/-- A finite status-read schedule for one byte. Validity is an explicit
    environment premise, not a readiness guarantee provided by the platform. -/
structure Slot where
  waits : List Word
  ready : Word
  notReady : ∀ s ∈ waits, UartTxPoll.mask s=0#32
  isReady : UartTxPoll.mask ready≠0#32

def duration (slots : List Slot) : Nat := slots.foldr (fun s n => 5*s.waits.length+7+n) 0
def reads (slots : List Slot) : List Observed.Read := slots.flatMap (fun s => UartTxWait.log (s.waits++[s.ready]))
def events (bs : List (BitVec 8)) : List Event := bs.map (fun b => ⟨0x10000000#32,UartTxByte.word b⟩)

/-- Actual byte loop with exact arbitrary finite wait schedules, RAM/ROM
    source views and explicit nonwrapping range. Order and all UART events
    follow from the real LBU/LSR/SB/branches, without a semantic send summary. -/
theorem contract (c : Core) (ram : Word → BitVec 8) (src : Word) (bs : List (BitVec 8)) (slots : List Slot)
    (hn : 0<bs.length) (hlen : slots.length=bs.length)
    (hp : c.pc=0x800007f4#32) (h12 : c.get 12=src) (h14 : c.get 14=src+BitVec.ofNat 32 bs.length)
    (h13 : c.get 13=0x10000000#32) (h15 : c.get 15=0x10000000#32)
    (hs : ReadBytes.Span B img ram src bs) (hw : src.toNat+bs.length<2^32) :
    ∃ d, Observed.Steps B img (duration slots) ⟨c,ram⟩ ⟨d,ram⟩ (reads slots) (events bs) ∧
      d.pc=0x8000080a#32 ∧ d.get 12=src+BitVec.ofNat 32 bs.length ∧
      (∀ r : Reg, r≠12 → r≠16 → r≠17 → d.get r=c.get r) ∧ d.sameCsr c := by
  induction bs generalizing c src slots with
  | nil => simp only [List.length_nil] at hn;omega
  | cons v vs ih =>
    cases slots with
    | nil => simp only [List.length_nil,List.length_cons] at hlen;omega
    | cons slot rest =>
      have hlen' : rest.length=vs.length := by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hlen
      have ht : taken .eq (src+1#32) (src+BitVec.ofNat 32 (v::vs).length)=decide (vs=[]) := by
        change decide (src+1#32=src+BitVec.ofNat 32 (v::vs).length)=_
        have he : src+1#32=src+BitVec.ofNat 32 (v::vs).length ↔ vs=[] := by
          rw [BitVec.add_right_inj]
          constructor
          · intro h
            have hv := congrArg BitVec.toNat h
            have hl : (v::vs).length<2^32 := by omega
            simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl] at hv
            have hzero : vs.length=0 := by simp only [List.length_cons] at hv;omega
            exact List.eq_nil_of_length_eq_zero hzero
          · intro h;subst vs;rfl
        simp only [he]
      obtain ⟨a,ta,pa,a12,ar,ac⟩ := UartTxTurn.contract c ram src _ v slot.waits slot.ready (decide (vs=[])) hp h12 h14 h13 h15
        (ReadBytes.head hs) slot.notReady slot.isReady ht
      by_cases hz : vs=[]
      · subst vs
        have hr : rest=[] := List.eq_nil_of_length_eq_zero (by simpa only [List.length_nil] using hlen')
        subst rest
        refine ⟨a,?_,by simpa only [decide_true,ite_true] using pa,a12,ar,ac⟩
        simpa only [duration,List.foldr_cons,List.foldr_nil,Nat.add_zero,reads,List.flatMap_cons,List.flatMap_nil,List.append_nil,events,List.map_cons,List.map_nil] using ta
      · have hpos : 0<vs.length := List.length_pos_iff.mpr hz
        have hnext : (src+1#32).toNat=src.toNat+1 := WordZero.add_nat src 1 (by have := hs.length;change vs.length+1<2^32 at this;simp only [List.length_cons] at hw;omega)
        have he : (src+1#32)+BitVec.ofNat 32 vs.length=src+BitVec.ofNat 32 (v::vs).length := by
          rw [BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 vs.length]
        obtain ⟨d,td,pd,d12,dr,dc⟩ := ih a (src+1#32) rest hpos hlen'
          (by simpa only [decide_eq_false hz,Bool.false_eq_true,ite_false] using pa) a12
          (by rw [ar 14 (by decide) (by decide) (by decide),h14,he])
          ((ar 13 (by decide) (by decide) (by decide)).trans h13)
          ((ar 15 (by decide) (by decide) (by decide)).trans h15)
          (ReadBytes.tail hs) (by rw [hnext];simp only [List.length_cons] at hw;omega)
        refine ⟨d,?_,pd,d12.trans he,fun r h12 h16 h17 => (dr r h12 h16 h17).trans (ar r h12 h16 h17),dc.trans ac⟩
        simpa only [duration,List.foldr_cons,reads,List.flatMap_cons,events,List.map_cons,List.singleton_append] using ta.trans td

theorem output (bs : List (BitVec 8)) : Observed.output (events bs)=bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have he : events (b::bs)=[⟨0x10000000#32,UartTxByte.word b⟩]++events bs := rfl
    rw [he,Observed.output_append,UartTxByte.output,ih];rfl

theorem no_input (slots : List Slot) : Observed.input (reads slots)=[] := by
  induction slots with
  | nil => rfl
  | cons s ss ih =>
    change Observed.input (UartTxWait.log (s.waits++[s.ready])++reads ss)=[]
    rw [Observed.input_append,UartTxWait.no_input,ih];rfl
end E5R.Thermostat.UartTxLoop
