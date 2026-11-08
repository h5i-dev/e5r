import Projects.thermostat.HttpDecCopyTurn
import Projects.thermostat.HttpPutData
namespace E5R.Thermostat.HttpDecCopyLoop
open E5R E5R.Thermostat

theorem memory_eq (ram : Word → BitVec 8) (src dst finish : Word) (v : BitVec 8) :
    HttpDecCopyTurn.memory ram src dst finish v=ramPut ram dst v := by
  unfold HttpDecCopyTurn.memory
  change ramPut ram dst (byteOf (v.setWidth 32) 0)=_
  rw [HttpPutData.byte_word]

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠12 → r≠13 → r≠14 → d.get r=c.get r

/-- The actual five-instruction copy loop, with checked byte loads and stores.
    The unchanged-source condition is explicit and maintained after each store. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst : Word) (xs : List (BitVec 8))
    (hn : xs≠[]) (hp : c.pc=0x800043ee#32) (h13 : c.get 13=src) (h12 : c.get 12=dst)
    (h10 : c.get 10=dst+BitVec.ofNat 32 xs.length) (hs : ReadBytes.Span B img ram src xs)
    (hd : Memory.Block B dst xs.length) (hsep : WordRegions.Disjoint src xs.length dst xs.length) :
    ∃ d, Quiet.Steps B img (5*xs.length) ⟨c,ram⟩ ⟨d,ByteWrite.write ram dst xs⟩ ∧
      d.pc=0x800043fe#32 ∧ d.get 13=src+BitVec.ofNat 32 xs.length ∧
      d.get 12=dst+BitVec.ofNat 32 xs.length ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c ram src dst with
  | nil => contradiction
  | cons v vs ih =>
    have hl := hs.length
    have ht : taken .ne (dst+1#32) (dst+BitVec.ofNat 32 (v::vs).length)=(!decide (vs=[])) := by
      change decide (dst+1#32≠dst+BitVec.ofNat 32 (v::vs).length)=_
      have he : dst+1#32=dst+BitVec.ofNat 32 (v::vs).length ↔ vs=[] := by
        rw [BitVec.add_right_inj]
        constructor
        · intro h
          have hh := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl] at hh
          exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hh;omega)
        · intro h;subst vs;rfl
      simp only [ne_eq,he,decide_not]
    have hd0 : B.inRam dst 1=true := by
      simpa only [BitVec.add_zero] using Memory.block_access hd (off := 0) (width := 1) (by decide) (by simp)
    obtain ⟨a,ta,pa,a14,a12,a13,ar,ac⟩ := HttpDecCopyTurn.contract B c ram src dst _ v (decide (vs=[])) h12 h13 h10 (ReadBytes.head hs) hd0 ht hp
    rw [memory_eq] at ta
    have af : Frame c a := fun r h12 h13 h14 => ar r h14 h12 h13
    by_cases hz : vs=[]
    · subst vs
      exact ⟨a,ta,by simpa only [decide_true,ite_true] using pa,a13,a12,af,ac⟩
    · have hs' := HttpPutData.tail_source hs hsep
      have hd' : Memory.Block B (dst+1#32) vs.length := Memory.sub_block hd (List.length_pos_iff.mpr hz) (by simp only [List.length_cons];omega)
      have he : (dst+1#32)+BitVec.ofNat 32 vs.length=dst+BitVec.ofNat 32 (v::vs).length := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 vs.length]
      obtain ⟨d,td,pd,d13,d12,dr,dc⟩ := ih a (ramPut ram dst v) (src+1#32) (dst+1#32) hz
        (by simpa only [decide_eq_false hz,Bool.false_eq_true,ite_false] using pa) a13 a12
        (by rw [af 10 (by decide) (by decide) (by decide),h10,he]) hs' hd' (HttpPutData.tail_disjoint hsep)
      refine ⟨d,?_,pd,?_,d12.trans he,?_,dc.trans ac⟩
      · have tt := ta.trans td
        simpa only [ByteWrite.write,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_comm] using tt
      · rw [d13,BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 vs.length]
      · intro r h12 h13 h14;exact (dr r h12 h13 h14).trans (af r h12 h13 h14)
end E5R.Thermostat.HttpDecCopyLoop
