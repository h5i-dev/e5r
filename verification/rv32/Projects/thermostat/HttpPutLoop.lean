import Projects.thermostat.HttpPutData
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.HttpPutLoop
open E5R E5R.Thermostat

def Frame (c d : Core) : Prop := ∀ r : Reg, r≠5 → r≠13 → r≠15 → r≠17 → d.get r=c.get r

/-- The actual checked byte-copy loop. The destination is disjoint from the
    source, including a ROM source view, and capacity bounds exclude panic. -/
theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (src dst cap : Word)
    (pos : Nat) (xs : List (BitVec 8)) (hne : xs≠[])
    (hc : pos+xs.length≤cap.toNat)
    (hp : c.pc=0x8000414e#32) (h10 : c.get 10=dst) (h11 : c.get 11=cap)
    (h13 : c.get 13=src) (h15 : c.get 15=BitVec.ofNat 32 pos)
    (h16 : c.get 16=src+BitVec.ofNat 32 xs.length)
    (hs : ReadBytes.Span B img ram src xs)
    (hd : Memory.Block B (dst+BitVec.ofNat 32 pos) xs.length)
    (hsep : WordRegions.Disjoint src xs.length (dst+BitVec.ofNat 32 pos) xs.length) :
    ∃ d, Quiet.Steps B img (7*xs.length) ⟨c,ram⟩ ⟨d,ByteWrite.write ram (dst+BitVec.ofNat 32 pos) xs⟩ ∧
      d.pc=0x80004166#32 ∧ d.get 13=src+BitVec.ofNat 32 xs.length ∧
      d.get 15=BitVec.ofNat 32 (pos+xs.length) ∧ Frame c d ∧ d.sameCsr c := by
  induction xs generalizing c ram src pos with
  | nil => contradiction
  | cons v vs ih =>
    have hl : (v::vs).length<2^32 := hs.length
    have hc32 := cap.isLt
    have hpos : pos<2^32 := by simp only [List.length_cons] at hc;omega
    have hcap : cap≠BitVec.ofNat 32 pos := by
      intro h
      have hh := congrArg BitVec.toNat h
      rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hpos] at hh
      simp only [List.length_cons] at hc;omega
    have ht : taken .ne (src+1#32) (src+BitVec.ofNat 32 (v::vs).length)=(!decide (vs=[])) := by
      change decide (src+1#32≠src+BitVec.ofNat 32 (v::vs).length)=_
      have he : src+1#32=src+BitVec.ofNat 32 (v::vs).length ↔ vs=[] := by
        rw [BitVec.add_right_inj]
        constructor
        · intro h
          have hh := congrArg BitVec.toNat h
          simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt hl] at hh
          exact List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hh;omega)
        · intro h;subst vs;rfl
      simp only [ne_eq,he,decide_not]
    have hd0 : B.inRam (dst+BitVec.ofNat 32 pos) 1=true := by
      simpa only [BitVec.add_zero] using Memory.block_access hd (off := 0) (width := 1) (by decide) (by simp)
    obtain ⟨a,ta,pa,a17,a5,a13,a15,ar,ac⟩ := HttpPutTurn.contract B c ram src dst (BitVec.ofNat 32 pos) cap
      (src+BitVec.ofNat 32 (v::vs).length) v (decide (vs=[])) h10 h11 h13 h15 h16 hcap (ReadBytes.head hs) hd0 ht hp
    rw [HttpPutData.memory] at ta
    have af : Frame c a := fun r h5 h13 h15 h17 => ar r h17 h5 h13 h15
    by_cases hz : vs=[]
    · subst vs
      refine ⟨a,ta,by simpa only [decide_true,ite_true] using pa,a13,?_,af,ac⟩
      simpa only [List.length_cons,List.length_nil,HttpPutData.next_pos] using a15
    · have hs' := HttpPutData.tail_source hs hsep
      have he : (src+1#32)+BitVec.ofNat 32 vs.length=src+BitVec.ofNat 32 (v::vs).length := by
        rw [BitVec.add_assoc,←BitVec.ofNat_add,List.length_cons,Nat.add_comm 1 vs.length]
      have hd' : Memory.Block B (dst+BitVec.ofNat 32 (pos+1)) vs.length := by
        rw [←HttpPutData.next_dst dst pos]
        exact Memory.sub_block hd (List.length_pos_iff.mpr hz) (by simp only [List.length_cons];omega)
      have hsep' : WordRegions.Disjoint (src+1#32) vs.length (dst+BitVec.ofNat 32 (pos+1)) vs.length := by
        rw [←HttpPutData.next_dst dst pos]
        exact HttpPutData.tail_disjoint hsep
      obtain ⟨d,td,pd,d13,d15,dr,dc⟩ := ih a (ramPut ram (dst+BitVec.ofNat 32 pos) v) (src+1#32) (pos+1) hz
        (by simp only [List.length_cons] at hc;omega)
        (by simpa only [decide_eq_false hz,Bool.false_eq_true,ite_false] using pa)
        ((af 10 (by decide) (by decide) (by decide) (by decide)).trans h10)
        ((af 11 (by decide) (by decide) (by decide) (by decide)).trans h11) a13
        (by rw [HttpPutData.next_pos] at a15;exact a15)
        (by rw [af 16 (by decide) (by decide) (by decide) (by decide),h16,he]) hs' hd' hsep'
      refine ⟨d,?_,pd,d13.trans he,?_,?_,dc.trans ac⟩
      · have tt := ta.trans td
        simpa only [ByteWrite.write,HttpPutData.next_dst,List.length_cons,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tt
      · simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using d15
      · intro r h5 h13 h15 h17
        exact (dr r h5 h13 h15 h17).trans (af r h5 h13 h15 h17)
end E5R.Thermostat.HttpPutLoop
