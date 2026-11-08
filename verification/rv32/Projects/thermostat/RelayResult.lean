import Projects.thermostat.RelayGuard
import Projects.thermostat.RelayDecodeBody
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000
namespace E5R.Thermostat.RelayResult
open E5R E5R.Thermostat

def decoded (v : Option Word) (xs : List (BitVec 8)) : Except Nat Spec.Command :=
  match v with
  | none => .error 404
  | some idx => if idx.toNat < 256 then RelaySpec.body idx xs else .error 404

theorem as_relay (first : Option (List (BitVec 8))) (xs : List (BitVec 8)) :
    decoded (first.bind WireSpec.parseU32) xs = WireSpec.relay first xs := by rfl

theorem contract (B : Board) (c : Core) (ram : Word → BitVec 8) (p : Word) (xs : List (BitVec 8)) (v : Option Word)
    (hs : Bytes.Span B ram p xs) (hp : c.pc = 0x8000219e#32)
    (h8 : c.get 8 = p) (h9 : c.get 9 = BitVec.ofNat 32 xs.length) (h : ParamReturn.Result c v) :
    ∃ d n, n ≤ 26 ∧ DetSteps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc = 0x80002212#32 ∧
      WireSpec.ResultWord (d.get 10) (decoded v xs) ∧
      (∀ r : Reg, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 15 → d.get r = c.get r) ∧ d.sameCsr c := by
  obtain ⟨c1,t1,pc1,tag1,flag1,regs1,csr1⟩ := RelayGuard.contract B c ram v hp h
  have h8' : c1.get 8 = p := (regs1 8 (by decide) (by decide)).trans h8
  have h9' : c1.get 9 = BitVec.ofNat 32 xs.length := (regs1 9 (by decide) (by decide)).trans h9
  cases v with
  | none =>
    have pc1' : c1.pc = 0x800021d8#32 := by simpa only [RelayGuard.valid,Bool.false_eq_true,ite_false] using pc1
    have flag1' : c1.get 12 = 0#32 := by simpa only [RelayGuard.valid,Bool.false_eq_true,ite_false] using flag1
    obtain ⟨d,td,pcd,vd,rd,cd⟩ := RelayFinish.notfound B c1 ram pc1' tag1 flag1'
    refine ⟨d,9,by omega,t1.trans td,pcd,vd,?_,cd.trans csr1⟩
    intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3,regs1 r h1 h3]
  | some idx =>
    by_cases hi : idx.toNat < 256
    · have pc1' : c1.pc = 0x800021aa#32 := by simpa only [RelayGuard.valid,decide_eq_true hi,ite_true] using pc1
      have h11 : c1.get 11 = idx := (regs1 11 (by decide) (by decide)).trans h.2
      obtain ⟨d,n,hn,td,pcd,vd,rd,cd⟩ := RelayDecodeBody.contract B c1 ram p idx xs hs hi pc1' h8' h9' h11 tag1
      refine ⟨d,4+n,by omega,t1.trans td,pcd,by simpa only [decoded,ite_eq_left hi] using vd,?_,cd.trans csr1⟩
      intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3 h4 h5 h6,regs1 r h1 h3]
    · have pc1' : c1.pc = 0x800021d8#32 := by simpa only [RelayGuard.valid,decide_eq_false hi,Bool.false_eq_true,ite_false] using pc1
      have flag1' : c1.get 12 = 0#32 := by simpa only [RelayGuard.valid,decide_eq_false hi,Bool.false_eq_true,ite_false] using flag1
      obtain ⟨d,td,pcd,vd,rd,cd⟩ := RelayFinish.notfound B c1 ram pc1' tag1 flag1'
      refine ⟨d,9,by omega,t1.trans td,pcd,by simpa only [decoded,ite_eq_right hi] using vd,?_,cd.trans csr1⟩
      intro r h1 h2 h3 h4 h5 h6;rw [rd r h1 h2 h3,regs1 r h1 h3]
end E5R.Thermostat.RelayResult
