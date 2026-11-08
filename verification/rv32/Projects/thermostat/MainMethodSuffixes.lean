import Projects.thermostat.MainMethodChains
import Projects.thermostat.MainMethodSelections
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace E5R.Thermostat.MainMethodSuffixes
open E5R E5R.Thermostat

theorem head (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80000d86#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<4 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<4 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤14 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 1).toNat=69 ∧ (bytes 2).toNat=65 ∧ (bytes 3).toNat=68 then 1#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 4 3 68 1 [(1,69),(2,65)] 0x80000d86#32 0x80000d9e#32
      MainMethodChains.head (by simp) (by decide) (by decide) memory data (MainMethodSelections.head B ram) c hp h15 h14

theorem post (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x8000111e#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<4 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<4 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤14 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 1).toNat=79 ∧ (bytes 2).toNat=83 ∧ (bytes 3).toNat=84 then 2#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 4 3 84 2 [(1,79),(2,83)] 0x8000111e#32 0x80001136#32
      MainMethodChains.post (by simp) (by decide) (by decide) memory data (MainMethodSelections.post B ram) c hp h15 h14

theorem patch (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80000e1a#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<5 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<5 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤20 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 0).toNat=80 ∧ (bytes 1).toNat=65 ∧ (bytes 2).toNat=84 ∧ (bytes 3).toNat=67 ∧ (bytes 4).toNat=72 then 4#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 5 4 72 4 [(0,80),(1,65),(2,84),(3,67)] 0x80000e1a#32 0x80000e4a#32
      MainMethodChains.patch (by simp) (by decide) (by decide) memory data (MainMethodSelections.patch B ram) c hp h15 h14

theorem delete (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80000db0#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<6 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<6 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤23 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 0).toNat=68 ∧ (bytes 1).toNat=69 ∧ (bytes 2).toNat=76 ∧ (bytes 3).toNat=69 ∧ (bytes 4).toNat=84 ∧ (bytes 5).toNat=69 then 5#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 6 5 69 5 [(0,68),(1,69),(2,76),(3,69),(4,84)] 0x80000db0#32 0x80000dec#32
      MainMethodChains.delete (by simp) (by decide) (by decide) memory data (MainMethodSelections.delete B ram) c hp h15 h14

theorem get (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80000e0a#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<3 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<3 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 1).toNat=69 ∧ (bytes 2).toNat=84 then 0#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 3 2 84 0 [(1,69)] 0x80000e0a#32 0x80000e16#32
      MainMethodChains.get (by simp) (by decide) (by decide) memory data (MainMethodSelections.get B ram) c hp h15 h14

theorem put (B : Board) (c : Core) (ram : Word → BitVec 8) (base : Word) (bytes : Nat → BitVec 8)
    (hp : c.pc=0x80001140#32) (h15 : c.get 15=base) (h14 : c.get 14=6#32)
    (memory : ∀ k, k<3 → B.inRam (base+BitVec.ofNat 32 k) 1=true)
    (data : ∀ k, k<3 → ram (base+BitVec.ofNat 32 k)=bytes k) :
    ∃ n d, n≤11 ∧ Quiet.Steps B img n ⟨c,ram⟩ ⟨d,ram⟩ ∧ d.pc=0x80001160#32 ∧
      d.get 14=(if (bytes 1).toNat=85 ∧ (bytes 2).toNat=84 then 3#32 else 6#32) ∧ MainMethodSuffix.Frame c d ∧ d.sameCsr c := by
  simpa only [MainMethodChain.accepts,List.length_cons,List.length_nil,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
    MainMethodSuffix.contract B ram base bytes 3 2 84 3 [(1,85)] 0x80001140#32 0x8000114c#32
      MainMethodChains.put (by simp) (by decide) (by decide) memory data (MainMethodSelections.put B ram) c hp h15 h14
end E5R.Thermostat.MainMethodSuffixes
