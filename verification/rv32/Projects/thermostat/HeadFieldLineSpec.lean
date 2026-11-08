import Projects.thermostat.HeadHeaderLineView
namespace E5R.Thermostat.HeadFieldLineSpec
open E5R E5R.Thermostat HttpRequestSpec

/-- One actual header-loop iteration, stopping before classify/add_header or
    the already identified More/Bad/empty-line completion blocks. -/
inductive Next where
  | more
  | bad (status : Nat)
  | done (len : Nat)
  | header (lineEnd : Nat) (parsed : HdrLine)
  deriving DecidableEq, Repr

def next (g : Nat → Nat) (i cap : Nat) : Next :=
  let j := lineEnd g i cap
  let term := lineTerm g j cap
  if term=1 then .more else if term=2 then .bad 400 else if j=i then .done (j+2)
  else .header j (headerLine g i j)

def At (c : Core) (ram : Word → BitVec 8) (sp : Word) (start : Nat) : Next → Prop
  | .more => c.pc=0x800033ea#32
  | .bad status => c.pc=0x8000342c#32 ∧ c.get 1=BitVec.ofNat 32 status
  | .done len => c.pc=0x80003456#32 ∧ c.get 24=BitVec.ofNat 32 (len-2)
  | .header le parsed => HeadHeaderLineView.At c ram sp (sp+516#32) start le parsed ∧
      c.get 11=BitVec.ofNat 32 le ∧ c.get 21=BitVec.ofNat 32 (le-start) ∧
      c.get 24=BitVec.ofNat 32 start ∧ c.get 26=BitVec.ofNat 32 le

theorem term_cases (g : Nat → Nat) (j cap : Nat) : lineTerm g j cap=0 ∨ lineTerm g j cap=1 ∨ lineTerm g j cap=2 := by
  unfold lineTerm
  repeat' split <;> simp_all
end E5R.Thermostat.HeadFieldLineSpec
