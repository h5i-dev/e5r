import Projects.thermostat.EqualLiteral
import Projects.thermostat.LetterBranch
import Projects.thermostat.LiteralCheck
import Projects.thermostat.WireSpec
namespace E5R.Thermostat.BodySites
open E5R E5R.Thermostat

def path_slash : Literal.Site img 47#8 where
  loadPc := 0x800020ae#32
  constPc := 0x800020b2#32
  branchPc := 0x800020b6#32
  nextPc := 0x800020ba#32
  badPc := 0x80002194#32
  constLen := 4#32
  offset := 0#32
  branchOffset := 0xde#32
  rd := 12
  rc := 13
  base := 11
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492014
  const_code := wd2147492018
  branch_code := wd2147492022
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def path_mode : Literal.EqualSite img 109#8 where
  loadPc := 0x800020ba#32
  constPc := 0x800020be#32
  branchPc := 0x800020c2#32
  equalPc := 0x80002136#32
  otherPc := 0x800020c6#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0x74#32
  rd := 12
  rc := 13
  base := 11
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  equal_aligned := by decide
  load_code := wd2147492026
  const_code := wd2147492030
  branch_code := wd2147492034
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_other := by decide +kernel
  to_equal := by decide +kernel

def auto_first : Literal.EqualSite img 97#8 where
  loadPc := 0x8000221c#32
  constPc := 0x80002220#32
  branchPc := 0x80002224#32
  equalPc := 0x8000225c#32
  otherPc := 0x80002228#32
  constLen := 4#32
  offset := 0#32
  branchOffset := 0x38#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  equal_aligned := by decide
  load_code := wd2147492380
  const_code := wd2147492384
  branch_code := wd2147492388
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_other := by decide +kernel
  to_equal := by decide +kernel

def off0 : Literal.Site img 111#8 where
  loadPc := 0x8000216e#32
  constPc := 0x80002172#32
  branchPc := 0x80002176#32
  nextPc := 0x8000217a#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 0#32
  branchOffset := 0x94#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492206
  const_code := wd2147492210
  branch_code := wd2147492214
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def off1 : Literal.Site img 102#8 where
  loadPc := 0x8000217a#32
  constPc := 0x8000217e#32
  branchPc := 0x80002182#32
  nextPc := 0x80002186#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0x88#32
  rd := 13
  rc := 12
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492218
  const_code := wd2147492222
  branch_code := wd2147492226
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def heat0 : Literal.Site img 101#8 where
  loadPc := 0x80002230#32
  constPc := 0x80002234#32
  branchPc := 0x80002238#32
  nextPc := 0x8000223c#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0xffffffd2#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492400
  const_code := wd2147492404
  branch_code := wd2147492408
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def heat1 : Literal.Site img 97#8 where
  loadPc := 0x8000223c#32
  constPc := 0x80002240#32
  branchPc := 0x80002244#32
  nextPc := 0x80002248#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 2#32
  branchOffset := 0xffffffc6#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492412
  const_code := wd2147492416
  branch_code := wd2147492420
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def heat2 : Literal.Site img 116#8 where
  loadPc := 0x80002248#32
  constPc := 0x8000224c#32
  branchPc := 0x80002250#32
  nextPc := 0x80002254#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 3#32
  branchOffset := 0xffffffba#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492424
  const_code := wd2147492428
  branch_code := wd2147492432
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

theorem heat_prefix : Literal.Chain img 12 13 8 0x80002248#32 0x8000220a#32 1 0x80002230#32 (WireSpec.ascii "ea") := by
  exact .cons heat0 rfl rfl rfl rfl rfl (.cons heat1 rfl rfl rfl rfl rfl (.nil 3))

def auto0 : Literal.Site img 117#8 where
  loadPc := 0x8000225c#32
  constPc := 0x80002260#32
  branchPc := 0x80002264#32
  nextPc := 0x80002268#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0xffffffa6#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492444
  const_code := wd2147492448
  branch_code := wd2147492452
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def auto1 : Literal.Site img 116#8 where
  loadPc := 0x80002268#32
  constPc := 0x8000226c#32
  branchPc := 0x80002270#32
  nextPc := 0x80002274#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 2#32
  branchOffset := 0xffffff9a#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492456
  const_code := wd2147492460
  branch_code := wd2147492464
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def auto2 : Literal.Site img 111#8 where
  loadPc := 0x80002274#32
  constPc := 0x80002278#32
  branchPc := 0x8000227c#32
  nextPc := 0x80002280#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 3#32
  branchOffset := 0xffffff8e#32
  rd := 12
  rc := 13
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492468
  const_code := wd2147492472
  branch_code := wd2147492476
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

theorem auto_prefix : Literal.Chain img 12 13 8 0x80002274#32 0x8000220a#32 1 0x8000225c#32 (WireSpec.ascii "ut") := by
  exact .cons auto0 rfl rfl rfl rfl rfl (.cons auto1 rfl rfl rfl rfl rfl (.nil 3))

def path_temp : LetterBranch.Site 116#8 where
  pc := 0x800020c6#32
  pass := 0x800020ce#32
  fail := 0x80002194#32
  offset := 0xca#32
  aligned := by decide
  branch_aligned := by decide
  fail_aligned := by decide
  constant := wd2147492038
  branch := wd2147492042
  to_pass := by decide +kernel
  to_fail := by decide +kernel

def mode_heat : LetterBranch.Site 104#8 where
  pc := 0x80002228#32
  pass := 0x80002230#32
  fail := 0x8000220a#32
  offset := 0xffffffde#32
  aligned := by decide
  branch_aligned := by decide
  fail_aligned := by decide
  constant := wd2147492392
  branch := wd2147492396
  to_pass := by decide +kernel
  to_fail := by decide +kernel
end E5R.Thermostat.BodySites
