import Projects.thermostat.EqualLiteral
import Projects.thermostat.LetterBranch
import Projects.thermostat.LiteralCheck
import Projects.thermostat.WireSpec
namespace E5R.Thermostat.RelaySites
open E5R E5R.Thermostat

def on0 : Literal.Site img 111#8 where
  loadPc := 0x800021bc#32
  constPc := 0x800021c0#32
  branchPc := 0x800021c4#32
  nextPc := 0x800021c8#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 0#32
  branchOffset := 0x46#32
  rd := 13
  rc := 14
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492284
  const_code := wd2147492288
  branch_code := wd2147492292
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def on1 : Literal.Site img 110#8 where
  loadPc := 0x800021c8#32
  constPc := 0x800021cc#32
  branchPc := 0x800021d0#32
  nextPc := 0x800021d4#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0x3a#32
  rd := 13
  rc := 14
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492296
  const_code := wd2147492300
  branch_code := wd2147492304
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def off0 : Literal.Site img 111#8 where
  loadPc := 0x800021de#32
  constPc := 0x800021e2#32
  branchPc := 0x800021e6#32
  nextPc := 0x800021ea#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 0#32
  branchOffset := 0x24#32
  rd := 13
  rc := 14
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492318
  const_code := wd2147492322
  branch_code := wd2147492326
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def off1 : Literal.Site img 102#8 where
  loadPc := 0x800021ea#32
  constPc := 0x800021ee#32
  branchPc := 0x800021f2#32
  nextPc := 0x800021f6#32
  badPc := 0x8000220a#32
  constLen := 4#32
  offset := 1#32
  branchOffset := 0x18#32
  rd := 13
  rc := 14
  base := 8
  rd_nonzero := by decide
  rc_nonzero := by decide
  distinct := by decide
  load_aligned := by decide
  const_aligned := by decide
  branch_aligned := by decide
  bad_aligned := by decide
  load_code := wd2147492330
  const_code := wd2147492334
  branch_code := wd2147492338
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

theorem on_prefix : Literal.Chain img 13 14 8 0x800021c8#32 0x8000220a#32 0 0x800021bc#32 [111#8] := by
  exact .cons on0 rfl rfl rfl rfl rfl (.nil 1)
end E5R.Thermostat.RelaySites
