import Projects.thermostat.HttpParseCode
import Projects.thermostat.LiteralQuiet
namespace E5R.Thermostat.HeadVersionSites
open E5R E5R.Thermostat

def h : Literal.Site img 72#8 where
  loadPc := 0x80002e20#32
  constPc := 0x80002e24#32
  branchPc := 0x80002e28#32
  nextPc := 0x80002e2c#32
  badPc := 0x80002efc#32
  constLen := 4#32
  offset := 2#32
  branchOffset := 0xd4#32
  rd := 28
  rc := 31
  base := 6
  rd_nonzero := by decide +kernel
  rc_nonzero := by decide +kernel
  distinct := by decide +kernel
  load_aligned := by decide +kernel
  const_aligned := by decide +kernel
  branch_aligned := by decide +kernel
  bad_aligned := by decide +kernel
  load_code := hh2147495456
  const_code := hh2147495460
  branch_code := hh2147495464
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def t1 : Literal.Site img 84#8 where
  loadPc := 0x80002e4a#32
  constPc := 0x80002e4e#32
  branchPc := 0x80002e52#32
  nextPc := 0x80002e56#32
  badPc := 0x80002efa#32
  constLen := 4#32
  offset := 3#32
  branchOffset := 0xa8#32
  rd := 10
  rc := 11
  base := 6
  rd_nonzero := by decide +kernel
  rc_nonzero := by decide +kernel
  distinct := by decide +kernel
  load_aligned := by decide +kernel
  const_aligned := by decide +kernel
  branch_aligned := by decide +kernel
  bad_aligned := by decide +kernel
  load_code := hh2147495498
  const_code := hh2147495502
  branch_code := hh2147495506
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def t2 : Literal.Site img 84#8 where
  loadPc := 0x80002e5c#32
  constPc := 0x80002e60#32
  branchPc := 0x80002e64#32
  nextPc := 0x80002e68#32
  badPc := 0x80002efa#32
  constLen := 4#32
  offset := 4#32
  branchOffset := 0x96#32
  rd := 10
  rc := 11
  base := 6
  rd_nonzero := by decide +kernel
  rc_nonzero := by decide +kernel
  distinct := by decide +kernel
  load_aligned := by decide +kernel
  const_aligned := by decide +kernel
  branch_aligned := by decide +kernel
  bad_aligned := by decide +kernel
  load_code := hh2147495516
  const_code := hh2147495520
  branch_code := hh2147495524
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def p : Literal.Site img 80#8 where
  loadPc := 0x80002e6e#32
  constPc := 0x80002e72#32
  branchPc := 0x80002e76#32
  nextPc := 0x80002e7a#32
  badPc := 0x80002efa#32
  constLen := 4#32
  offset := 5#32
  branchOffset := 0x84#32
  rd := 10
  rc := 11
  base := 6
  rd_nonzero := by decide +kernel
  rc_nonzero := by decide +kernel
  distinct := by decide +kernel
  load_aligned := by decide +kernel
  const_aligned := by decide +kernel
  branch_aligned := by decide +kernel
  bad_aligned := by decide +kernel
  load_code := hh2147495534
  const_code := hh2147495538
  branch_code := hh2147495542
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel

def slash : Literal.Site img 47#8 where
  loadPc := 0x80002e80#32
  constPc := 0x80002e84#32
  branchPc := 0x80002e88#32
  nextPc := 0x80002e8c#32
  badPc := 0x80002efa#32
  constLen := 4#32
  offset := 6#32
  branchOffset := 0x72#32
  rd := 10
  rc := 11
  base := 6
  rd_nonzero := by decide +kernel
  rc_nonzero := by decide +kernel
  distinct := by decide +kernel
  load_aligned := by decide +kernel
  const_aligned := by decide +kernel
  branch_aligned := by decide +kernel
  bad_aligned := by decide +kernel
  load_code := hh2147495552
  const_code := hh2147495556
  branch_code := hh2147495560
  to_const := by decide +kernel
  to_branch := by decide +kernel
  to_next := by decide +kernel
  to_bad := by decide +kernel
end E5R.Thermostat.HeadVersionSites
