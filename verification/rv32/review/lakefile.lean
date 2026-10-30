import Lake
open Lake DSL

-- Review-owned native tools. The rv32 package is a path dependency so this
-- does not touch verification/rv32/lakefile.lean.
package review

require rv32 from ".."

lean_exe fwreplay where
  root := `FwReplay

lean_exe diff where
  root := `Diff

lean_exe decodesweep where
  root := `DecodeSweep
