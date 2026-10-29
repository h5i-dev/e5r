import Lake
open Lake DSL

-- Lake builds only the native test tools. Proof checking runs plain `lean`
-- module by module from tools/check.py, so no stale build output is trusted.
package rv32

lean_lib Theories where
  globs := #[.submodules `Theories]

lean_lib FirmwareImage where
  roots := #[`Projects.hifive1.Image]

lean_exe replay where
  root := `tools.Replay
