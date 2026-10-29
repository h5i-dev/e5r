import Lake
open Lake DSL

-- Lake builds only the native test tools. Proof checking runs plain `lean`
-- module by module from tools/check.py, so no stale build output is trusted.
package rv32

lean_lib Theories where
  globs := #[.submodules `Theories]

lean_lib FirmwareImage where
  roots := #[`Projects.hifive1.Image, `Projects.hifive1.Config]

lean_exe replay where
  root := `tools.Replay

lean_exe analyze_firmware where
  root := `tools.AnalyzeFirmware

lean_lib Tools where
  roots := #[`tools.Analyze, `tools.RingDraft, `tools.ReplayLib]

lean_exe replay_isa where
  root := `tools.ReplayIsa

lean_exe trace_guard where
  root := `tools.TraceGuard
