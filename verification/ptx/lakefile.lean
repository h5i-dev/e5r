import Lake
open Lake DSL

-- Core Lean only: no `require`, so nothing is fetched (docs/verification-ptx.md).
package ptx

@[default_target]
lean_lib Ptx where
  globs := #[.andSubmodules `Ptx]
