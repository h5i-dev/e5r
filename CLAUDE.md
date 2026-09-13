# CLAUDE.md

Scope, milestones and the list of things this project will not build live in
[`ROADMAP.md`](ROADMAP.md). Read that first.

## This checkout is release-only

The machine this repository is developed on has 7.5 GB of RAM and the workspace
will grow a SLEIGH compiler, several decoders and a decompiler. A dev-profile
build of that is large enough to be a problem here, and the release build is
already warm, so a debug build is also the slower path.

Whether a dev build is affordable is a fact about the machine, not about the
project, so the guards are opt-in and gitignored rather than committed settings:

1. `scripts/no-debug-guard.sh on` parks a regular file at `target/debug`, so
   cargo stops with "failed to create directory ... File exists" before it
   compiles anything. `off` and `status` do what they say. It works against every
   tool, not just Claude Code. The file is under `target/`, which is ignored.
2. `scripts/deny-debug-build.py` is a PreToolUse hook that refuses dev-profile
   cargo commands, target-directory redirection, and attempts to remove the
   guard. Wire it up in `.claude/settings.local.json`:

   ```json
   { "hooks": { "PreToolUse": [ { "matcher": "Bash", "hooks": [
     { "type": "command",
       "command": "python3 \"$CLAUDE_PROJECT_DIR/scripts/deny-debug-build.py\"" } ] } ] } }
   ```

Both are on in this checkout. Every cargo invocation takes `--release` and the
binary is `./target/release/r12e`. Do not work around a "File exists" failure on
`target/debug`: build release, or turn the guard off deliberately, which is the
owner's call.

CI runs on disposable runners, so the workflow builds dev profile on purpose. Do
not add `--release` there.
