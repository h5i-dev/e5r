You are fixing a bug in a program, but you will not see or compile its source code. The program
is a static RISC-V 64 Linux binary (rv64imafd, no compressed instructions), built from the
project below at the commit where the issue was reported. Fix the issue by producing the fixed
binary yourself.

## Your tools

Your only tools are those of the `swebin` MCP server. They work on files in your episode
directory (plain file names, no paths):
- `list_files`, `read_file` (text files only), `write_file` (.s .lean .txt .md .json .patch), `copy_file`;
- nocompiler, the binary toolkit:
  - `disasm` prints a function as structured text (blocks, loops, instructions);
  - `asm` turns structured text back into a relocatable object;
  - `link` puts that object into a binary: each function it defines replaces the function of the same name, and calls to it go to the new code;
  - also `check`, `funcs`, `symbols`, `sections`, `info`, `strings`, `stats`, `xrefs`, `decompile` (pseudo-C, for reading only; nothing compiles it), `diff`, `refine`, `emulate`;
- `run_tests` runs the project's existing tests (the PASS_TO_PASS tests) against your binary under qemu. The tests that check this issue are hidden, as in SWE-bench;
- `submit` submits your binary and ends the episode. This happens once: the hidden tests and the existing tests run, and the reward is final.

## Rules

- Change the binary only through these tools. There is no compiler, no shell and no interpreter, and none is needed.
- Keep the fix small. Change the functions the issue is about, and keep everything else as it is.
- The reward is 1 if every hidden test of the issue passes and every existing test still passes, and 0 otherwise. A proof bonus exists in the environment (a Lean proof that your unchanged functions refine the original), but `check_proof` is not available in this run: ignore it.
- You have 90 minutes. When the time is up, whatever binary is in place is submitted for you.

Start with `list_files` and `read_file ISSUE.md`. The issue follows.

## The issue

{ISSUE}
