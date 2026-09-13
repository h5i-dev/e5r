# r12e

Reverse engineering from the command line. Load a binary, recover its
functions, disassemble them, decompile them, and ask questions about what is
there.

Every command takes `--json` and prints the same information in a form a
script can read. Exit codes are `0` for success, `1` for nothing found, `2` for
a bad command line, and `3` for input that could not be read.

```
cargo build --release
./target/release/r12e info /bin/ls
```

## What it will and will not tell you

Every recovered fact carries the evidence for it, and the strength of that
evidence is printed next to it:

| Strength | Meaning |
| --- | --- |
| `asserted` | A person or an agent wrote it in the annotation log. |
| `proven` | The file says so: a symbol table, debug information, an entry point, an unwind record. |
| `inferred` | Something in the code implies it: a call target, a jump table, an import thunk. |
| `heuristic` | A pattern suggests it: a prologue, a linear sweep, a pointer in data. |

Where a thing cannot be worked out, it is reported as unknown rather than
guessed at. A function whose control flow could not be followed to the end is
marked incomplete; a jump table whose bound could not be established is left
unresolved; an instruction the lifter does not model appears as unmodelled in
the output rather than being approximated.

## Looking at a file

```
r12e info FILE           container, architecture, entry, what the loader noticed
r12e sections FILE       sections and where they are mapped
r12e symbols FILE        symbols the container names
r12e imports FILE        what it needs from elsewhere
r12e exports FILE        what it offers
r12e strings FILE        strings found in the image, by section
r12e stats FILE          counts: functions, blocks, instructions, references
```

`info` and the listings above need only the container, so they are instant
whatever the size of the file.

## Code

```
r12e funcs FILE                     every recovered function and its evidence
r12e disas FILE TARGET              disassemble a function, an address, or `all`
r12e xrefs FILE TARGET [--from]     references to an address, or from one
r12e decompile FILE TARGET          pseudo-C for a function, or for `all`
r12e emulate FILE TARGET [ARGS...]  run a function and report what it did
```

`TARGET` is an address (`0x401000`, `401000`), a symbol name, or `all`.

The decompiler's output says what the machine does in C's notation. It does
not claim to be the source. Where the control flow does not fit an `if` or a
`while`, a labelled `goto` appears rather than a shape that is not there, and
the number of them is printed above the function: that is the honest measure
of how well the structuring worked. Where the binary carries debug
information, parameters are named and typed as the compiler recorded them;
where it does not, they are recovered from what the code does with them.

`emulate` runs the function in the same interpreter the lifters are tested
against. Nothing escapes the process: memory is a copy of the image, a system
call stops the run, and a budget bounds it.

## Structure and types

```
r12e shapes FILE TARGET     what the pointers a function takes point at
r12e vtables FILE           virtual tables and the classes they belong to
```

`shapes` reports the offsets a function touches through each pointer it is
given, and the element size when it walks an array of them. It reports what it
saw rather than a conclusion: it does not name fields and it does not average
two disagreeing strides into one.

## Asking questions

```
r12e query FILE 'functions where insns > 100 and name ~ "crypt"'
r12e query FILE 'strings where length >= 20 and text ~ "/etc/"'
r12e query FILE 'xrefs where kind = call and to = 0x401000 limit 20'
```

Entities: `functions`, `strings`, `symbols`, `imports`, `exports`, `sections`,
`xrefs`. Operators: `=` `!=` `<` `<=` `>` `>=`, `~` for contains and `!~` for
does not, combined with `and`, `or`, `not` and brackets. Numbers may be
decimal or hexadecimal. A field that does not exist is a mistake in the query
and is reported as one, with the fields there are.

## Comparing builds

```
r12e diff OLD NEW [--all]
```

Functions are matched across the two builds by a fingerprint of their
instruction shape rather than by address, so the match survives a relink.
Matched, changed, added and removed are reported with a similarity score.
Given a vulnerable build and a patched one, this points at the change.

## Naming a stripped binary

```
r12e sig FILE create -o LIBRARY      a signature for every named function
r12e sig FILE apply LIBRARY          name what the library recognizes
```

A signature identifies a function by its content rather than its address, so a
library built from a binary with symbols names the same code in one without
them. It refuses every coin flip: two signatures that disagree about a hash
name nothing, a short function is not identified by shape alone, and import
thunks are excluded because they differ only in an offset.

The file is sorted text, so a signature library reviews in a diff.

## Annotations

```
r12e annotate FILE name TARGET NAME
r12e annotate FILE comment TARGET TEXT
r12e annotate FILE list
r12e annotate FILE undo
```

Annotations are written to a log beside the binary, keyed to a content anchor
rather than an address, so the work survives a rebuild. The log is text sorted
by that anchor, so two analysts on separate branches merge without conflict
markers. Add this to `.gitattributes`:

```
*.r12e merge=union
```

## Driving it from a program

Every command takes `--json`. The schema is named in every document
(`"schema": "r12e/1"`) and addresses are hex strings so nothing is lost to a
float.

```
r12e mcp
```

speaks the Model Context Protocol on stdin and stdout, so an agent can open a
file, look at it, and write annotations without a shell.

## Shell integration

```
r12e completions bash > /etc/bash_completion.d/r12e
r12e completions zsh  > ~/.zsh/completions/_r12e
r12e completions fish > ~/.config/fish/completions/r12e.fish
r12e manpage          > /usr/local/share/man/man1/r12e.1
```

Both are generated from the command tree, so they cannot describe a command
that does not exist.

## Common options

| Option | Effect |
| --- | --- |
| `--json` | Print the same information as JSON. |
| `--base ADDR` | Load a raw image, or rebase a relocatable one, at an address. |
| `--arch NAME` | The architecture of a raw image, which has no header to say. |
| `--threads N` | How much of the analysis to run in parallel. The output does not depend on this. |

## What is not built yet

ARM32 and SLEIGH languages, PDB for Windows binaries, Go and Objective-C
metadata, patch sets, and an interactive session. `ROADMAP.md` is the list, and
it says what each milestone is and what it is measured by.
