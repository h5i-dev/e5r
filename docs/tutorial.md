# From a stripped binary to a committed annotation log

Forty minutes, one binary, and at the end the work is in git where a colleague
can review it and a rebuild cannot throw it away.

Everything below is a real command. The binary is whatever you have; the
transcript uses a stripped build of the repository's own fixture so the output
is reproducible.

```
$ bash scripts/build-fixtures.sh
$ cp fixtures/build/driver.a64.O2 ./prog
$ strip ./prog
```

## 1. Ask what it is before asking anything else

```
$ r12e info prog
```

Format, architecture, entry point, image base, whether it is position
independent, and what the loader noticed. This does no analysis at all, so it
is instant on a 500 MB binary.

Read the warnings. A loader that had to guess says so here, and everything
after this point rests on it.

## 2. Find the functions, and look at the evidence column

```
$ r12e funcs prog
address                 size  blocks   insns  strength  evidence                    name
0x400144                  24       1       9  inferred  direct call target          sub_400144
0x400168                  14       1       5  inferred  direct call target          sub_400168
0x40017c                  18       1       6  inferred  direct call target          sub_40017c
...
```

`strength` and `evidence` are the point, and this binary is a good example of
why. It is freestanding, so there is no `.eh_frame` and the symbol table is
gone: every one of these is `inferred`, found because something calls it.
On an ordinary dynamically linked binary you will see `proven` from
`.eh_frame`, which the compiler emits for unwinding and which survives
stripping, and `heuristic` where a prologue scan found something that merely
looked like a function. Those three fail differently, so they are never mixed
into one number.

To see what is fact and what is a scanner's opinion, run it both ways:

```
$ r12e funcs prog --no-scan | wc -l
$ r12e funcs prog | wc -l
```

The difference is the scan's contribution, and if it is large on your binary
that is worth knowing before you trust it.

## 3. Get the names back, if the code came from somewhere with names

Build a signature library from a binary that has symbols:

```
$ r12e sig fixtures/build/driver.a64.O2 create -o driver.r12e-sig
38 signature(s) written
$ r12e sig prog apply driver.r12e-sig
address              match      name                         was
0x400144             exact      arith8                       sub_400144
0x400168             exact      arith16                      sub_400168
0x40017c             exact      arith32                      sub_40017c
...
```

A signature identifies a function by what it is rather than where it is, and
`match` says how strongly. Apply the same library to builds at other
optimization levels and the column earns its place:

| build the signatures came from | applied to | exact | shape | none |
| --- | --- | --- | --- | --- |
| `driver.a64.O2` | `O3` | 35 | 0 | |
| `driver.a64.O2` | `Os` | 28 | 0 | |
| `driver.a64.O2` | `O1` | 27 | 1 | |
| `driver.a64.O2` | `O0` | 0 | 0 | all |

The one `shape` match at `-O1` is `_start`, whose bytes differ and whose
instruction shapes do not. `-O0` recovers nothing, correctly: the code really
is different, and a tool that claimed a match there would be lying to you.

The number that matters is recall **with zero wrong names**. A wrong name is
worse than no name, because you will believe it.

## 4. Read the code

```
$ r12e disas prog 0x400144
$ r12e decompile prog 0x400144
```

The C is a statement of what the machine does, in C's notation. Where the
structuring could not express the control flow without a label, a `goto`
appears and the count is printed, rather than a shape that is not there. Where
an operation has no C, a named helper appears (`__bits`, `__clobbered`,
`__condition`) and the unmodelled count is reported.

To find the function worth reading first:

```
$ r12e query prog 'functions where insns > 100 and calls > 5'
$ r12e strings prog --min 8
$ r12e xrefs prog 0x410008
```

## 5. Write down what you worked out

```
$ r12e annotate prog name 0x400144 parse_header
$ r12e annotate prog comment 0x400144 "length is little endian, unlike the rest"
$ r12e annotate prog type 0x400144 "int parse_header(const uint8_t *p, size_t n)"
```

Each one prints what it recorded:

```
0x400144 name = "parse_header"
0x400144 comment = "length is little endian, unlike the rest"
```

and writes `prog.r12e`, one assertion per line:

```
$ cat prog.r12e
r12e-annotations 1
# One assertion per line, sorted by content id. Order does not affect the
# result, so the union of two branches is the correct merge. Put this in
# .gitattributes so git does that for you:
#     *.r12e merge=union
# Do not sort or reflow by hand.
name shape=6a0730fc0e7aa36f bytes=893ddaba11934499 insns=9 abs=400144 off=0 \
  seq=0 id=0a30883f9c5dc4a3 by="you" value="parse_header"
comment shape=6a0730fc0e7aa36f bytes=893ddaba11934499 insns=9 abs=400144 off=0 \
  seq=1 id=c009f5fec3f16326 by="you" value="length is little endian, unlike the rest"
```

(Two lines here, one line in the file.)

Each line is keyed by a **content anchor**: a fingerprint of the function's
instruction shapes with branch targets excluded, an exact hash of its bytes,
and its address as a tiebreak. The first two survive a rebase and a relink.

Made a mistake:

```
$ r12e annotate prog undo
$ r12e annotate prog redo
```

Undo is a new assertion, not an edit, so the history is never rewritten.

## 6. Commit it

```
$ echo '*.r12e merge=union' >> .gitattributes
$ git add .gitattributes prog.r12e
$ git commit -m "Name the header parser and its length field"
```

That one line in `.gitattributes` is what makes two branches of annotations
merge without conflict markers. The tool prints a note if you forget it.

Now a colleague can do this:

```
$ git checkout -b theirs
... annotate different functions ...
$ git checkout main && git merge theirs
```

and get both sets of work, because the file is append-only text sorted by a
sequence number with a content hash as a deterministic tiebreak.

## 7. Prove the work survived the rebuild

This is the step the incumbents cannot do.

```
$ make -B                      # rebuild the program from changed source
$ r12e annotate ./prog list
0x400144            name     "parse_header"
0x400144            comment  "length is little endian, unlike the rest"
```

The names come back because the log is keyed by content, not by address. The
three fields at the front of each line are what did it: `shape=` is the
fingerprint that survives a rebase and a relink, `bytes=` is the exact hash for
the same-binary fast path, and `abs=` is the address, used only as a tiebreak.

Where it matters most is the case where an anchor resolves on the address
alone, because that means the code the annotation was written against is not
there any more. Nothing hides that. `r12e sig ... apply` prints the resolution
per function in its `match` column, and `r12e patch ... apply` refuses outright
unless you pass `--allow-address-only`.

## 8. Save the session

```
$ r12e project new prog -o prog.r12e-proj
$ r12e project add prog.r12e-proj --signatures driver.r12e-sig
$ git add prog.r12e-proj && git commit -m "Record the session"
```

A project names its binary by content as well as by path. Opening it against a
different build says so, rather than answering about bytes that are not there.

## What you have now

A text file in git that a colleague can review line by line, that merges, that
`git blame` works on, and that survives the next build. That is the whole
argument for this tool.
