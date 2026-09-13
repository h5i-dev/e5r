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
0x400144                  24       1       9  proven    .eh_frame                   -
0x400168                  14       1       5  proven    .eh_frame                   -
...
```

`strength` and `evidence` are the point. `proven` from `.eh_frame` means the
compiler emitted an unwind entry for exactly this range, which survives
stripping. `heuristic` from a prologue scan means something looked like a
function. The two fail differently, so they are never mixed into one number.

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
$ r12e sig prog apply driver.r12e-sig
```

A signature identifies a function by what it is rather than where it is. The
number that matters is recall **with zero wrong names**: a wrong name is worse
than no name, because you will believe it.

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

This writes `prog.r12e`, one assertion per line:

```
$ cat prog.r12e
r12e-log 1
name 3f0a1c2b8e7d4a19 d41d8cd98f00b204 12 0 seq=1 who=you value=parse_header
...
```

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
```

The names come back, and each one says how it was found:

```
0x400180  parse_header   shape     # the bytes changed, the shape did not
0x4001c4  read_length    exact     # this function was not touched
0x400220  emit_record    address   # only the address matched: check this one
```

`address` is the resolution that means "the code this was written against is
not there any more". It is not hidden, and nothing that writes to a binary
accepts it without being told to.

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
