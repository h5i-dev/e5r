#!/usr/bin/env python3
"""Proof sizes for examples/demo/README.md: lines and tokens, without blank lines and
comments.

    python3 -I examples/demo/tools/count.py [--markdown]

Per function and side (lean/Demo/<F><A|B>.lean):
  invariants  the `loop_inv ... measure ...` blocks of the nocompiler_auto call
  script      everything else in the file's theorems (intro, the call, the
              verification conditions)
  lemmas      other declarations in the file (per-function lemmas)
Shared, counted once (lean/Demo/<F>Spec.lean): the specification and the
lemmas about it. Libraries: the core (lean/NoCompiler without Auto.lean and Ext/),
NoCompiler/Auto.lean, NoCompiler/Ext/Rvc.lean, NoCompiler/Vocab/."""
import os, re, sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
LEAN = os.path.join(ROOT, "lean")
TOKEN = re.compile(r"[A-Za-z_À-￿][A-Za-z0-9_'.!?À-￿]*|\d[\dA-Fa-fx#]*|«[^»]*»|[^\sA-Za-z0-9_]")


def code_lines(text):
    """Lines without comments (`--`, `/- -/`, `/-- -/`) and blank lines."""
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    out = []
    for l in text.split("\n"):
        l = re.sub(r"--.*", "", l).rstrip()
        if l.strip():
            out.append(l)
    return out


def tokens(lines):
    return sum(len(TOKEN.findall(l)) for l in lines)


def split_proof(path):
    lines = code_lines(open(path).read())
    inv, script, lemmas = [], [], []
    mode = None
    for l in lines:
        s = l.lstrip()
        indent = len(l) - len(s)
        if indent == 0:
            if s.startswith("theorem") and ("VerifiedImg" in s or "VerifiedC" in s):
                mode = "thm"; script.append(l); continue
            if s.startswith(("import", "namespace", "open", "end ", "set_option")):
                mode = None; continue
            mode = "lemma"; lemmas.append(l); continue
        if mode == "thm":
            if s.startswith("loop_inv"):
                mode = "inv"; inv.append(l); continue
            script.append(l)
        elif mode == "inv":
            if indent >= 4 and not s.startswith("nocompiler_auto"):
                inv.append(l)
            else:
                mode = "thm"; script.append(l)
        elif mode == "lemma":
            lemmas.append(l)
    return inv, script, lemmas


def count_file(path):
    ls = code_lines(open(path).read())
    return len(ls), tokens(ls)


def main():
    md = "--markdown" in sys.argv
    rows = []
    for f in ["Sum", "Sum2", "Cobs"]:
        for side in ["B", "A"]:
            p = os.path.join(LEAN, "Demo", f"{f}{side}.lean")
            if not os.path.exists(p):
                continue
            inv, script, lemmas = split_proof(p)
            rows.append((f, side, len(inv), tokens(inv), len(script), tokens(script),
                         len(lemmas), tokens(lemmas)))
    shared = []
    for f in ["Sum", "Cobs"]:
        text = open(os.path.join(LEAN, "Demo", f"{f}Spec.lean")).read()
        k = text.index("/-! ## Facts") if "/-! ## Facts" in text else text.index("/-! Facts")
        a, b = code_lines(text[:k]), code_lines(text[k:])
        shared.append((f"{f}Spec.lean: specification", len(a), tokens(a)))
        shared.append((f"{f}Spec.lean: lemmas about it", len(b), tokens(b)))
    core = [os.path.join(dp, n) for dp, _, ns in os.walk(os.path.join(LEAN, "NoCompiler")) for n in ns
            if n.endswith(".lean") and "Ext" not in dp and "Vocab" not in dp
            and n not in ("Auto.lean", "Vocab.lean")]
    vocab = [os.path.join(LEAN, "NoCompiler", "Vocab", n)
             for n in sorted(os.listdir(os.path.join(LEAN, "NoCompiler", "Vocab")))]
    libs = [("core lean/NoCompiler (without Auto.lean, Ext/, Vocab/)", core),
            ("lean/NoCompiler/Vocab/ (spec vocabulary: lists, folds, words, memory)", vocab),
            ("lean/NoCompiler/Auto.lean (nocompiler_auto, shared normal form)", [os.path.join(LEAN, "NoCompiler", "Auto.lean")]),
            ("lean/NoCompiler/Ext/Rvc.lean (RVC extension, nocompiler_auto_c)", [os.path.join(LEAN, "NoCompiler", "Ext", "Rvc.lean")])]
    if md:
        print("| function | side | invariants + measures | script | per-function lemmas | total |")
        print("| --- | --- | --- | --- | --- | --- |")
        for f, side, il, it, sl, st, ll, lt in rows:
            print(f"| {f} | {side} | {il} lines, {it} tokens | {sl} lines, {st} tokens | "
                  f"{ll} lines, {lt} tokens | {il + sl + ll} lines, {it + st + lt} tokens |")
        print()
        print("| shared (counted once) | lines | tokens |\n| --- | --- | --- |")
        for f, n, t in shared:
            print(f"| lean/Demo/{f} | {n} | {t} |")
        print()
        print("| library | lines | tokens |\n| --- | --- | --- |")
        for name, fs in libs:
            n = t = 0
            for x in fs:
                a, b = count_file(x); n += a; t += b
            print(f"| {name} | {n} | {t} |")
    else:
        for f, side, il, it, sl, st, ll, lt in rows:
            print(f"{f:5} {side}: invariants {il:3} lines {it:5} tokens | script {sl:3} lines {st:5} tokens"
                  f" | lemmas {ll:3} lines {lt:5} tokens")
        for f, n, t in shared:
            print(f"shared Demo/{f}: {n} lines, {t} tokens")
        for name, fs in libs:
            n = t = 0
            for x in fs:
                a, b = count_file(x); n += a; t += b
            print(f"{name}: {n} lines, {t} tokens")


main()
