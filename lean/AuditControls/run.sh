#!/usr/bin/env bash
# Controls for the axiom audit (lean/Audit.lean) and for nocompiler_auto's
# debugging option. Each control adds one new file to a copy of lean/, with no
# list edited anywhere, and requires the audit to react:
#
#   sorry       a theorem proved with sorry          -> the audit FAILS, naming it
#   bv_decide   a theorem proved with bv_decide      -> the audit passes and lists
#                                                       it in the bv_decide tier
#   debug-src   committed source turning on the debugging option
#                                                    -> the audit FAILS, naming the line
#   debug-use   a nocompiler_auto proof with the debugging option on
#                                                    -> the file does not build
#   unbuilt     a source file whose module was never built
#                                                    -> the audit FAILS
# and the unmodified copy passes.
#
#   lean/AuditControls/run.sh            (from the repository root; needs lake)
set -euo pipefail
cd "$(dirname "$0")/../.."
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
mkdir -p "$work/root/examples"
cp -r lean "$work/root/lean"
cp -r examples/elf "$work/root/examples/elf"
mkdir -p "$work/root/examples/demo" && cp -r examples/demo/elf "$work/root/examples/demo/elf"
L="$work/root/lean"
fail=0
audit() { (cd "$L" && lake exe nocompiler-audit .. > "$work/out" 2>&1); }
add() { printf '%s\n' "$2" > "$L/Examples/$1.lean"; }
drop() { rm -f "$L/Examples/$1.lean"; rm -rf "$L/.lake/build/lib/lean/Examples/$1".*; }
build() { (cd "$L" && lake build "Examples.$1" > "$work/build" 2>&1); }

(cd "$L" && lake build nocompiler-audit > /dev/null)

if audit; then echo "ok   unmodified: the audit passes"
else echo "FAIL unmodified copy fails the audit:"; tail -5 "$work/out"; fail=1; fi

add AuditCtlSorry 'theorem audit_ctl_sorry : (1 : Nat) = 2 := sorry'
build AuditCtlSorry || true
if ! audit && grep -q 'FAIL audit_ctl_sorry depends on \[sorryAx\]' "$work/out"; then
  echo "ok   sorry: the audit fails on audit_ctl_sorry (sorryAx)"
else echo "FAIL sorry: not caught"; tail -5 "$work/out"; fail=1; fi
drop AuditCtlSorry

add AuditCtlBv 'import Std.Tactic.BVDecide
theorem audit_ctl_bv (x y : BitVec 16) : (x ^^^ y) + 2 * (x &&& y) = x + y := by bv_decide'
build AuditCtlBv
if audit && grep -q '^  audit_ctl_bv$' "$work/out"; then
  echo "ok   bv_decide: audit_ctl_bv is listed in the bv_decide tier and the audit passes"
else echo "FAIL bv_decide: not classified"; tail -8 "$work/out"; fail=1; fi
drop AuditCtlBv

add AuditCtlDebug 'import NoCompiler.Auto
set_option nocompiler.auto.debugKernel true
theorem audit_ctl_dbg : True := trivial'
build AuditCtlDebug
if ! audit && grep -q 'FAIL debugging option turned on.*AuditCtlDebug.lean:2' "$work/out"; then
  echo "ok   debug-src: the audit fails on the line that turns the option on"
else echo "FAIL debug-src: not caught"; tail -5 "$work/out"; fail=1; fi
drop AuditCtlDebug

add AuditCtlDebugUse 'import Demo.SumB
open NoCompiler Demo.Sum.ImageB
namespace Demo.Sum
set_option nocompiler.auto.debugKernel true in
theorem sum_dbg : VerifiedImg code sum_dom sum_entry spec := by
  rintro ⟨a, xs⟩ s he ⟨ha0, ha1, hlen, hal, harr⟩
  nocompiler_auto sum_func s he
    loop_inv $l1 (fun u => True) measure (fun u => (u.reg 11).toNat)
end Demo.Sum'
if build AuditCtlDebugUse; then echo "FAIL debug-use: a proof with the debugging option on builds"; fail=1
elif grep -q 'debugKernel is on' "$work/build"; then
  echo "ok   debug-use: a proof with the debugging option on does not build"
else echo "FAIL debug-use: it fails, but not for the option:"; tail -5 "$work/build"; fail=1; fi
drop AuditCtlDebugUse

add AuditCtlUnbuilt 'theorem audit_ctl_unbuilt : True := trivial'
if ! audit && grep -q 'FAIL axiom audit: a module of the source tree could not be imported' "$work/out"; then
  echo "ok   unbuilt: the audit fails on a source file that was not built"
else echo "FAIL unbuilt: not caught"; tail -5 "$work/out"; fail=1; fi
drop AuditCtlUnbuilt

exit $fail
