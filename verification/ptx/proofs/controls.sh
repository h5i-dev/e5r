#!/usr/bin/env bash
# Supplied-proof route (docs/verification/ptx.md, "Supplied proofs"):
# the two supplied proofs must be accepted, and every negative control
# refused with the reason it targets.
#
#   proofs/controls.sh E5R_VERIFY
set -euo pipefail
exe=$1
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
tc=$(tr -d '[:space:]' <"$root/lean-toolchain")
tmp=$(mktemp -d)
checker="$root/.lake/build/bin/proofcheck"
cleanup() {
  if [[ -f "$tmp/proofcheck.original" ]]; then cp "$tmp/proofcheck.original" "$checker"; fi
  rm -rf "$tmp"
}
trap cleanup EXIT
fail=0

run() { # name ptx spec proof want-verdict reason-substring
  local name=$1 ptx=$2 spec=$3 proof=$4 want=$5 why=$6 got reason rc expected_rc
  set +e
  "$exe" ptx check "$ptx" --spec "$spec" --project "$root" --proof "$proof" --memory-mb "${E5R_SUPPLIED_MEMORY_MIB:-6144}" >"$tmp/r.json"
  rc=$?
  set -e
  got=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$tmp/r.json")
  reason=$(python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(" ".join(d["reasons"]))' "$tmp/r.json")
  if [[ $got == proved && $want == proved ]]; then
    cp "$checker" "$tmp/proofcheck.original"
    if ! "$exe" verify-result "$tmp/r.json" > /dev/null 2>&1; then
      echo "WRONG: accepted supplied proof is not fresh" >&2; fail=1
    fi
    python3 - "$checker" <<'PYCHECKER'
import pathlib, sys
p = pathlib.Path(sys.argv[1]); p.write_bytes(p.read_bytes() + b'\0')
PYCHECKER
    if "$exe" verify-result "$tmp/r.json" > /dev/null 2>&1; then
      echo "WRONG: a changed checker executable is still fresh" >&2; fail=1
    fi
    cp "$tmp/proofcheck.original" "$checker"
  fi
  expected_rc=3
  [[ $want == proved ]] && expected_rc=0
  if [[ $got == "$want" && $reason == *"$why"* && $rc == "$expected_rc" ]]; then
    printf '%-34s %-8s ok\n' "$name" "$got"
  else
    printf '%-34s %-8s WRONG (want %s, reason %s, exit %s; got exit %s): %s\n' "$name" "$got" "$want" "$why" "$expected_rc" "$rc" "$reason"
    fail=1
  fi
}

k=$root/m5/m4/kernels
s=$root/m5/m4/specs
run "a_direct, supplied proof" "$k/a_direct.ptx" "$s/a_direct.json" "$here/a_direct.lean" proved ""
run "s_pingpong, supplied proof" "$k/s_pingpong.ptx" "$s/s_pingpong.json" "$here/s_pingpong.lean" proved ""

ph=$(sha256sum "$k/a_direct.ptx" | cut -d' ' -f1)
sh=$(sha256sum "$s/a_direct.json" | cut -d' ' -f1)
man="/- e5r-proof ptx=$ph spec=$sh toolchain=$tc -/"
neg() { # name reason body
  printf '%s\n%s\n' "$man" "$3" >"$tmp/$1.lean"
  run "refused: $1" "$k/a_direct.ptx" "$s/a_direct.json" "$tmp/$1.lean" unknown "$2"
}
neg weaker "does not state E5rSpec.statement" 'import E5rSpec
theorem E5rProof.correct : True := trivial'
neg different "does not state E5rSpec.statement" 'import E5rSpec
theorem E5rProof.correct : ¬ E5rSpec.statement → True := fun _ => trivial'
neg sorry "sorryAx" 'import E5rSpec
theorem E5rProof.correct : E5rSpec.statement := sorry'
neg axiom "declares the axiom" 'import E5rSpec
axiom cheat : E5rSpec.statement
theorem E5rProof.correct : E5rSpec.statement := cheat'
neg skip-kernel "kernel rejects" 'import E5rSpec
import Lean
open Lean Elab Command
set_option debug.skipKernelTC true
run_cmd liftTermElabM do
  let d : TheoremVal := {
    name := "E5rProof.correct".toName
    levelParams := []
    type := mkConst ("E5rSpec.statement".toName)
    value := mkConst ("True.intro".toName) }
  addDecl (.thmDecl d)'
neg native-decide "does not compile" 'import E5rSpec
theorem E5rProof.correct : E5rSpec.statement := by native_decide'
neg import "only the statement module" 'import E5rSpec
import Lake
theorem E5rProof.correct : E5rSpec.statement := sorry'

# Use the real accepted proof and add an elaboration side effect; its proposition
# is unchanged in memory, but the tool-owned statement artifact must be immutable.
python3 - "$here/a_direct.lean" "$tmp/artifact.lean" <<'PYCONTROL'
import pathlib, sys
s = pathlib.Path(sys.argv[1]).read_text()
s = s.replace('import E5rSpec', 'import E5rSpec\nimport Lean', 1)
s = s.replace('namespace E5rProof', 'run_cmd Lean.Elab.Command.liftIO <| IO.FS.writeFile "E5rSpec.lean" "def statement : Prop := True"\n\nnamespace E5rProof', 1)
pathlib.Path(sys.argv[2]).write_text(s)
PYCONTROL
run "refused: changed statement artifact" "$k/a_direct.ptx" "$s/a_direct.json" "$tmp/artifact.lean" unknown "generated statement artifacts changed"

# The original checker is restored even if the mutation control fails.
checker="$root/.lake/build/bin/proofcheck"
cp "$checker" "$tmp/proofcheck.original"
python3 - "$here/a_direct.lean" "$tmp/checker-artifact.lean" <<'PYCONTROL'
import pathlib, sys
s = pathlib.Path(sys.argv[1]).read_text()
s = s.replace('import E5rSpec', 'import E5rSpec\nimport Lean', 1)
s = s.replace('namespace E5rProof', 'run_cmd Lean.Elab.Command.liftIO do\n    let some path ← IO.getEnv "E5R_CHECKER" | throw <| IO.userError "missing checker"\n    let bytes ← IO.FS.readBinFile path\n    IO.FS.writeBinFile path (bytes.push 0)\n\nnamespace E5rProof', 1)
pathlib.Path(sys.argv[2]).write_text(s)
PYCONTROL
run "refused: changed checker executable" "$k/a_direct.ptx" "$s/a_direct.json" "$tmp/checker-artifact.lean" unknown "proof checker executable changed"
cp "$tmp/proofcheck.original" "$checker"

# a proof bound to other inputs: the a_direct proof against an edited spec
python3 - "$s/a_direct.json" "$tmp/a_direct_edited.json" <<'EOF'
import json, sys
d = json.load(open(sys.argv[1])); d["max_block"] = 512
json.dump(d, open(sys.argv[2], "w"), indent=2)
EOF
run "refused: stale spec hash" "$k/a_direct.ptx" "$tmp/a_direct_edited.json" "$here/a_direct.lean" unknown "written for a different spec"
sed 's/toolchain=[^ ]*/toolchain=leanprover\/lean4:v4.34.0/' "$here/a_direct.lean" >"$tmp/oldtc.lean"
run "refused: stale toolchain" "$k/a_direct.ptx" "$s/a_direct.json" "$tmp/oldtc.lean" unknown "written for a different toolchain"
grep -v 'e5r-proof' "$here/a_direct.lean" >"$tmp/nomanifest.lean"
run "refused: no manifest" "$k/a_direct.ptx" "$s/a_direct.json" "$tmp/nomanifest.lean" unknown "no \`e5r-proof"

((fail)) && { echo "proof controls: FAILED" >&2; exit 1; }
echo "proof controls: 2 supplied proofs accepted, 12 negative controls refused; checker freshness controls passed"
