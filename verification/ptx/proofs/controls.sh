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
trap 'rm -rf "$tmp"' EXIT
fail=0

run() { # name ptx spec proof want-verdict reason-substring
  local name=$1 ptx=$2 spec=$3 proof=$4 want=$5 why=$6 got reason
  set +e
  "$exe" ptx check "$ptx" --spec "$spec" --project "$root" --proof "$proof" >"$tmp/r.json"
  set -e
  got=$(python3 -c 'import json,sys; print(json.load(open(sys.argv[1]))["verdict"])' "$tmp/r.json")
  reason=$(python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(" ".join(d["reasons"]))' "$tmp/r.json")
  if [[ $got == "$want" && $reason == *"$why"* ]]; then
    printf '%-34s %-8s ok\n' "$name" "$got"
  else
    printf '%-34s %-8s WRONG (want %s, reason %s): %s\n' "$name" "$got" "$want" "$why" "$reason"
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
echo "proof controls: 2 supplied proofs accepted, 10 negative controls refused"
