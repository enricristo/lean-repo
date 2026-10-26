#!/usr/bin/env bash
# Re-run, for one challenge folder, the checks that Comparator makes before it accepts a proof:
#   1. Challenge and Submission build as separate modules with the pinned Lean and Mathlib;
#   2. every theorem listed in config.json uses only the permitted axioms;
#   3. every declaration of the Challenge module (types of theorems, types and bodies of
#      definitions) elaborates to exactly the same term in Submission, compared with pp.all, so
#      every implicit argument and instance is visible.
# Comparator itself additionally replays the exported environment through the kernel inside a
# sandbox. This script does not replace it; it reproduces what can be checked with Lean alone.
#
# Usage: bash challenges/check.sh challenges/<folder>
set -euo pipefail
cd "$1"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

if [ ! -d .lake/packages/mathlib/.lake/build ]; then
  lake exe cache get
fi
lake build Challenge Submission

read -r THEOREMS AXIOMS < <(python3 - <<'PY'
import json
c = json.load(open("config.json"))
print(",".join(c["theorem_names"]), ",".join(sorted(c["permitted_axioms"])))
PY
)

status=0
mkdir -p .check
{ echo "import Submission"; for t in ${THEOREMS//,/ }; do echo "#print axioms $t"; done; } > .check/Axioms.lean
lake env lean .check/Axioms.lean | tee .check/axioms.txt
python3 - "$AXIOMS" <<'PY' || status=1
import re, sys
allowed = set(sys.argv[1].split(","))
for line in open(".check/axioms.txt"):
    m = re.search(r"depends on axioms: \[(.*)\]", line)
    if m:
        used = {a.strip() for a in m.group(1).split(",") if a.strip()}
        if not used <= allowed:
            sys.exit(f"forbidden axioms: {sorted(used - allowed)}")
    elif "does not depend on any axioms" not in line and line.strip():
        sys.exit(f"unexpected output: {line.strip()}")
print("axioms: ok")
PY

# Every declaration of the Challenge module, printed with pp.all: types of theorems, types and
# bodies of definitions. The same names are then printed from the Submission module.
dump() {  # $1 = module, $2 = challenge|submission
  cat > ".check/Dump$1.lean" <<LEAN
import $1
open Lean Elab Command Meta
set_option pp.all true
#eval show CommandElabM Unit from do
  let env ← getEnv
  let names : Array Name ← if "$2" == "challenge" then do
      let some idx := env.getModuleIdx? \`Challenge | throwError "Challenge module missing"
      let ns := env.constants.map₁.toList.filterMap fun (n, _) =>
        if env.getModuleIdxFor? n == some idx && !n.isInternal then some n else none
      IO.FS.writeFile ".check/names.txt" (String.intercalate "\n" (ns.map toString))
      pure ns.toArray
    else do
      let s ← IO.FS.readFile ".check/names.txt"
      pure ((s.splitOn "\n").filter (· ≠ "") |>.map String.toName).toArray
  let names := names.qsort (fun a b => a.toString < b.toString)
  let mut out := ""
  for n in names do
    match env.find? n with
    | none => out := out ++ s!"{n} MISSING\n"
    | some ci =>
      let ty ← liftTermElabM <| ppExpr ci.type
      let body ← match ci with
        | .defnInfo d => do
            let v ← liftTermElabM <| ppExpr d.value
            pure s!" := {v}"
        | _ => pure ""
      out := out ++ s!"{n} : {ty}{body}\n"
  IO.FS.writeFile ".check/decls_$2.txt" out
  IO.println s!"{names.size} declarations"
LEAN
  lake env lean ".check/Dump$1.lean"
}
dump Challenge challenge
dump Submission submission
if diff -q .check/decls_challenge.txt .check/decls_submission.txt >/dev/null; then
  echo "statements and definitions: identical"
else
  echo "statements and definitions: DIFFERENT"
  diff .check/decls_challenge.txt .check/decls_submission.txt | head -40 || true
  status=1
fi
exit $status
