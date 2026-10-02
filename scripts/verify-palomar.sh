#!/usr/bin/env bash
# Check every selected name in both module environments, and require genuine
# definitions (defnInfo) for every definition_name in Challenge.
set -euo pipefail
cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:$PATH"
export LAKE_HOME="$HOME/.elan/toolchains/leanprover--lean4---v4.35.0-rc2"

python3 - <<'PY'
import json
from pathlib import Path
cfg = json.loads(Path("comparator.json").read_text())
names = cfg["theorem_names"] + cfg["definition_names"]
for module, suffix in [("Challenge", "challenge"), ("Solution", "solution")]:
    lines = ["module", f"public import {module}", ""]
    lines.extend(f"#check @{name}" for name in names)
    Path(f"/tmp/maskin-verify-{suffix}.lean").write_text("\n".join(lines) + "\n")
kind_src = ["module", "public import Challenge", "import Lean", "",
            "open Lean Elab Command"]
for name in cfg["definition_names"]:
    kind_src.extend([
        "#eval show CommandElabM Unit from do",
        "  let env ← getEnv",
        f"  match env.find? `{name} with",
        f'  | some (.defnInfo _) => logInfo "DEF-OK {name}"',
        f'  | _ => throwError "NOT-A-DEF {name}"',
    ])
Path("/tmp/maskin-verify-defkinds.lean").write_text("\n".join(kind_src) + "\n")
print("generated check files")
PY

echo "== elaboration against Challenge =="
lake env lean /tmp/maskin-verify-challenge.lean
echo "== elaboration against Solution =="
lake env lean /tmp/maskin-verify-solution.lean
echo "== definition kinds in Challenge =="
lake env lean /tmp/maskin-verify-defkinds.lean 2>&1 | grep -c "DEF-OK" | xargs -I{} echo "defs confirmed: {}"
echo "== comparator name check PASS =="
