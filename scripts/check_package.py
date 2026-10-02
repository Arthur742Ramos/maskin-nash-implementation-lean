"""Fail closed on contract drift and holes outside named Challenge statements."""
import hashlib
import json
import platform
import re
import sys
from datetime import datetime, timezone
from pathlib import Path

from make_challenge import render

ROOT = Path(__file__).resolve().parent.parent
cfg = json.loads((ROOT / "comparator.json").read_text())
expected = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": ["Maskin.maskin_necessity", "Maskin.maskin_sufficiency"],
    "definition_names": ["Maskin.Profile", "Maskin.lowerContour", "Maskin.MaskinMonotone",
                         "Maskin.NoVetoPower", "Maskin.CanonMsg", "Maskin.canonOutcome",
                         "Maskin.attainable", "Maskin.IsNashEq", "Maskin.NashImplements"],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
}
assert cfg == expected, "Comparator contract differs from the selected Maskin contract"
assert len(cfg["theorem_names"]) == 2 and len(cfg["definition_names"]) == 9
original = (ROOT / "Challenge.lean").read_bytes()
assert original == render().encode(), "Challenge differs from the generated library source"
assert len(original) <= 100 * 1024 and len(original.splitlines()) <= 1000
for file in [*ROOT.glob("*.lean"), *ROOT.glob("Maskin/*.lean")]:
    content = file.read_text()
    assert content.startswith("module\n"), f"Missing module header: {file}"
    if file == ROOT / "Challenge.lean":
        # Generation equality restricts holes to the two selected theorem proofs.
        assert len(re.findall(r"(?m)^  sorry$", content)) == 2
        checked_content = re.sub(r"(?m)^  sorry$", "", content)
    else:
        checked_content = content
    assert not re.search(r"\b(sorry|sorryAx|admit|axiom|unsafe|native_decide|ofReduceBool)\b", checked_content), file
    assert len(content.splitlines()) <= 10000, file
for name in cfg["definition_names"]:
    assert re.search(r"(?m)^(?:noncomputable\s+)?(?:def|abbrev)\s+"
                     + re.escape(name.removeprefix("Maskin.")) + r"\b", original.decode()), name
assert all(re.search(r"(?m)^theorem\s+" + re.escape(n.removeprefix("Maskin.")) + r"\b", original.decode())
           for n in cfg["theorem_names"])
print(f"Package shape: PASS; Challenge {len(original.splitlines())} lines, {len(original)} bytes; two named statement holes; complete library/Solution")

axioms = ROOT / "evidence/final-axioms.log"
if axioms.exists():
    rows = dict(re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", axioms.read_text()))
    noax = set(re.findall(r"'([^']+)' does not depend on any axioms", axioms.read_text()))
    assert not (set(rows) & noax), "duplicate axiom rows"
    rows.update({name: "" for name in noax})
    selected = cfg["theorem_names"] + cfg["definition_names"]
    assert set(selected) <= rows.keys(), set(selected) - rows.keys()
    for name, used in rows.items():
        assert set(re.findall(r"[A-Za-z][A-Za-z0-9_.]*", used)) <= set(cfg["permitted_axioms"]), (name, used)
    print("All selected declarations and internal proof milestones use only the three standard axioms")

files = sorted(set([*ROOT.glob("*.lean"), *ROOT.glob("Maskin/*.lean"),
                    ROOT / "lean-toolchain", ROOT / "lake-manifest.json", ROOT / "comparator.json"]))
hashes = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in files}
record = {
    "source_files_sha256": hashes,
    "lean": (ROOT / "lean-toolchain").read_text().strip(),
    "mathlib": "065356127b1dc0016f66b7283ce0ce2c4055aa55",
    "comparison": "two exact theorem statements with named Challenge holes; nine genuine unchanged definitions; complete Solution proofs",
    "verification_kernels": ["Lean default"],
}
manifest = ROOT / "evidence/verification-manifest.json"
if "--record" in sys.argv:
    record["recorded_at_utc"] = datetime.now(timezone.utc).isoformat()
    record["local_platform"] = platform.platform()
    manifest.parent.mkdir(parents=True, exist_ok=True)
    manifest.write_text(json.dumps(record, indent=2) + "\n")
else:
    assert manifest.exists(), "Missing verification manifest; use --record after validation"
    saved = json.loads(manifest.read_text())
    for key, value in record.items():
        assert saved[key] == value, ("Verification manifest mismatch", key)
    print("Recorded source hashes match the exact current source")
