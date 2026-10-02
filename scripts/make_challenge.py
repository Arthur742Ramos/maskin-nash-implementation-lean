"""Generate genuine definitions and the two exact comparator statement holes.

Complete proofs remain in the Maskin library imported by Solution.
"""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def statement(source, name):
    match = re.search(r"(?m)^theorem " + re.escape(name) + r"\b[\s\S]*?:=", source)
    assert match, f"Missing theorem statement: {name}"
    return match.group(0) + " by\n  sorry\n"


def render():
    defs = (ROOT / "Maskin/Defs.lean").read_text()
    sufficiency = (ROOT / "Maskin/Sufficiency.lean").read_text()
    namespace = "namespace Maskin\n"
    start = defs.index(namespace) + len(namespace)
    stop = defs.index("theorem maskin_necessity", start)
    # Preserve every byte of the definition block, including classical bodies.
    definitions = defs[start:stop]
    header = """module

public import Mathlib

/-!
Compact comparison surface for Maskin's Nash implementation theorem.
All definitions below are genuine, with their exact library bodies.
Only the two comparator-selected theorem proofs are deliberate statement holes.
The complete, mechanically checked proofs are in the Maskin library imported by Solution.
The proofs were developed with AI assistance and then independently compiled,
audited for placeholders and axioms, and comparator-checked; no separate
independent human review of the proofs was performed.
The official comparator checks their exact contracts.
-/

@[expose] public section

open scoped BigOperators

namespace Maskin
"""
    # Mirror the reference tail: the expose section is left open at EOF
    # (as in the reference Challenge.lean); only the namespace is closed.
    return (header + definitions
            + statement(defs, "maskin_necessity") + "\n"
            + statement(sufficiency, "maskin_sufficiency")
            + "\nend Maskin\n")


if __name__ == "__main__":
    (ROOT / "Challenge.lean").write_text(render())
    print("wrote Challenge.lean")
