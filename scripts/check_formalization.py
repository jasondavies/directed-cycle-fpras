"""Build and audit the principal Lean declarations; reject nonstandard axioms."""
from pathlib import Path
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
subprocess.run(["lake", "build"], cwd=ROOT, check=True)
result = subprocess.run(["lake", "env", "lean", "validation/Axioms.lean"], cwd=ROOT,
                        check=True, text=True, capture_output=True)
print(result.stdout, end="")
allowed = {"propext", "Classical.choice", "Quot.sound"}
entries = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", result.stdout)
empty = re.findall(r"'([^']+)' does not depend on any axioms", result.stdout)
expected = re.findall(r"^#print axioms (\S+)", (ROOT / "validation/Axioms.lean").read_text(), re.M)
found = {name for name, _ in entries} | set(empty)
assert found == set(expected), (found, expected)
assert "sorryAx" not in result.stdout
for name, axioms in entries:
    used = {s.strip() for s in axioms.split(",") if s.strip()}
    assert used <= allowed, (name, used - allowed)
for source in [*(ROOT / "DirectedCycleFPRAS").glob("*.lean"), ROOT / "Solution.lean"]:
    # This catches accidental admissions in addition to the dependency audit.
    assert not re.search(r"^\s*(?:axiom\s|opaque\s)|\b(?:sorry|admit)\b",
                         source.read_text(), re.M), source
report = {
    "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
    "mathlib_commit": next(p["rev"] for p in json.loads(
        (ROOT / "lake-manifest.json").read_text())["packages"] if p["name"] == "mathlib"),
    "theorems_audited": expected,
    "axioms": {name: [s.strip() for s in axioms.split(",") if s.strip()]
               for name, axioms in entries} | {name: [] for name in empty},
    "build_passed": True,
    "scope": ("Vertex/feedback-set witnesses; recorded adaptive rejection; concrete counting and "
              "conditional sampling programs; oracle repair, amplification and finite-bit coupling; "
              "oracle-call and composed fair-bit budgets; residual-instance queries and counting "
              "output height; the exact independent-set/acyclicity gadget. Algorithm S fuel, pools, "
              "first-open sampling, stopping, induced-subtype and parent-pointer correspondences "
              "are checked. Harris's inequality, concrete outflow and weighted proposal laws, "
              "empirical-pool moments, resolved predictions, and quantitative finite-program "
              "martingale bounds are checked. Deferred-edge DFS laws, snapshot splitting, "
              "concrete conditional moments and the absorbing round-process correspondence prove "
              "Theorem 9 for Algorithm S. Counting and sampling have no oracle-accuracy premise. "
              "Fixed-parameter bit budgets and intermediate arithmetic heights are checked. "
              "Executable rational programs, explicit graph searches, arbitrary-order Algorithm S "
              "refinement, bounded cumulative selection, fair-bit compilation and tape execution "
              "are checked. The checked sampler reports zero mass exactly and preserves the "
              "positive core's law. Written cost bounds distinguish the indexed implementation "
              "from the supplied executable's repeated scans; compiled Lean runtime is not proved. "
              "Independent-set complexity hardness is external. "
              "The Palomar Solution wrappers are included in the axiom audit; deliberate "
              "Challenge placeholders are excluded. Python models have no Lean refinement proof."),
}
(ROOT / "validation").mkdir(exist_ok=True)
(ROOT / "validation/lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: {len(expected)} theorem axiom audits; no proof admissions.")
