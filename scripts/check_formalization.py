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
for source in (ROOT / "DirectedCycleFPRAS").glob("*.lean"):
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
    "scope": ("Probabilistic correctness of the oracle reduction, including the conditional sampler, "
              "adaptive good-oracle coupling, median amplification, random-bit rounding, and "
              "oracle-call, random-bit and charged local-operation counts, residual-instance queries "
              "and output bit-size bounds; the expanded cycleFPRAS program combines accuracy, "
              "all amplified-oracle fair bits, and rational output height. Algorithm S support, "
              "fuel, pools, first-open conditional sampling, and early-stop lemmas are checked; "
              "no machine model, so polynomial running time is "
              "assembled from these counts by a written argument, local-operation charges are "
              "trusted annotations, and the accuracy of the cited paper's Algorithm S, as "
              "transcribed, is a hypothesis."),
}
(ROOT / "validation").mkdir(exist_ok=True)
(ROOT / "validation/lean-verification.json").write_text(json.dumps(report, indent=2) + "\n")
print(f"PASS: {len(expected)} theorem axiom audits; no proof admissions.")
