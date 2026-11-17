"""Check Palomar packaging and metadata; Comparator checks the formal statements.

Requires validation/requirements.txt. The metadata schema is pinned; --schema
can supply that schema locally when running without network access.
"""
from pathlib import Path
import argparse
import json
import os
import re
import urllib.request

import jsonschema
import yaml

ROOT = Path(__file__).resolve().parents[1]
SCHEMA_URL = (
    "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/"
    "99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json"
)
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--schema", type=Path, help="local copy of the pinned v0.4 schema")
args = parser.parse_args()
schema = (json.loads(args.schema.read_text()) if args.schema else
          json.load(urllib.request.urlopen(SCHEMA_URL)))
metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text())
jsonschema.Draft7Validator(schema).validate(metadata)
assert metadata["project"]["responsible_maintainers"]
assert metadata["project"]["license"] == "Apache-2.0"
license_text = (ROOT / "LICENSE").read_text()
assert "Apache License" in license_text and "Version 2.0, January 2004" in license_text
assert "TEMPLATE:" not in (ROOT / "formalization.yaml").read_text()
assert metadata["status"]["sorry_count"] == metadata["status"]["sorry_in_definitions"] == 0
sources = metadata["sources"]
assert all(s["relationship"] in {
    "formalizes", "adapts", "independently-proves", "background", "other"
} for s in sources)
assert any(s["relationship"] in {"formalizes", "adapts", "independently-proves"} for s in sources)
assert all(s.get("type") != "original-proof" for s in sources)

config = json.loads((ROOT / "comparator.json").read_text())
assert set(config) == {
    "challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms"
}
assert config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
assert set(config["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"}
assert config["theorem_names"]
assert set(config["theorem_names"]) == {
    s["lean"] for s in metadata["alignment"]["statements"]
}
audit = (ROOT / "validation/Axioms.lean").read_text()
for name in config["theorem_names"] + config["definition_names"]:
    assert f"#print axioms {name}\n" in audit, name

count = 0
for directory, dirs, files in os.walk(ROOT, followlinks=False):
    dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
    for name in files:
        if not name.endswith(".lean"):
            continue
        source = Path(directory) / name
        assert not source.is_symlink(), source
        content = source.read_text()
        assert len(content.splitlines()) <= 10000, source
        if name != "lakefile.lean":
            assert re.match(r"\s*module\b", content), source
        count += 1
challenge = (ROOT / "Challenge.lean").read_text()
assert len(challenge.splitlines()) <= 300 and len(challenge.encode()) <= 32 * 1024
imports = re.findall(r"^(?:public )?import (\S+)", challenge, re.M)
assert imports and all(i == "Mathlib" or i.startswith("Mathlib.") for i in imports)
assert (ROOT / "lakefile.toml").is_file() and not (ROOT / "lakefile.lean").exists()
manifest = json.loads((ROOT / "lake-manifest.json").read_text())
assert all(p["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", p["rev"])
           for p in manifest["packages"])
mathlib_toolchain = ROOT / ".lake/packages/mathlib/lean-toolchain"
if mathlib_toolchain.exists():
    assert mathlib_toolchain.read_text().strip() == (ROOT / "lean-toolchain").read_text().strip()
print(f"PASS: metadata schema; {count} Lean source modules; independent Challenge; pinned dependencies.")
print("Run scripts/check.sh and scripts/verify-comparator.sh for proof validation.")
