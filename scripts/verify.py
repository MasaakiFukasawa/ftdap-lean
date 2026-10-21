#!/usr/bin/env python3
"""Build every project module and check the transitive axiom audit."""
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
MATHLIB_REV = "5ed2965256430c3649e86755f9576b54eca72435"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(command, log):
    with subprocess.Popen(command, cwd=ROOT, env=dict(os.environ, NO_COLOR="1"),
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          text=True) as process:
        output = []
        for line in process.stdout:
            print(line, end="", flush=True)
            log.write(line)
            log.flush()
            output.append(line)
        if process.wait():
            raise SystemExit(f"Command failed: {' '.join(command)}")
    return "".join(output)


def main():
    sources = sorted((ROOT / "src").glob("*.lean"))
    roots = (ROOT / "module-roots.txt").read_text().splitlines()
    if roots != sorted(p.stem for p in sources):
        raise SystemExit("module-roots.txt must list every source module exactly once")
    for path in sources:
        if re.search(r"^\s*(?:axiom|unsafe)\b|\b(?:sorry|admit)\b", path.read_text(), re.M):
            raise SystemExit(f"Unproved declaration or unsafe code in {path.name}")
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    mathlib = next(p for p in manifest["packages"] if p["name"] == "mathlib")
    if mathlib["type"] != "git" or mathlib["rev"] != MATHLIB_REV:
        raise SystemExit("The mathlib manifest pin does not match the audited revision")
    audit = ROOT / "src" / "AllChecks.lean"
    declarations = re.findall(r"^#print axioms (\S+)\s*$", audit.read_text(), re.M)
    if len(declarations) != 323 or len(set(declarations)) != len(declarations):
        raise SystemExit("Expected 323 distinct declarations in AllChecks.lean")
    # Remove stale success reports before starting a new verification.
    (ROOT / "verification.json").unlink(missing_ok=True)
    with (ROOT / "build.log").open("w") as log:
        run(["lake", "build"], log)
    revision = subprocess.check_output(
        ["git", "-C", str(ROOT / ".lake/packages/mathlib"), "rev-parse", "HEAD"],
        text=True).strip()
    if revision != MATHLIB_REV:
        raise SystemExit(f"Unexpected checked-out mathlib revision: {revision}")
    with (ROOT / "verification.log").open("w") as log:
        output = run(["lake", "env", "lean", "-DwarningAsError=true", str(audit)], log)
    if "sorryAx" in output:
        raise SystemExit("A proof placeholder appeared in the axiom audit")
    found = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
    found += [(name, "") for name in re.findall(r"'([^']+)' does not depend on any axioms", output)]
    if len(found) != len(declarations) or {name for name, _ in found} != set(declarations):
        raise SystemExit("The audit output does not cover exactly the requested declarations")
    dependencies = set()
    for name, axioms in found:
        used = {a.strip() for a in axioms.split(",") if a.strip()}
        if used - ALLOWED_AXIOMS:
            raise SystemExit(f"Unexpected axioms for {name}: {sorted(used - ALLOWED_AXIOMS)}")
        dependencies.update(used)
    report = {
        "status": "passed",
        "lean": (ROOT / "lean-toolchain").read_text().strip(),
        "mathlib": revision,
        "modules": len(sources),
        "audited_declarations": len(found),
        "axioms": sorted(dependencies),
        "sources_sha256": {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in sources},
    }
    (ROOT / "verification.json").write_text(json.dumps(report, indent=2) + "\n")
    print(f"Verified {len(sources)} modules and {len(found)} declarations; "
          f"axioms: {', '.join(sorted(dependencies))}.")


if __name__ == "__main__":
    main()
