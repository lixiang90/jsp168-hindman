"""Portable source-hash check and optional build/registered-axiom audit.

This verifies the recorded partial checkpoint, not StrongConjecture.
Historical workstation-specific round audits remain unchanged.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="also run lake build and Verification.lean")
    args = parser.parse_args()
    manifest = json.loads((ROOT / "verification-manifest.json").read_text(encoding="utf-8"))
    failures = []
    for item in manifest["files"]:
        path = (ROOT / item["path"]).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file():
            failures.append(item["path"] + ": missing or outside repository")
        elif hashlib.sha256(path.read_bytes()).hexdigest() != item["sha256"]:
            failures.append(item["path"] + ": SHA-256 mismatch")
    if failures:
        print("Snapshot verification failed:\n" + "\n".join(failures), file=sys.stderr)
        return 1
    print(f"Verified {len(manifest['files'])} exact file hashes.", flush=True)
    print("Full target proved: " + str(manifest["full_target_proved"]), flush=True)
    if not args.build:
        return 0
    out = ROOT / "verification-local"
    out.mkdir(exist_ok=True)
    for name, command in [("build", ["lake", "build"]),
                          ("axioms", ["lake", "env", "lean", "Verification.lean"])]:
        print("Running " + " ".join(command), flush=True)
        with (out / (name + ".txt")).open("wb") as log:
            result = subprocess.run(command, cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
        if result.returncode:
            print(f"{name} failed; see {out / (name + '.txt')}", file=sys.stderr)
            return result.returncode
    text = (out / "axioms.txt").read_text(encoding="utf-8")
    reports = re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", text, re.M)
    free = re.findall(r"^'(.+)' does not depend on any axioms", text, re.M)
    actual = {name: {a.strip() for a in axioms.split(',') if a.strip()} for name, axioms in reports}
    actual.update({name: set() for name in free})
    expected = set(re.findall(r"^#print axioms (\S+)", (ROOT / "Verification.lean").read_text(encoding="utf-8"), re.M))
    if set(actual) != expected or len(actual) != manifest["selected_axiom_report_count"]:
        print("Registered axiom report coverage mismatch.", file=sys.stderr)
        return 1
    bad = {name: sorted(axioms - ALLOWED) for name, axioms in actual.items() if axioms - ALLOWED}
    if bad:
        print("Unexpected axioms: " + json.dumps(bad), file=sys.stderr)
        return 1
    print(f"Build and {len(actual)} registered axiom checks passed. Main theorem remains unfinished.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
