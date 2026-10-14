from pathlib import Path
import json
import sys
from importlib.util import spec_from_file_location, module_from_spec

sys.stdout.reconfigure(encoding="utf-8")
spec = spec_from_file_location("previous_audit", "round-native-bracket-audit.py")
old = module_from_spec(spec)
spec.loader.exec_module(old)
prefix = "round-group-lie-nilpotency"
baseline = old.obj(prefix + "-baseline.json")
assert len(baseline["files"]) == 733
assert all(old.digest(f["path"]) == f["sha256"] for f in baseline["files"])
modules = [
    "Hindman168/NativeLieCommutatorDerivative.lean",
    "Hindman168/NativeLieCommutatorWords.lean",
    "Hindman168/LieLowerCentralProductCutoff.lean",
    "Hindman168/NativeLieCommutatorProducts.lean",
    "Hindman168/NativeLieGroupNilpotency.lean"
]

names = []
counts = {}
for path in modules:
    ds = old.declarations(path)
    names.extend("Hindman168." + n for _, n in ds)
    counts[Path(path).stem] = {
        "theorems": sum(k in {"theorem", "lemma"} for k, _ in ds),
        "selected_declarations": len(ds),
    }
assert len(names) == len(set(names)) == 23
assert sum(c["theorems"] for c in counts.values()) == 21
root = old.read("Hindman168.lean")
registry = old.read("Verification.lean")
for path in modules:
    statement = "import " + path[:-5].replace("/", ".")
    assert statement not in root.splitlines()
    root += "\n" + statement + "\n"
for name in names:
    statement = "#print axioms " + name
    assert statement not in registry.splitlines()
    registry += "\n" + statement + "\n"
Path("Hindman168.lean").write_text(root, encoding="utf-8")
Path("Verification.lean").write_text(registry, encoding="utf-8")
old.write_obj(prefix + "-registration.json", {
    "baseline_hashes_verified_before_registration": 733,
    "new_modules": modules, "names": names, "module_report_counts": counts,
})
print(json.dumps({"new_modules": len(modules), "counts": counts,
                  "new_reports": len(names), "new_theorems": 21}))
