"""Correct the module count after repeating all actual proof audit checks."""
from importlib.util import spec_from_file_location, module_from_spec

spec = spec_from_file_location("current_audit", "round-native-lie-subgroups-audit.py")
audit = module_from_spec(spec)
spec.loader.exec_module(audit)
baseline, registration, files, verified, blog, alog, fixed = audit.checks()
manifest = audit.obj("verification-manifest.json")
review = audit.obj("round-native-lie-subgroups-review.json")
assert manifest["files"] == files
assert manifest["last_round"]["remaining"] == review["remaining"]
assert review["verification"] == verified
assert len(manifest["proved_components"]) == 857
assert manifest["proved_components"][-10:] == audit.COMPONENTS
assert manifest["last_round"]["new_module_count"] == 47
assert len(registration["new_modules"]) == 10
manifest["last_round"]["new_module_count"] = len(registration["new_modules"])
audit.write_obj("verification-manifest.json", manifest)
print("Corrected recorded module count to the verified ten modules; proof hashes and logs unchanged.")
