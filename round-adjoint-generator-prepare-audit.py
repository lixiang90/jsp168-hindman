from pathlib import Path

old = Path("round-native-adjoint-audit.py").read_text(encoding="utf-8")
head = old.split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-adjoint"': 'PREFIX = "round-adjoint-generator"',
    'OLD = "round-curve-regularity"': 'OLD = "round-native-adjoint"',
    'len(baseline["files"]) == 719 and len(new_modules) == 5': 'len(baseline["files"]) == 724 and len(new_modules) == 3',
    'len(own) == 706 and len(pnt) == 9': 'len(own) == 709 and len(pnt) == 9',
    'len(names) == len(set(names)) == 36': 'len(names) == len(set(names)) == 26',
    'sum(c["theorems"] for c in module_counts.values()) == 31': 'sum(c["theorems"] for c in module_counts.values()) == 25',
    'len(registered) == len(set(registered)) == len(actual) == 3609': 'len(registered) == len(set(registered)) == len(actual) == 3635',
    'len(previous) == 3573': 'len(previous) == 3609',
    'len(source_files) == len({f["path"] for f in source_files}) == 724': 'len(source_files) == len({f["path"] for f in source_files}) == 727',
}
for before, after in changes.items():
    assert head.count(before) == 1, before
    head = head.replace(before, after)
body = Path("round-adjoint-generator-audit-body.py").read_text(encoding="utf-8")
Path("round-adjoint-generator-audit.py").write_text(head + "\n" + body, encoding="utf-8")
