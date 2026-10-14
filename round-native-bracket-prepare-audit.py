from pathlib import Path

old = Path("round-adjoint-generator-audit.py").read_text(encoding="utf-8-sig")
head = old.split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-adjoint-generator"': 'PREFIX = "round-native-bracket"',
    'OLD = "round-native-adjoint"': 'OLD = "round-adjoint-generator"',
    'len(baseline["files"]) == 724 and len(new_modules) == 3': 'len(baseline["files"]) == 727 and len(new_modules) == 6',
    'len(own) == 709 and len(pnt) == 9': 'len(own) == 715 and len(pnt) == 9',
    'len(names) == len(set(names)) == 26': 'len(names) == len(set(names)) == 29',
    'sum(c["theorems"] for c in module_counts.values()) == 25': 'sum(c["theorems"] for c in module_counts.values()) == 27',
    'len(registered) == len(set(registered)) == len(actual) == 3635': 'len(registered) == len(set(registered)) == len(actual) == 3664',
    'len(previous) == 3609': 'len(previous) == 3635',
    'len(source_files) == len({f["path"] for f in source_files}) == 727': 'len(source_files) == len({f["path"] for f in source_files}) == 733',
}
for before, after in changes.items():
    assert head.count(before) == 1, before
    head = head.replace(before, after)
body = Path("round-native-bracket-audit-body.py").read_text(encoding="utf-8-sig")
Path("round-native-bracket-audit.py").write_text(head + "\n" + body, encoding="utf-8")
