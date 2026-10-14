"""Exact proof registration and unchanged verification gates for native global inverse."""
from pathlib import Path
import ast
import json
import re

prefix = "round-native-global-inverse"
old_prefix = "round-native-dexp-filtration"
modules = ["Hindman168/NativeLieGlobalLogarithm.lean", "Hindman168/NativeLieExponentialDiffeomorph.lean"]


def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)


register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-exponential-fibers-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = re.sub(r"\b(?:759|55|48)\b", lambda m: {"759": "770", "55": "10", "48": "8"}[m[0]], register)
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")
head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-dexp-filtration"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-exponential-fibers"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 759 and len(new_modules) == 11': 'len(baseline["files"]) == 770 and len(new_modules) == 2',
    'len(own) == 752 and len(pnt) == 9': 'len(own) == 754 and len(pnt) == 9',
    'len(names) == len(set(names)) == 55': 'len(names) == len(set(names)) == 10',
    'sum(c["theorems"] for c in module_counts.values()) == 48': 'sum(c["theorems"] for c in module_counts.values()) == 8',
    'len(registered) == len(set(registered)) == len(actual) == 3854': 'len(registered) == len(set(registered)) == len(actual) == 3864',
    'len(previous) == 3799': 'len(previous) == 3854',
    'len(source_files) == len({f["path"] for f in source_files}) == 770': 'len(source_files) == len({f["path"] for f in source_files}) == 772',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)
application = [
    "PROGRESS: the preceding finite-Picard and whole-group covering round was recorded and freshly rechecked before this saved 770-file baseline and current edits. Every baseline source/config hash is verified before registration. Retained proofs, StrongStatement, pins and attribution stay unchanged; only root imports and exact-name registry change among retained sources. No official/remote updates are checked and no unavoidable blocker is established.",
    "NativeLieGlobalLogarithm uses the proved genuine E-to-G exponential covering of the entire original connected finite-dimensional nilpotent group. The original G is genuinely locally path connected because the original exponential is a quotient map from the actual real normed model E. No separate local-connectivity assumption is supplied, and original simply connectedness is not transferred to an open subset.",
    "The actual covering lifting theorem applied to the identity continuous map of the whole original simply connected G and the actual lift 0 of 1 constructs a genuine continuous map L:G-to-E with L(1)=0 and Exp(L(g))=g. This is derived from the actual original covering, not a supplied logarithm, global inverse or flow. The original model is genuinely preconnected. True covering lift uniqueness compares L composed with Exp to identity E at zero, so L(Exp(v))=v. Hence actual original exponential injectivity is proved and the actual additive period subgroup K is exactly bottom.",
    "NativeLieExponentialDiffeomorph identifies the constructed global logarithm with the retained actual native local logarithm near each original Exp(v). Whole-group surjectivity covers every original g. Actual exponential injectivity turns their genuine right inverse identities into actual local equality, which transfers the proved native C-infinity local inverse regularity. The actual Exp and actual L, with proved two-sided inverse laws, constitute a native Diffeomorph between original model E and original arbitrary G. Actual manifold differentiation of their identity composition gives the true inverse differential composition. No matrix replacement, assumed BCH or inverse regularity is supplied.",
    "Two new modules, eight proved theorems and two definitions give ten exact new kernel reports. Require actual terminal exit-zero full build/kernel records, byte logs and hashes, current oleans, exact names/imports and all-source trust scans. All 754 own and nine attributed PNT+ modules, plus root and registry, are covered. Retained axiom sets and six retained axiom-free reports remain unchanged. Only standard axioms are allowed; fixed local paper objects and dependency pins are checked without updates.",
    "Remaining: identify the actual finite Picard product logarithm as the rational Lie-polynomial BCH structure, compare individual original group/Lie lower-central layers, derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Original nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and prize submission await full proof and audit.",
]
components = [
    "actual original simply connected nilpotent Lie group has a genuine continuous global logarithm by whole-group covering lifting with true two-sided inverse laws and eliminated original period subgroup",
    "actual original native exponential and its constructed global logarithm form a genuine native C-infinity diffeomorphism with true inverse differential composition",
]
progress = (
    "The actual original native adjoint differential is the original native bracket, and original group nilpotency proves native Lie lower-central termination at the original class c. The actual original exponential comes from proved genuine global invariant curves. Original relative-curve mixed derivatives and group cocycle prove the actual finite dexp formula and genuine native local C-infinity inverses. Original fibers are exactly cosets of the proved closed discrete native central period subgroup. Actual dexp defect W_v lowers original layers, W_v^c=0, and the genuine finite geometric sum U_v is its true two-sided inverse. The actual C-infinity field F_w(v)=U_v(w) strictly improves parameter differences by one original lower-central layer. Original finite-dimensionality proves these layers genuinely closed and true quotient-map integral commutation keeps actual integrals inside them. "
    "Actual global Picard iterates gamma_0=u and gamma_(n+1)=u+integral(0..t,F_w(gamma_n)) have true FTC derivatives. Actual differences gamma_(n+1)-gamma_n belong to S_n; the original nilpotency class c kills the next difference, proving gamma_(c+1)=gamma_c and the genuine global logarithm-lifting ODE including c=0. Actual manifold chain rules and original global integral-curve uniqueness prove Exp(gamma(t))=Exp(u)*gamma_w(t), giving a true product logarithm at one. The actual original exponential range is a subgroup; its true openness and original connectedness make it all of G. Thus genuine whole-group surjectivity and the actual additive-period quotient covering are proved. "
    "Original simply connectedness now eliminates the actual period group. Original local path connectedness is genuinely derived from the actual exponential quotient map of original E; it is not an extra premise. The true covering lifting theorem lifts identity G with lift zero of one to an actual continuous logarithm L. Actual preconnectedness of original E and genuine covering lift uniqueness prove both inverse laws L(Exp(v))=v and Exp(L(g))=g. Actual original exponential injectivity follows and K is exactly bottom. Near every original group point the actual global L equals the previously constructed true local logarithm by injectivity. Therefore L is genuinely native C-infinity. The actual native exponential and this constructed L form a global native C-infinity Diffeomorph E-to-G, with actual inverse differential composition. Global surjectivity, injectivity, period elimination and global smooth inverse no longer remain open tasks. No replacement matrix model, supplied global inverse, assumed BCH or nonabelian additive lattice logarithms is used. "
    "Remaining: prove that the genuine finite Picard product logarithms have the required rational Lie-polynomial BCH structure; compare individual original group/Lie lower-central layers; derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Full calibration/Alignment and original ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established."
)
body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
numeric = {"834": "845", "845": "847", "48": "8", "55": "10", "752": "754", "761": "763", "3854": "3864", "759": "770", "11": "2"}
body = re.sub(r"\b(?:" + "|".join(numeric) + r")\b", lambda m: numeric[m[0]], body)
old_status = "Global exponential invertibility for arbitrary connected simply connected nilpotent Lie groups, full faithful matrix integration or Malcev comparison, BCH comparison outside the concrete strict-matrix realization, and transfer to arbitrary original paper groups with their specified lattices remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted."
new_status = "Global native C-infinity exponential invertibility for arbitrary original connected simply connected finite-dimensional real nilpotent Lie groups is now proved from the actual covering lift and actual local inverse comparison. Full faithful matrix integration or Malcev comparison, rational Lie-polynomial BCH comparison outside the concrete strict-matrix realization, and specified-lattice rational subgroup cocompactness remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted."
anchor = "    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)\n"
replacement = anchor + "    old_status = " + repr(old_status) + "\n    new_status = " + repr(new_status) + "\n    assert remaining.count(old_status) == 1\n    remaining = remaining.replace(old_status, new_status)\n"
body = replace_exact(body, anchor, replacement)
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-native-global-inverse: PROGRESS. Two new modules, eight proved theorems and two definitions; ten exact new reports. All 770 baseline source/config hashes verified before registration. Retained proofs, pins and attribution unchanged; only root and registry changed. The actual original E-to-G exponential covering and quotient-derived original local path connectedness permit the genuine covering lifting theorem on the original simply connected G. It constructs L:G-to-E with L(1)=0 and Exp(L(g))=g. Actual preconnectedness of original E and actual lift uniqueness prove L(Exp(v))=v, genuine original exponential injectivity and K=bottom. Actual injectivity identifies L locally with the actual native local logarithm at every group point, proving native C-infinity regularity. The actual original exponential and derived L are a genuine global native C-infinity Diffeomorph with actual inverse differential composition. Rational Lie-polynomial BCH, individual group/Lie layer comparison, Malcev, specified-lattice cocompactness and full arithmetic target remain unproved. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3864 exact unique standard-axiom reports. Retained axioms and six retained axiom-free reports unchanged. All 754 own and nine attributed PNT+ modules plus root and registry scanned; 772 current source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. StrongConjecture and prize target unproved. No unavoidable blocker. Review: round-native-global-inverse-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "modules": len(modules), "theorems": 8, "reports": 10}))
