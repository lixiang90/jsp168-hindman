"""Extend the exact proof audit to genuine rational Picard polynomials."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json

prefix = "round-native-rational-picard"
old_prefix = "round-native-lie-subgroups"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
previous = module_from_spec(spec)
spec.loader.exec_module(previous)
baseline = previous.obj(prefix + "-baseline.json")
assert baseline == previous.obj("verification-manifest.json")
assert len(baseline["files"]) == 782
assert all(previous.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in previous.declarations(p)]
assert len(modules) == 11 and len(decls) == 58
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 44


def replace_exact(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before), count)
    return text.replace(before, after)


register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-global-inverse-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = replace_exact(register, 'len(baseline["files"]) == 772', 'len(baseline["files"]) == 782')
register = replace_exact(register, 'len(names) == len(set(names)) == 47', 'len(names) == len(set(names)) == 58')
register = replace_exact(register, 'sum(c["theorems"] for c in counts.values()) == 43', 'sum(c["theorems"] for c in counts.values()) == 44')
register = replace_exact(register, '"baseline_hashes_verified_before_registration": 772', '"baseline_hashes_verified_before_registration": 782')
register = replace_exact(register, '"new_theorems": 43', '"new_theorems": 44')
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")
head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
head_changes = {
    'PREFIX = "round-native-lie-subgroups"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-global-inverse"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 772 and len(new_modules) == 10': 'len(baseline["files"]) == 782 and len(new_modules) == 11',
    'len(own) == 764 and len(pnt) == 9': 'len(own) == 775 and len(pnt) == 9',
    'len(names) == len(set(names)) == 47': 'len(names) == len(set(names)) == 58',
    'sum(c["theorems"] for c in module_counts.values()) == 43': 'sum(c["theorems"] for c in module_counts.values()) == 44',
    'len(registered) == len(set(registered)) == len(actual) == 3911': 'len(registered) == len(set(registered)) == len(actual) == 3969',
    'len(previous) == 3864': 'len(previous) == 3911',
    'len(source_files) == len({f["path"] for f in source_files}) == 782': 'len(source_files) == len({f["path"] for f in source_files}) == 793',
}
for before, after in head_changes.items():
    head = replace_exact(head, before, after)
head = replace_exact(head, "\n\ndef read(path):", '\n\nNEW_AXIOM_FREE = {"Hindman168.finiteVectorPolynomialSum"}\nAXIOM_FREE = AXIOM_FREE | NEW_AXIOM_FREE\n\n\ndef read(path):')
head = replace_exact(head, '    assert all(a <= ALLOWED for a in actual.values())\n', '    assert all(a <= ALLOWED for a in actual.values())\n    assert {n for n, a in previous.items() if not a} == AXIOM_FREE - NEW_AXIOM_FREE\n    assert NEW_AXIOM_FREE <= set(names) and not NEW_AXIOM_FREE & set(previous)\n')
application = [
    "PROGRESS: the preceding native real Lie-subgroup round was recorded and freshly rechecked before the saved 782-file baseline and these edits. All baseline source/config hashes are reverified before registration. Only root and exact-name registry change among retained sources; proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates are checked and no unavoidable blocker is established.",
    "FiniteVectorPolynomial uses genuine finite lists of degree/coefficient pairs. Evaluation is the actual finite sum of real monomials times original vectors. Exact add, rational scalar and continuity laws are proved. FiniteVectorPolynomialBilinear expands every pair of terms, adds their degrees and applies the actual continuous bilinear map; its real evaluation is exactly the bilinear application of the original polynomial curves. No associative ring structure on the vector model is introduced.",
    "FiniteVectorPolynomialIntegral maps (n,v) to (n+1,v/(n+1)) using rational scalar division. Actual real monomial integrals and the actual Bochner integral add law prove its evaluation equals the genuine primitive from zero at every real t. FiniteVectorPolynomialRational proves coefficient membership under finite sums, rational scales, original bilinear operations and this primitive, and membership at every rational evaluation time. A rational subspace is not assumed closed: explicit rational coefficient arithmetic is the reason integration endpoints remain rational.",
    "FiniteVectorPolynomialSums proves exact finite-sum and iterated-bilinear-power evaluation and coefficient laws. NativeLieRationalDefectPolynomial uses rational signed reciprocal factorials and actual original adjoint differential powers. Its evaluation is exactly the previously proved original dexp defect W_v(w), by the true finite formula and scalar-cast compatibility. Its coefficients stay in a bracket-closed original rational structure.",
    "NativeLieRationalFieldPolynomial represents actual W_v powers recursively and sums the true finite geometric inverse. Its real evaluation is exactly the original actual logarithm-lifting field F_w(v). NativeLieRationalPicardPolynomial recursively forms the original constant u plus the explicit primitive of this original field polynomial. Real evaluation equals every previously constructed genuine Picard integral iterate, not a replacement flow. Coefficients remain in the original rational structure; hence true Picard and stabilized lift values at every rational time lie there.",
    "NativeLieRationalBCH requires only an actual Q-linear subspace V closed under the original native Lie bracket. The rational module is compatible with real scalar restriction by the genuine rational scalar tower; it is not a supplied group model. The retained actual adjoint-differential/native-bracket identification transfers original bracket closure to the polynomial construction. The actual original global logarithm of Exp(u)*Exp(w) belongs to V whenever u,w belong to V. The actual exponential image Exp(V) is itself a subgroup with exact global logarithm membership; it is not asserted topologically closed. No claim is made that logarithms of an arbitrary specified group lattice are an additive lattice.",
    "NativeLieRationalAdjoint derives original generator-power rational membership and actual adjoint invariance under exponentials with rational logarithm from the original finite factorial formula. Whole-group global logarithms transfer this to every original group element whose actual logarithm is in V. This proves the rational-coordinate conjugation fact on an already identified bracket-closed structure; identifying that structure with the arbitrary specified lattice remains a task.",
    "NativeLieRationalProductCurve gives an explicit finite rational polynomial list whose actual real value at every t equals the original global log of Exp(u) times the genuine one-parameter w curve at t. The endpoint is the original noncommuting product logarithm. Every coefficient is generated by actual original bilinear bracket operations and rational scalars, and coefficient membership for any original rational Lie structure is proved. This is an explicit finite recursive rational BCH representation, not a supplied formal identity or an assumed inverse.",
    "Eleven new modules, 44 proved theorems and 14 definitions give 58 exact new reports. Require actual terminal exit-zero complete build/kernel records, byte logs and hashes, exact names/imports, current oleans and all-source trust scans. All 775 own and nine attributed PNT+ modules plus root and registry are covered. Retained axiom sets and six retained axiom-free reports stay unchanged. Newly axiom-free declarations, if any, are separately determined from actual kernel output; no added trust axiom is permitted. No new option overrides are introduced.",
    "Remaining: quantitative degree/denominator bounds and identification of the rational structure associated with an arbitrary specified lattice; reverse individual original group/Lie lower-central inclusion, exact comparison and algebraic group layer closedness; faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness; full calibration/Alignment and ordered positive arithmetic witnesses. StrongConjecture and the full prize target remain unproved; publication and submission await complete proof and audit.",
]
components = [
    "genuine finite real vector polynomial lists have exact additive and rational scalar evaluation laws and continuous actual evaluations",
    "actual continuous bilinear operations on original vector polynomial curves have true finite pairwise coefficient expansions without vector ring assumptions",
    "actual Bochner primitives of finite vector polynomial curves are given by rational reciprocal positive-degree coefficient divisions",
    "actual rational coefficient membership is preserved by finite polynomial arithmetic and primitives and implies rational-time membership without rational-subspace closedness",
    "actual finite vector polynomial sums and iterated bilinear powers have exact real evaluations and true rational coefficient membership",
    "actual original native dexp defect on polynomial curves has an explicit rational factorial and original bracket coefficient representation",
    "actual original finite inverse logarithm field on polynomial curves has a genuine rational finite polynomial representation",
    "all actual original Picard iterates and stabilized logarithm lifts are explicit finite rational polynomials and retain the original rational structure at rational times",
    "actual original noncommuting product logarithms preserve every actual bracket-closed rational Lie structure and its exponential image is a genuine subgroup",
    "actual original adjoint of every group element with rational logarithm preserves the original bracket-closed rational Lie structure by true finite factorial formulas",
    "actual original log of Exp(u) times Exp(t*w) is represented at every real time by an explicit finite rational original-bracket Picard polynomial",
]
progress = previous.NEW_PROGRESS.split("Remaining:", 1)[0] + (
    "The genuine finite Picard product logarithm now has an explicit finite recursive rational original-bracket polynomial representation. Actual finite coefficient lists evaluate as real vector polynomials; pairwise original bilinear expansion and rational scaling preserve exact evaluations. The actual Bochner primitive of a monomial is given by division by its positive new degree in Q. Thus rational-time membership is proved by exact arithmetic, without treating an arbitrary Q-linear subspace as topologically closed. Actual original dexp defect powers and the actual finite geometric inverse field have explicit rational polynomial lists, using the actual adjoint differential already identified with the original native bracket. The actual Picard integral iterates exactly equal the real evaluations of their recursively constructed finite coefficient lists. Their coefficients stay in every original bracket-closed Q-linear structure V containing u,w; all true Picard iterates and the stabilized lift belong to V at rational times. The actual global logarithm of Exp(u)*Exp(w) therefore belongs to V, and Exp(V) itself is a genuine subgroup with exact actual logarithm membership. Actual original finite factorial adjoint formulas prove that conjugation by group elements with logarithms in V preserves V. An explicit finite polynomial list represents the actual original global logarithm of Exp(u)*Exp(t*w) for every real t, with the genuine product logarithm at one. All operations use original vectors, original brackets and rational scalars, not replacement matrices or supplied BCH laws. "
    "Remaining: quantitative degree/denominator bounds and identification of the rational structure arising from an arbitrary specified lattice; reverse individual original group/Lie lower-central inclusion, exact series comparison and algebraic group layer closedness; faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. The actual finite rational BCH construction does not make logarithms of a nonabelian specified lattice additive. Full calibration/Alignment and original ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established."
)
body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
body = body[:start] + "    note = __CURRENT_NOTE__" + body[end:]
body_changes = [
    ('len(manifest["proved_components"]) == 847', 'len(manifest["proved_components"]) == 857', 1),
    ('len(manifest["proved_components"]) == 857 and manifest["proved_components"][-10:]', 'len(manifest["proved_components"]) == 868 and manifest["proved_components"][-11:]', 1),
    ('"baseline_hash_count": 772', '"baseline_hash_count": 782', 1),
    ('"new_theorem_count": 43', '"new_theorem_count": 44', 2),
    ('"new_selected_report_count": 47', '"new_selected_report_count": 58', 2),
    ('"new_module_count": 10', '"new_module_count": 11', 1),
    ('len(registration["new_modules"]) == 10', 'len(registration["new_modules"]) == 11', 1),
    ('"project_modules": 764', '"project_modules": 775', 1),
    ('"scanned_module_count": 773', '"scanned_module_count": 784', 1),
    ('"exact_unique_reports": 3911', '"exact_unique_reports": 3969', 1),
    ('"baseline_hashes_verified_before_registration": 772', '"baseline_hashes_verified_before_registration": 782', 1),
    ('review["new_theorem_count"] == 43', 'review["new_theorem_count"] == 44', 1),
    ('review["new_selected_report_count"] == 47', 'review["new_selected_report_count"] == 58', 1),
    ('scan["scanned_module_count"] == 773', 'scan["scanned_module_count"] == 784', 1),
    ('kernel["exact_unique_reports"] == 3911', 'kernel["exact_unique_reports"] == 3969', 1),
    ('"new_theorems": 43', '"new_theorems": 44', 1),
    ('"new_selected_declarations": 47', '"new_selected_declarations": 58', 1),
    ('"all_source_modules_scanned": 773', '"all_source_modules_scanned": 784', 1),
    ('"kernel_exact_unique_reports": 3911', '"kernel_exact_unique_reports": 3969', 1),
]
for before, after, count in body_changes:
    body = replace_exact(body, before, after, count)
body = replace_exact(body, '        "axiom_free_reports": sorted(AXIOM_FREE),\n', '        "axiom_free_reports": sorted(AXIOM_FREE),\n        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),\n        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),\n')
status_before = 'Full faithful matrix integration or Malcev comparison, rational Lie-polynomial BCH comparison outside the concrete strict-matrix realization, and specified-lattice rational subgroup cocompactness remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted.'
status_after = 'An explicit finite recursive rational original-bracket polynomial representation of the actual BCH product logarithm in arbitrary original nilpotent Lie groups is now proved by genuine polynomial Picard evaluations. Full faithful integration or Malcev comparison, quantitative degree/denominator bounds, identification of the rational structure from arbitrary specified lattices, and specified-lattice rational subgroup cocompactness remain unproved; no universal group embedding or specified-lattice cocompactness theorem is asserted.'
anchor = "    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)\n"
body = replace_exact(body, anchor, anchor + "    old_status = " + repr(status_before) + "\n    new_status = " + repr(status_after) + "\n    assert remaining.count(old_status) == 1\n    remaining = remaining.replace(old_status, new_status)\n")
note1 = "\n2026-10-10 round-native-rational-picard: PROGRESS. Eleven new modules, 44 proved theorems and 14 definitions; 58 exact new reports. All 782 baseline source/config hashes verified before registration; only retained root and registry change. Actual finite vector polynomial lists, original bilinear expansion and rational reciprocal-degree primitives give exact real evaluations of actual original defect powers, finite inverse fields and every true Picard iterate. Rational-time values remain in every actual original bracket-closed Q-linear structure without assuming it closed. The actual original product logarithm therefore preserves that structure; its exponential image is itself a subgroup. Actual finite factorial adjoint formulas give rational conjugation invariance. An explicit finite recursive rational original-bracket polynomial represents the actual global log of Exp(u)*Exp(t*w) for every real t. Specified-lattice identification/cocompactness, quantitative bounds, reverse group/Lie layer comparison, Malcev and full target remain unproved. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3969 exact unique standard-axiom reports. Retained axioms and six retained axiom-free reports unchanged; any newly axiom-free declarations are recorded separately from actual kernel output. All 775 own and nine attributed PNT+ modules plus root and registry scanned; 793 source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-rational-picard-review.json.\n\n"
body = replace_exact(body, "__CURRENT_NOTE__", "(" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")")
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "modules": len(modules), "theorems": 44, "reports": 58}))
