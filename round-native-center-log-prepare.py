"""Prepare exact audit for actual center logarithmic lattice and rational basis."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json
import re

prefix = "round-native-center-log"
old_prefix = "round-native-root-saturation"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
old = module_from_spec(spec)
spec.loader.exec_module(old)
baseline = old.obj(prefix + "-baseline.json")
assert baseline == old.obj("verification-manifest.json")
assert len(baseline["files"]) == 823
assert all(old.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in old.declarations(p)]
assert len(modules) == 9 and len(decls) == 41
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 34
assert sum(k == "def" for k, _ in decls) == 7


def exact(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before), count)
    return text.replace(before, after)


def simultaneous(text, changes):
    for before, (after, count) in changes.items():
        assert text.count(before) == count, (before, text.count(before), count)
    pattern = re.compile("|".join(re.escape(s) for s in sorted(changes, key=len, reverse=True)))
    return pattern.sub(lambda m: changes[m.group(0)][0], text)


register = old.read(old_prefix + "-register.py")
register = simultaneous(register, {
    '"round-native-lattice-finite-audit.py"': ('"' + old_prefix + '-audit.py"', 1),
    'prefix = "' + old_prefix + '"': ('prefix = "' + prefix + '"', 1),
    'len(baseline["files"]) == 813': ('len(baseline["files"]) == 823', 1),
    'len(names) == len(set(names)) == 25': ('len(names) == len(set(names)) == 41', 1),
    'sum(c["theorems"] for c in counts.values()) == 25': ('sum(c["theorems"] for c in counts.values()) == 34', 1),
    '"baseline_hashes_verified_before_registration": 813': ('"baseline_hashes_verified_before_registration": 823', 1),
    '"new_theorems": 25': ('"new_theorems": 34', 1),
})
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
Path(prefix + "-build.py").write_text(exact(old.read(old_prefix + "-build.py"), old_prefix, prefix), encoding="utf-8")
head = old.read(old_prefix + "-audit.py").split("\nAPPLICATION =", 1)[0]
assert old.NEW_AXIOM_FREE == set() and len(old.AXIOM_FREE) == 11
head = simultaneous(head, {
    'PREFIX = "' + old_prefix + '"': ('PREFIX = "' + prefix + '"', 1),
    'OLD = "round-native-lattice-finite"': ('OLD = "' + old_prefix + '"', 1),
    'len(baseline["files"]) == 813 and len(new_modules) == 10': ('len(baseline["files"]) == 823 and len(new_modules) == 9', 1),
    'len(own) == 805 and len(pnt) == 9': ('len(own) == 814 and len(pnt) == 9', 1),
    'len(names) == len(set(names)) == 25': ('len(names) == len(set(names)) == 41', 1),
    'sum(c["theorems"] for c in module_counts.values()) == 25': ('sum(c["theorems"] for c in module_counts.values()) == 34', 1),
    'len(registered) == len(set(registered)) == len(actual) == 4064': ('len(registered) == len(set(registered)) == len(actual) == 4105', 1),
    'len(previous) == 4039': ('len(previous) == 4064', 1),
    'len(source_files) == len({f["path"] for f in source_files}) == 823': ('len(source_files) == len({f["path"] for f in source_files}) == 832', 1),
})
application = [
    "PROGRESS: the previous actual original center lattice round was freshly rechecked before the exact 823-file baseline was saved. Independently verified every baseline byte hash before registration. Only retained root and registry change; retained original proofs, full statement, dependency pins and attributed sources remain unchanged. No remote updates or unavoidable blocker.",
    "NativeLieCenterModel constructs V as the actual original adjoint differential kernel in E. Its membership is equivalent to zero actual adjoint generator and to vanishing original native brackets against every original vector. The retained true original exponential commuting detection identifies Exp(v) in center(G) exactly with v in V, and the actual original global logarithm preserves this membership. Original generator zero gives the genuine additive exponential law whenever the first direction lies in V.",
    "NativeLieCenterExponential constructs the actual natural subtype homeomorphism V to center(G) using the retained actual smooth original exponential and actual continuous global logarithm with both proved inverse laws. It proves true original central product logarithms add, and the actual restricted exponential and logarithm preserve the corresponding operations. Genuine convex contractibility of the original V transfers to the actual original center. No center model or homeomorphism is supplied as a premise.",
    "NativeCenterLogLattice constructs an actual additive subgroup of original V by actual specified Gamma membership of Exp(v). Genuine central additivity, zero and negation laws supply subgroup closure, hence its actual integer submodule. The actual center logarithm membership is precisely original Gamma membership. Its genuine continuous injective map through the original exponential to actual discrete Gamma proves natural logarithmic integer lattice discreteness. Additivity is restricted to the actual center, not asserted for nonabelian Log(Gamma).",
    "NativeCenterLogQuotient constructs the actual center quotient logarithm into V/L. Original coset equality gives an actual Gamma-center difference; its genuine additive center logarithm lies in L and proves well-definedness. The original continuous quotient map and actual center logarithm prove genuine continuity. The actual exponential inverse gives surjectivity onto the full additive quotient. The previously proved actual center quotient compactness therefore yields CompactSpace(V/L). No quotient compactness is assumed beyond the original ambient specified-lattice compactness.",
    "IntegerCocompactRealSpan proves compactness of the natural integer-submodule additive quotient forces full real span. A proper actual real span yields an actual nonzero real linear functional annihilating L. Its true integer-linear quotient map is continuous by actual finite-dimensional linear continuity and surjects onto R by scaling an actual nonzero functional value. Noncompactness of R contradicts actual quotient compactness. Discreteness additionally gives the genuine full IsZLattice property, not a supplied full-span premise.",
    "NativeCenterLogSpanning applies this actual quotient argument to the original V and actual specified center logarithmic lattice. Thus L spans the entire original real center model and is a genuine full discrete integer lattice. The pinned Mathlib lattice rank theorem yields actual integer lattice rank equal to the original real center dimension. No real Q-basis independence is inferred merely from finite Q dimension and ambient real spanning.",
    "IntegerLatticeRationalBasis constructs a genuine integer lattice basis of index Fin(finrank_R(E)) from actual lattice rank, then the pinned Mathlib ofZLatticeBasis theorem gives a real basis with the same actual lattice vectors. Its integer span is exactly L. Genuine scalar-tower span equality proves its rational span equals the actual Q-span of L. Restricting actual real linear independence gives a genuine rational basis inside that actual Q-span. Its original columns coincide exactly with the real basis columns, proving true real independence, finite Q dimension and equality of actual Q-rank and real ambient dimension.",
    "NativeCenterRationalBasis defines the actual rational span of the actual specified center logarithmic lattice and instantiates the preceding construction. It is genuinely finite dimensional over Q, its dimension equals the actual original real center dimension, and it has a constructed Q-basis whose actual original center-model vectors are real linearly independent. This establishes the rational form for the actual center lattice, not for the entire original nonabelian lattice.",
    "NativeCenterRationalInclusion proves the exact original E-valued image of L is Log(Gamma intersect center(G)). Genuine map-span equality identifies the actual E-valued image of the central rational span with the Q-span of precisely these original logarithms. It embeds in the retained actual W=span_Q(Log(Gamma)). Actual full real center-lattice spanning gives span_R(Log(Gamma intersect center(G)))=V. No equality between this central Q-span and all central vectors in W is asserted.",
    "Nine new modules, 34 theorems and seven definitions give 41 exact new reports. Require actual terminal exit-zero full build and kernel records, exact names/imports, all-source trust scans, current new oleans, unchanged retained axiom sets and eleven retained axiom-free reports. All 814 own and nine attributed PNT+ modules plus root and registry are covered; 832 source/config hashes. New axiom-free reports are checked against actual kernel output. No new option overrides, supplied proof placeholders or dependency edits.",
    "The actual center now has a constructed full rational form from its actual specified intersection lattice and a real-independent Q-basis. Full ambient lattice rational form still requires central induction: identification of W intersect V with this actual center rational span and original quotient lattice/control remain unproved. Arbitrary rational subgroup lattice cocompactness, root-saturation subgroup closure, quantitative degree/denominator bounds, reverse original group/Lie comparison, faithful integration/Malcev, full calibration/Alignment and ordered positive arithmetic witnesses remain. StrongConjecture and the full prize target are unproved; publication/submission await full proof and audit.",
]
components = [
    "actual original real Lie center model is the genuine adjoint differential kernel and exponentiates exactly to the original group center",
    "actual original center exponential and logarithm give a constructed natural subtype homeomorphism with genuine additive central laws and contractibility",
    "actual specified center lattice logarithms form a genuine discrete integer submodule through original central exponential closure and true continuous injectivity",
    "actual original natural center quotient logarithm is continuous and surjective onto the true additive logarithmic lattice quotient, transferring proved compactness",
    "actual compact integer-submodule quotients force full real span by genuine quotient functional continuity and real noncompactness",
    "actual specified original center logarithmic lattice spans the original real center and has integer rank equal to the actual original real center dimension",
    "actual full discrete integer lattices yield constructed compatible real and rational bases, true real independence and rational rank equal to real dimension",
    "actual specified center logarithmic rational span has a constructed full rational form and a real-independent Q-basis of actual center dimension",
    "actual center rational coordinates identify with original Gamma-center logarithms inside E, embed in original W and have full real center span",
]
progress = (
    "The actual original Lie center is now represented by the true adjoint differential kernel V in original E, with actual membership equivalent to vanishing original native brackets. "
    "True original exponential and global logarithm identify V with the actual original group center through a constructed natural subtype homeomorphism. "
    "The genuine original central product logarithm adds, the restricted exponential preserves addition, and actual convex contractibility transfers to the original center. "
    "The specified actual Gamma therefore gives a genuine integer submodule L in V consisting exactly of the true center lattice logarithms. "
    "Actual original central additivity and negation prove L closure, and the genuine continuous injective original exponential into discrete Gamma proves L discrete. "
    "Actual original center coset differences and genuine logarithm addition construct a true continuous surjective map from center(G)/(Gamma intersect center(G)) to V/L. "
    "The retained actual center quotient compactness thus proves the original additive quotient V/L compact. "
    "An actual nonzero real functional annihilating a hypothetically proper real span of L would descend to a genuine continuous surjective quotient map V/L to R, contradicting original compactness. "
    "Consequently actual L spans the full original V and is a true full discrete integer lattice. The pinned Mathlib actual lattice rank theorem gives integer rank equal to original real center dimension. "
    "An actual integer basis, actual ofZLatticeBasis construction and genuine scalar restriction produce compatible integer, rational and real bases. "
    "The constructed actual Q-span basis has exactly the original real basis columns, so it is real linearly independent; its actual rational dimension equals the original real center dimension. "
    "This constructs the actual specified center lattice rational form without supplying rationality, basis independence or restricted compactness. "
    "Its actual E-valued integer image is exactly Log(Gamma intersect center(G)), its rational image is the Q-span of these true original logarithms and is contained in actual W, and its real span is exactly V. "
    "No additive property of nonabelian Log(Gamma) is asserted. "
    "Remaining: full ambient real scalar-extension injectivity and specified-lattice rational form via actual central induction, including identification of W intersect V with this constructed actual center rational span and original quotient lattice control; "
    "arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
new_progress = old.NEW_PROGRESS.split("Remaining:", 1)[0] + progress
body = old.read(old_prefix + "-audit.py")
body = body[body.index("\ndef record():"):]
body = simultaneous(body, {
    'len(manifest["proved_components"]) == 888': ('len(manifest["proved_components"]) == 898', 1),
    '"baseline_hash_count": 813': ('"baseline_hash_count": 823', 1),
    '"new_theorem_count": 25': ('"new_theorem_count": 34', 2),
    '"new_selected_report_count": 25': ('"new_selected_report_count": 41', 2),
    '"new_module_count": 10': ('"new_module_count": 9', 1),
    '"project_modules": 805': ('"project_modules": 814', 1),
    '"scanned_module_count": 814': ('"scanned_module_count": 823', 1),
    '"exact_unique_reports": 4064': ('"exact_unique_reports": 4105', 1),
    '"baseline_hashes_verified_before_registration": 813': ('"baseline_hashes_verified_before_registration": 823', 1),
    'review["new_theorem_count"] == 25': ('review["new_theorem_count"] == 34', 1),
    'review["new_selected_report_count"] == 25': ('review["new_selected_report_count"] == 41', 1),
    'len(manifest["proved_components"]) == 898': ('len(manifest["proved_components"]) == 907', 1),
    'manifest["proved_components"][-10:]': ('manifest["proved_components"][-9:]', 1),
    'len(registration["new_modules"]) == 10': ('len(registration["new_modules"]) == 9', 1),
    'scan["scanned_module_count"] == 814': ('scan["scanned_module_count"] == 823', 1),
    'kernel["exact_unique_reports"] == 4064': ('kernel["exact_unique_reports"] == 4105', 1),
    '"new_theorems": 25': ('"new_theorems": 34', 1),
    '"new_selected_declarations": 25': ('"new_selected_declarations": 41', 1),
    '"all_source_modules_scanned": 814': ('"all_source_modules_scanned": 823', 1),
    '"kernel_exact_unique_reports": 4064': ('"kernel_exact_unique_reports": 4105', 1),
})
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-center-log: PROGRESS. Nine new modules, 34 proved theorems and seven definitions; 41 exact new reports. "
    "All 823 baseline hashes verified before registration; only retained root/registry change. Actual original center is the genuine adjoint kernel, with true restricted exponential homeomorphism and additive central product logarithms. "
    "Actual center logarithmic lattice is a genuine discrete integer submodule. True continuous surjective original center quotient logarithm proves its additive quotient compact. Actual quotient linear functionals and real noncompactness force full real center span. "
    "Genuine integer lattice rank and compatible actual integer/rational/real basis constructions give the true center rational form with a real-independent Q-basis. Its actual original E-image identifies precisely with the Q-span of original Gamma-center logarithms and embeds in W. "
    "Full ambient central induction, W intersect V equality, original quotient lattice control, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. "
    "Eleven retained axiom-free reports and all retained axiom sets unchanged; actual new empty reports separately checked. All 814 own and nine attributed PNT+ modules plus root/registry scanned; 832 source/config hashes. Actual full build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + ' + str(verified["build_jobs"]) + ' + repr(
    " jobs, 4105 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-log-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 34, "new_reports": 41}))
