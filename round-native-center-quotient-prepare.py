"""Prepare exact audit for actual original center quotient induction groundwork."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json
import re

prefix = "round-native-center-quotient"
old_prefix = "round-native-center-log"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
old = module_from_spec(spec)
spec.loader.exec_module(old)
baseline = old.obj(prefix + "-baseline.json")
assert baseline == old.obj("verification-manifest.json")
assert len(baseline["files"]) == 832
assert all(old.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in old.declarations(p)]
assert len(modules) == 10 and len(decls) == 22
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 20
assert sum(k == "def" for k, _ in decls) == 2

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
    '"round-native-root-saturation-audit.py"': ('"' + old_prefix + '-audit.py"', 1),
    'prefix = "' + old_prefix + '"': ('prefix = "' + prefix + '"', 1),
    'len(baseline["files"]) == 823': ('len(baseline["files"]) == 832', 1),
    'len(names) == len(set(names)) == 41': ('len(names) == len(set(names)) == 22', 1),
    'sum(c["theorems"] for c in counts.values()) == 34': ('sum(c["theorems"] for c in counts.values()) == 20', 1),
    '"baseline_hashes_verified_before_registration": 823': ('"baseline_hashes_verified_before_registration": 832', 1),
    '"new_theorems": 34': ('"new_theorems": 20', 1),
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
    'OLD = "round-native-root-saturation"': ('OLD = "' + old_prefix + '"', 1),
    'len(baseline["files"]) == 823 and len(new_modules) == 9': ('len(baseline["files"]) == 832 and len(new_modules) == 10', 1),
    'len(own) == 814 and len(pnt) == 9': ('len(own) == 824 and len(pnt) == 9', 1),
    'len(names) == len(set(names)) == 41': ('len(names) == len(set(names)) == 22', 1),
    'sum(c["theorems"] for c in module_counts.values()) == 34': ('sum(c["theorems"] for c in module_counts.values()) == 20', 1),
    'len(registered) == len(set(registered)) == len(actual) == 4105': ('len(registered) == len(set(registered)) == len(actual) == 4127', 1),
    'len(previous) == 4064': ('len(previous) == 4105', 1),
    'len(source_files) == len({f["path"] for f in source_files}) == 832': ('len(source_files) == len({f["path"] for f in source_files}) == 842', 1),
})
application = [
    "PROGRESS: the previous actual center logarithmic lattice round was freshly rechecked before the exact 832-file baseline was saved. All baseline proof/config bytes were independently checked before registration. Only retained root and registry change; all retained original proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates or unavoidable blocker.",
    "SubgroupFiniteIdentityNeighborhood proves an actual subgroup with finite intersection with an open identity neighborhood is discrete in its natural subtype topology. Removing the actual finitely many nonidentity subgroup points leaves an actual open singleton neighborhood. The original topological group singleton criterion gives discreteness; no quotient discreteness is supplied.",
    "NormalQuotientFiniteLatticeImage proves the actual image of a specified discrete Gamma in G/N has finite intersection with an actual quotient image of O subset compact K. For actual representatives o and gamma of the same quotient point, o^-1*gamma belongs to N. Actual compact representatives C modulo Gamma intersect N give n=c*delta. The adjusted actual representative o*c=gamma*delta^-1 lies in Gamma intersect K*C and has exactly the original quotient value because c belongs to N. This actual compact discrete intersection is finite. No compactness of Gamma itself is asserted.",
    "NormalQuotientLatticeDiscreteness constructs a genuine compact original identity neighborhood K and uses its actual open interior. The actual quotient map is open, and the previous actual finite intersection theorem applies to its image. Original closed normal N gives the natural quotient Hausdorff property, allowing the actual finite identity-neighborhood criterion to prove discreteness of the specified image Gamma. Only actual compact representatives in N are used as the general auxiliary premise.",
    "SubgroupQuotientImageMap constructs the genuine coset map G/Gamma to K/(f Gamma) induced by an actual group homomorphism f. Original left-coset relation and genuine mapped subgroup membership prove well-definedness even when Gamma is nonnormal. Actual quotient topology proves continuity for continuous f, and actual surjectivity of f proves quotient-map surjectivity. Original compact source quotient therefore gives the actual target coset quotient compactness. Neither Gamma nor f Gamma is required to be normal.",
    "NormalQuotientLatticeCocompactness applies the genuine coset map to the original quotient homomorphism G to G/N. Thus actual CompactSpace(G/Gamma) implies actual CompactSpace((G/N)/(image Gamma)) directly. It needs neither a discrete Gamma nor original topological group structure, because genuine coset quotient continuity and actual quotient homomorphism surjectivity suffice.",
    "NativeCenterCompactRepresentatives derives an actual compact center representative set for the original specified lattice from the original compact coset quotient, actual locally compact original G, actual Gamma finite generation and the previously proved equality centralizer(Gamma)=center(G). This discharges every auxiliary hypothesis rather than assuming a compact center quotient or full ambient rational form.",
    "NativeCenterQuotientLattice combines the actual center representative set with actual original local compactness and center closedness. The actual image of the specified original Gamma in original G/center(G) is genuinely discrete and cocompact in its natural quotient topology. No different lattice, replacement group or supplied quotient lattice condition is used.",
    "NativeCenterQuotientRelation proves exactly that v-w lies in the actual original real adjoint kernel V if and only if Exp(v)^-1*Exp(w) belongs to the actual original center. Central addition yields one implication. For the reverse, the true logarithm of that actual central difference lies in V; actual central exponential addition and original exponential injectivity give Log(c)+v=w. This identifies the actual quotient relations without claiming addition of general nonabelian logarithms.",
    "NativeCenterQuotientHomeomorph descends the already proved true original exponential diffeomorphism through these exactly matching original quotient relations. The constructed genuine homeomorphism E/V to G/center(G) has original exponential on actual representatives and original logarithm on inverse representatives, and sends zero to the true quotient identity. Actual real topological vector quotient contractibility transfers to the original group quotient, proving it contractible and hence simply connected. No quotient LieGroup or smooth quotient model has yet been claimed.",
    "NativeCenterQuotientDimension uses the genuine original nontrivial nilpotent center theorem and the actual center exponential homeomorphism to prove V has strictly positive real dimension. Actual real quotient rank-nullity therefore proves finrank_R(E/V)<finrank_R(E) for nontrivial original G. This supplies a genuine decreasing dimension for future central induction, not the induction result itself.",
    "Ten new modules, twenty proved theorems and two actual definitions give 22 new exact kernel reports. All 824 own and nine attributed PNT+ modules, root and registry are covered by exact full build, all-source trust scan, exact kernel-name checks and 842 source/config hashes. Require terminal exit-zero records, warning-free new sources, current new oleans, unchanged retained axiom sets and actual empty-report checks. No new options or dependency edits.",
    "Actual center quotient lattice control, actual quotient homeomorphism, contractibility, simply connectedness and strict real dimension descent are now proved. Remaining ambient rational-form induction requires the original center quotient's genuine smooth Lie structure and bracket/exponential comparison, and identification of W intersect V with the center lattice rational span. Arbitrary rational subgroup lattice cocompactness, root-saturation subgroup closure, quantitative degree/denominator bounds, reverse original group/Lie comparison, faithful integration/Malcev, full calibration/Alignment and positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await full proof and audit.",
]
components = [
    "actual finite identity-neighborhood intersection proves subgroup discreteness by deleting the genuine finite nonidentity set",
    "actual original compact representative adjustment proves finite quotient lattice image intersection without assuming quotient discreteness",
    "actual closed normal subgroup compact intersection representatives yield genuine natural quotient lattice image discreteness",
    "actual continuous surjective group homomorphisms induce genuine continuous surjective nonnormal coset quotient maps and transfer compactness",
    "actual original specified compact lattice quotient descends to the genuine normal quotient lattice-image coset space",
    "actual original center compact representatives are derived from specified lattice compactness, finite generation and genuine centralizer equality",
    "actual specified original lattice image in the original center quotient is discrete and cocompact in its natural topology",
    "actual original center coset equivalence is exactly original exponential-coordinate difference membership in the real adjoint kernel",
    "actual original center quotient is homeomorphic to the real center-model quotient by the true descended exponential and logarithm and is contractible and simply connected",
    "actual original nontrivial nilpotency forces positive real center dimension and strictly smaller actual center quotient model dimension",
]
progress = (
    "The actual image of the original specified lattice Gamma in G/center(G) is now genuinely discrete and cocompact in the original natural quotient topology. "
    "An actual compact original identity neighborhood and actual center representatives modulo Gamma intersect center(G) adjust each original projected Gamma element to an original Gamma representative in a genuine compact product. "
    "Finiteness of the actual discrete compact intersection, actual quotient openness and deletion of actual finite nonidentity points prove quotient lattice discreteness. "
    "The actual continuous surjective coset map from G/Gamma to (G/center(G))/(image Gamma) proves its actual compactness without requiring Gamma normal. "
    "Every actual center compact representative hypothesis is derived from original lattice compactness, original local compactness, actual Gamma finite generation and the genuine original centralizer equality. "
    "Actual original exponential central addition and actual original exponential injectivity prove exact original coset relation equivalence: v-w lies in V if and only if Exp(v)^-1*Exp(w) lies in center(G). "
    "Therefore the genuine original exponential diffeomorphism descends to a constructed actual homeomorphism E/V to G/center(G), with actual exponential and actual logarithm formulas on all original representatives and zero sent to the quotient identity. "
    "The actual real topological vector quotient is contractible, so the actual original center quotient is contractible and simply connected. "
    "Original nontrivial nilpotency gives a nontrivial actual center; its actual exponential homeomorphism gives positive real dimension of V, and actual quotient rank-nullity proves strict real model dimension descent. "
    "No actual quotient LieGroup, smooth quotient chart, quotient bracket identification, full rational-form induction or additive nonabelian Log(Gamma) is supplied or asserted. "
    "Remaining: construct the original center quotient genuine smooth Lie model and prove its bracket/exponential comparison for full ambient scalar-extension injectivity and specified-lattice rational-form induction; "
    "identify W intersect V with the actual specified center lattice rational span; arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; "
    "reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
new_progress = old.NEW_PROGRESS.split("Remaining:", 1)[0] + progress
body = old.read(old_prefix + "-audit.py")
body = body[body.index("\ndef record():"):]
body = simultaneous(body, {
    'len(manifest["proved_components"]) == 898': ('len(manifest["proved_components"]) == 907', 1),
    '"baseline_hash_count": 823': ('"baseline_hash_count": 832', 1),
    '"new_theorem_count": 34': ('"new_theorem_count": 20', 2),
    '"new_selected_report_count": 41': ('"new_selected_report_count": 22', 2),
    '"new_module_count": 9': ('"new_module_count": 10', 1),
    '"project_modules": 814': ('"project_modules": 824', 1),
    '"scanned_module_count": 823': ('"scanned_module_count": 833', 1),
    '"exact_unique_reports": 4105': ('"exact_unique_reports": 4127', 1),
    '"baseline_hashes_verified_before_registration": 823': ('"baseline_hashes_verified_before_registration": 832', 1),
    'review["new_theorem_count"] == 34': ('review["new_theorem_count"] == 20', 1),
    'review["new_selected_report_count"] == 41': ('review["new_selected_report_count"] == 22', 1),
    'len(manifest["proved_components"]) == 907': ('len(manifest["proved_components"]) == 917', 1),
    'manifest["proved_components"][-9:]': ('manifest["proved_components"][-10:]', 1),
    'len(registration["new_modules"]) == 9': ('len(registration["new_modules"]) == 10', 1),
    'scan["scanned_module_count"] == 823': ('scan["scanned_module_count"] == 833', 1),
    'kernel["exact_unique_reports"] == 4105': ('kernel["exact_unique_reports"] == 4127', 1),
    '"new_theorems": 34': ('"new_theorems": 20', 1),
    '"new_selected_declarations": 41': ('"new_selected_declarations": 22', 1),
    '"all_source_modules_scanned": 823': ('"all_source_modules_scanned": 833', 1),
    '"kernel_exact_unique_reports": 4105': ('"kernel_exact_unique_reports": 4127', 1),
})
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-center-quotient: PROGRESS. Ten new modules, twenty proved theorems and two definitions; 22 exact new reports. "
    "All 832 baseline hashes verified before registration; only retained root/registry change. Actual original compact center representatives adjust projected Gamma elements to genuine original compact discrete intersections. "
    "Actual finite quotient identity-neighborhood intersection proves genuine discreteness of the specified original lattice image in original G/center(G). "
    "Actual continuous surjective nonnormal coset quotient maps transfer the original lattice quotient compactness, giving actual quotient lattice cocompactness. "
    "Actual original center cosets coincide exactly with real adjoint-kernel vector differences. The true original exponential diffeomorphism descends to an actual E/V to G/center(G) homeomorphism with genuine representative formulas. "
    "Actual real quotient contractibility proves the original center quotient contractible and simply connected. Original nontrivial nilpotency gives positive real center dimension and strict quotient model dimension descent. "
    "Original quotient smooth Lie structure and comparison, full ambient rational form induction, W intersect V equality, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. "
    "Retained axiom sets and eleven retained axiom-free reports are unchanged; actual new empty reports separately checked. All 824 own and nine attributed PNT+ modules plus root/registry scanned; 842 source/config hashes. Actual full build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + ' + str(verified["build_jobs"]) + ' + repr(
    " jobs, 4127 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-quotient-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 20, "new_reports": 22}))
