"""Prepare exact audit for actual original smooth center quotient."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json
import re

prefix = "round-native-center-smooth"
old_prefix = "round-native-center-quotient"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
old = module_from_spec(spec)
spec.loader.exec_module(old)
baseline = old.obj(prefix + "-baseline.json")
assert baseline == old.obj("verification-manifest.json")
assert len(baseline["files"]) == 842
assert all(old.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in old.declarations(p)]
assert len(modules) == 8 and len(decls) == 25
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 15
assert sum(k == "def" for k, _ in decls) == 9 and sum(k == "instance" for k, _ in decls) == 1

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
    '"round-native-center-log-audit.py"': ('"' + old_prefix + '-audit.py"', 1),
    'prefix = "' + old_prefix + '"': ('prefix = "' + prefix + '"', 1),
    'len(baseline["files"]) == 832': ('len(baseline["files"]) == 842', 1),
    'len(names) == len(set(names)) == 22': ('len(names) == len(set(names)) == 25', 1),
    'sum(c["theorems"] for c in counts.values()) == 20': ('sum(c["theorems"] for c in counts.values()) == 15', 1),
    '"baseline_hashes_verified_before_registration": 832': ('"baseline_hashes_verified_before_registration": 842', 1),
    '"new_theorems": 20': ('"new_theorems": 15', 1),
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
    'OLD = "round-native-center-log"': ('OLD = "' + old_prefix + '"', 1),
    'len(baseline["files"]) == 832 and len(new_modules) == 10': ('len(baseline["files"]) == 842 and len(new_modules) == 8', 1),
    'len(own) == 824 and len(pnt) == 9': ('len(own) == 832 and len(pnt) == 9', 1),
    'len(names) == len(set(names)) == 22': ('len(names) == len(set(names)) == 25', 1),
    'sum(c["theorems"] for c in module_counts.values()) == 20': ('sum(c["theorems"] for c in module_counts.values()) == 15', 1),
    'len(registered) == len(set(registered)) == len(actual) == 4127': ('len(registered) == len(set(registered)) == len(actual) == 4152', 1),
    'len(previous) == 4105': ('len(previous) == 4127', 1),
    'len(source_files) == len({f["path"] for f in source_files}) == 842': ('len(source_files) == len({f["path"] for f in source_files}) == 850', 1),
})
application = [
    "PROGRESS: previous actual original center quotient round was freshly independently rechecked before the exact 842-file baseline was saved. Every retained source/config hash is independently verified before registration. Only retained root and registry change; retained original proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates or unavoidable blocker.",
    "ClosedFiniteRealQuotientSection constructs an actual continuous real-linear quotient projection and an actual continuous real-linear section of a finite real submodule quotient. Actual module projectivity yields an algebraic right inverse of the actual mkQ surjection. Actual finite dimension proves this right inverse continuous; its actual linear composition equality gives its pointwise right-inverse law. No linear section, complement or smoothness is supplied as a premise.",
    "NativeCenterQuotientNormedModel proves the actual real adjoint kernel V is closed by the true continuous adjoint differential kernel theorem. The original quotient E/V therefore has its actual canonical separated normed real vector structure with its existing original quotient topology. Actual projection and section instantiate the genuine finite quotient construction and satisfy its exact right-inverse law. No replacement quotient vector space is introduced.",
    "HomeomorphSingletonDiffeomorph constructs a single global chart on the actual target topology of a genuine normed-model homeomorphism. The actual inverse open embedding supplies the singleton chart and actual smooth manifold proof. Its genuine coordinate composition identity proves the forward map smooth and the actual global chart is smooth in reverse, giving an actual diffeomorphism. This generic construction does not assume any target algebraic operation smooth. Named chart definitions are reducible class definitions; no new options are introduced.",
    "NativeCenterQuotientCharted applies that construction to the retained actual original exponential quotient homeomorphism. Actual original G/center(G), with its original quotient group and topology, gets the constructed singleton C-infinity chart over the actual original E/V. The actual quotient exponential and logarithm give a genuine diffeomorphism for this chart. No original quotient LieGroup structure is a premise.",
    "NativeCenterQuotientSmoothProjection proves the actual original center projection smooth through its exact original representative formula: q(g)=e(pi(Log(g))). The retained true original global logarithm is smooth, actual pi is continuous linear and smooth, and e is the constructed actual quotient diffeomorphism. Original Exp(Log(g))=g proves the formula, so the actual homomorphism q itself is smooth, not an unrelated coordinate surrogate.",
    "NativeCenterQuotientSmoothLift constructs a genuine global lift s of the original center quotient by actual Log quotient coordinates, the actual constructed linear section and true original exponential. The actual section right-inverse law and exact quotient exponential representative formula prove q(s(x))=x for every original quotient point. Actual diffeomorphism inverse, actual continuous linear section and original smooth exponential prove s smooth. No group homomorphism property of s is asserted.",
    "NativeCenterQuotientLieGroup proves actual original quotient multiplication and inversion smooth by lifting actual quotient arguments through the constructed smooth s, using the original genuine Lie group operations, and projecting with the actual smooth quotient homomorphism q. The true original homomorphism laws and q(s(x))=x identify those actual composite maps with the original quotient group operations. Actual constructed manifold, actual multiplication smoothness and actual inversion smoothness therefore give a genuine LieGroup structure on original G/center(G). It is not a replacement BCH group or a supplied quotient LieGroup assumption.",
    "NativeCenterQuotientDifferential proves the genuine lift preserves the actual quotient identity. Differentiating the actual global right-inverse identity q composed with s=id at the actual quotient identity gives a true right inverse for the actual original quotient differential Dq at original 1. That actual continuous linear right inverse proves Dq surjective. Exact identification of Dq with pi, its kernel with V, bracket comparison and quotient native exponential comparison are not asserted yet.",
    "Eight new modules, fifteen proved theorems, nine constructed definitions and one proved closedness instance give 25 exact new kernel reports. All 832 own and nine attributed PNT+ modules, root and registry are covered by exact full build, all-source trust scan and exact kernel-name checks; 850 source/config hashes. Require terminal exit-zero records, warning-free new sources, current new oleans, unchanged retained axiom sets and actual empty-report checks. No new options, sorry/admit or dependency edits.",
    "Original center quotient smooth Lie structure, actual smooth projection, actual smooth global lift and actual quotient differential surjectivity are now proved, together with retained actual quotient lattice discreteness/cocompactness, contractibility/simply connectedness and strict dimension descent. Remaining: exact differential/center-kernel identification and actual bracket/exponential comparison for full original ambient rational-form induction, including W intersect V equal to the actual center lattice rational span. Arbitrary rational subgroup lattice cocompactness, root-saturation subgroup closure, quantitative degree/denominator bounds, reverse original group/Lie comparison, faithful integration/Malcev, full calibration/Alignment and positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await full proof and audit.",
]
components = [
    "actual finite real submodule quotient projection has a constructed continuous real-linear right inverse from genuine projectivity and finite dimension",
    "actual original real adjoint-kernel center model is closed and gives the canonical normed original quotient with constructed actual linear section",
    "actual homeomorphisms from a normed real model construct genuine global singleton smooth charts and actual diffeomorphisms without assuming target operation smoothness",
    "actual original center quotient carries a constructed global C-infinity chart and true exponential/logarithm quotient diffeomorphism in its original topology",
    "actual original center projection is smooth by the genuine global logarithm, actual linear quotient projection and constructed actual quotient diffeomorphism formula",
    "actual original center quotient admits a constructed genuine smooth global lift which is a proved right inverse of the original center projection",
    "actual original center quotient multiplication and inversion are smooth through original lifted operations, yielding a genuine constructed original quotient LieGroup structure",
    "actual original smooth center projection differential has a genuine continuous linear right inverse at identity and is surjective",
]
new_progress = (
    "Retained genuine original native exponential/logarithm diffeomorphism, rational finite BCH/Picard construction, actual W bracket closure, actual full real logarithmic span and actual Gamma finite generation remain proved for the arbitrary original specified lattice. "
    "Retained actual center logarithmic integer lattice is discrete and full, with compact additive quotient, compatible integer/rational/real bases and real-independent actual center Q-basis. "
    "Retained original center quotient lattice image is discrete and cocompact, original E/V is homeomorphic to original G/center(G), and that original quotient is contractible and simply connected with strictly lower real model dimension for nontrivial G. "
    "Now the actual real center model V is proved closed as the genuine continuous adjoint kernel, giving the canonical separated normed original real quotient E/V with its original topology. "
    "Actual projectivity and finite dimension construct a genuine continuous linear section of its actual mkQ projection and prove the exact right-inverse law. "
    "The actual original exponential quotient homeomorphism supplies a constructed global singleton C-infinity chart on original G/center(G), with an actual quotient exponential/logarithm diffeomorphism. "
    "The exact actual formula q(g)=e(pi(Log(g))) proves the original center projection smooth. "
    "Actual quotient inverse coordinates, actual constructed linear section and genuine original exponential construct a global smooth original quotient lift s, and actual representative formulas prove q(s(x))=x at every actual quotient point. "
    "Lifting actual quotient arguments, performing the original smooth group operations and projecting by actual smooth q prove the original quotient multiplication and inversion smooth, hence construct a genuine original quotient LieGroup structure. "
    "The actual lift preserves identity, and differentiating its genuine right-inverse law gives a genuine continuous linear right inverse of the actual original quotient differential at original 1, proving that differential surjective. "
    "No replacement group, different lattice, supplied quotient smoothness, supplied linear section, group homomorphism property of the lift or additive nonabelian logarithm is assumed. "
    "Remaining: identify the exact actual original quotient differential with the original real quotient projection and its kernel with V, and prove actual native quotient bracket/exponential comparison for full ambient scalar-extension injectivity and specified-lattice rational-form induction; "
    "identify W intersect V with the actual specified center lattice rational span; arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; "
    "reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
body = old.read(old_prefix + "-audit.py")
body = body[body.index("\ndef record():"):]
body = simultaneous(body, {
    'len(manifest["proved_components"]) == 907': ('len(manifest["proved_components"]) == 917', 1),
    '"baseline_hash_count": 832': ('"baseline_hash_count": 842', 1),
    '"new_theorem_count": 20': ('"new_theorem_count": 15', 2),
    '"new_selected_report_count": 22': ('"new_selected_report_count": 25', 2),
    '"new_module_count": 10': ('"new_module_count": 8', 1),
    '"project_modules": 824': ('"project_modules": 832', 1),
    '"scanned_module_count": 833': ('"scanned_module_count": 841', 1),
    '"exact_unique_reports": 4127': ('"exact_unique_reports": 4152', 1),
    '"baseline_hashes_verified_before_registration": 832': ('"baseline_hashes_verified_before_registration": 842', 1),
    'review["new_theorem_count"] == 20': ('review["new_theorem_count"] == 15', 1),
    'review["new_selected_report_count"] == 22': ('review["new_selected_report_count"] == 25', 1),
    'len(manifest["proved_components"]) == 917': ('len(manifest["proved_components"]) == 925', 1),
    'manifest["proved_components"][-10:]': ('manifest["proved_components"][-8:]', 1),
    'len(registration["new_modules"]) == 10': ('len(registration["new_modules"]) == 8', 1),
    'scan["scanned_module_count"] == 833': ('scan["scanned_module_count"] == 841', 1),
    'kernel["exact_unique_reports"] == 4127': ('kernel["exact_unique_reports"] == 4152', 1),
    '"new_theorems": 20': ('"new_theorems": 15', 1),
    '"new_selected_declarations": 22': ('"new_selected_declarations": 25', 1),
    '"all_source_modules_scanned": 833': ('"all_source_modules_scanned": 841', 1),
    '"kernel_exact_unique_reports": 4127': ('"kernel_exact_unique_reports": 4152', 1),
})
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-center-smooth: PROGRESS. Eight new modules, fifteen proved theorems, nine definitions and one proved closedness instance; 25 exact new reports. "
    "All 842 baseline hashes verified before registration; only retained root/registry change. Actual original center model is closed, and the canonical normed real quotient has a constructed actual continuous linear section. "
    "Actual original quotient exponential homeomorphism constructs a genuine global smooth chart and quotient diffeomorphism. Original q(g)=e(pi(Log(g))) proves actual center projection smooth. "
    "Actual section and original exponential construct a genuine smooth global quotient lift with a proved actual projection right-inverse law. "
    "Lifting actual arguments, using original Lie group operations and projecting smoothly proves the original quotient multiplication and inversion smooth, giving the actual original quotient LieGroup structure. "
    "Actual lift preserves identity, and actual differential right-inverse law proves original quotient differential surjectivity. "
    "Exact differential/center-kernel identification, actual native bracket/exponential comparison, full ambient rational-form induction, W intersect V equality, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. "
    "All retained axiom sets and eleven retained axiom-free reports unchanged; new empty reports independently checked. All 832 own and nine attributed PNT+ modules plus root/registry scanned; 850 source/config hashes. Actual full build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + ' + str(verified["build_jobs"]) + ' + repr(
    " jobs, 4152 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-smooth-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 15, "new_reports": 25}))
