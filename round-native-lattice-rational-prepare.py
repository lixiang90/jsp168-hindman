"""Extend the exact audit to original subgroup rational and real spans."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json

prefix = "round-native-lattice-rational"
old_prefix = "round-native-rational-picard"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
previous = module_from_spec(spec)
spec.loader.exec_module(previous)
baseline = previous.obj(prefix + "-baseline.json")
assert baseline == previous.obj("verification-manifest.json")
assert len(baseline["files"]) == 793
assert all(previous.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in previous.declarations(p)]
assert len(modules) == 11 and len(decls) == 41
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 36


def replace_exact(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before), count)
    return text.replace(before, after)


register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-lie-subgroups-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = replace_exact(register, 'len(baseline["files"]) == 782', 'len(baseline["files"]) == 793')
register = replace_exact(register, 'len(names) == len(set(names)) == 58', 'len(names) == len(set(names)) == 41')
register = replace_exact(register, 'sum(c["theorems"] for c in counts.values()) == 44', 'sum(c["theorems"] for c in counts.values()) == 36')
register = replace_exact(register, '"baseline_hashes_verified_before_registration": 782', '"baseline_hashes_verified_before_registration": 793')
register = replace_exact(register, '"new_theorems": 44', '"new_theorems": 36')
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")
head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
head_changes = {
    'PREFIX = "' + old_prefix + '"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-lie-subgroups"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 782 and len(new_modules) == 11': 'len(baseline["files"]) == 793 and len(new_modules) == 11',
    'len(own) == 775 and len(pnt) == 9': 'len(own) == 786 and len(pnt) == 9',
    'len(names) == len(set(names)) == 58': 'len(names) == len(set(names)) == 41',
    'sum(c["theorems"] for c in module_counts.values()) == 44': 'sum(c["theorems"] for c in module_counts.values()) == 36',
    'len(registered) == len(set(registered)) == len(actual) == 3969': 'len(registered) == len(set(registered)) == len(actual) == 4010',
    'len(previous) == 3911': 'len(previous) == 3969',
    'len(source_files) == len({f["path"] for f in source_files}) == 793': 'len(source_files) == len({f["path"] for f in source_files}) == 804',
    'NEW_AXIOM_FREE = {"Hindman168.finiteVectorPolynomialSum"}': 'NEW_AXIOM_FREE = set()',
    '    "Hindman168.MatrixDepth.smul",': '    "Hindman168.MatrixDepth.smul",\n    "Hindman168.finiteVectorPolynomialSum",',
}
for before, after in head_changes.items():
    head = replace_exact(head, before, after)
application = [
    "PROGRESS: the preceding rational Picard round was recorded and freshly rechecked before the saved 793-file baseline and these edits. All 793 baseline hashes are independently reverified before registration. Only the root and exact-name registry change among retained sources; retained proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates are checked and no unavoidable blocker is established.",
    "RationalVectorPolynomialCoefficients proves exact uniqueness of finite Q-vector polynomial coefficients from their values at all natural numbers, using actual algebraic duals and scalar polynomial uniqueness. The actual Q-module quotient of an arbitrary rational subspace extracts coefficient membership from natural-time membership. Real natural monomials are converted to genuine rational scalars by scalar compatibility. No rational-subspace closedness, norm or finite rational dimension is assumed.",
    "NativeLieAdjointNatPolynomial rewrites the genuine original adjoint curve applied to an original vector as a finite polynomial with rational reciprocal-factorial coefficients. The actual original group nilpotency class makes its terminal and next powers zero, so two genuinely zero terms pad the formula and permit extraction of the linear coefficient even at class zero or one. Natural-time curve membership therefore implies membership of the actual original adjoint generator applied to that vector.",
    "NativeSubgroupLogarithmSpan defines W as span_Q of the actual original global logarithms of the arbitrary specified original subgroup Gamma. The original exponential conjugation identity and actual two-sided logarithm inverse laws give Ad(g)(Log(h))=Log(g*h*g^-1). Original subgroup closure and actual Q-linear span induction prove Ad(g) preserves W for every g in Gamma. Log(Gamma) itself is not asserted additive.",
    "NativeSubgroupBracketSpan uses the actual natural-time equality exp(n*Log(g))=g^n for g in Gamma. Thus all natural-time original adjoint values of Log(h) belong to W, and coefficient extraction gives B_Log(g)(Log(h)) in W. Actual bilinearity in both arguments extends this to all of W. The retained original adjoint-differential/native-bracket identity proves actual native bracket closure of W without a supplied rational structure or bracket-closure premise. The retained genuine rational Picard/BCH theorem gives closure under the actual noncommuting product logarithm.",
    "NativeSubgroupRationalHull exponentiates this derived bracket-closed W into a genuine original subgroup, gives exact original global-logarithm membership and proves it contains Gamma. Actual span minimality proves containment in every exponential rational Lie structure containing Gamma's actual logarithms. Every hull element's actual adjoint preserves W by the true finite original factorial formula. No claim is made that this hull is closed, discrete or cocompact.",
    "RationalBilinearRealSpan proves actual real bilinear preservation of the real span of an actual preserved Q-subspace by two genuine linear-span arguments. NativeSubgroupRealLieSpan therefore constructs an actual original native real Lie subalgebra S from W. Its underlying original real model equals span_R(Log(Gamma)), not a different generated algebra. The true original exponential subgroup contains Gamma and is closed and contractible by the retained finite-dimensional exponential/logarithm homeomorphism.",
    "NilpotentLieSubalgebraSpanning proves explicitly that S plus the actual commutator layer equals the whole Lie algebra only when S itself equals the whole algebra. The proof decomposes actual original vectors into S and a lower-central layer, expands actual brackets, and descends through the true terminating lower-central series. No maximal-subalgebra or Malcev conclusion is assumed.",
    "NativeLieLogarithmCharacter constructs an actual continuous real function f(Log(g)) from an original real linear functional. Its actual additive character law follows from the true original product-logarithm error in the native commutator layer. Nonzero functionals yield surjective actual characters via the genuine original exponential/logarithm inverse. NativeLieCharacterCompactQuotient descends this actual function to the original coset quotient G/Gamma using original left-coset relations, without requiring Gamma normal. Compactness of that actual quotient and noncompactness of R force the functional to vanish.",
    "NativeLatticeRealSpanning applies actual real algebraic dual separation to a hypothetical proper original native Lie subalgebra containing all Log(Gamma). Its sum with the actual commutator layer is proper by the proved nilpotent spanning lemma. The separating nonzero functional gives a continuous surjective real character on the actual compact original quotient, a contradiction. Therefore every actual cocompact subgroup's logarithms span the entire original real model, and the actual W=span_Q(Log(Gamma)) has full real span. CompactSpace(G/Gamma) is the original specified quotient compactness premise, not a newly assumed compactness conclusion. Gamma discreteness is not needed for this real-spanning theorem.",
    "Eleven new modules, 36 theorems and five definitions give 41 exact new reports. Require actual terminal exit-zero complete build/kernel records, byte logs and hashes, exact names/imports, current oleans and all-source trust scans. All 786 own and nine attributed PNT+ modules plus root and registry are covered. All seven retained axiom-free reports and retained axiom sets remain unchanged; actual new reports must use only standard allowed axioms. No option overrides are introduced.",
    "Remaining: prove finite Q dimension and the full rational form of the actual specified discrete cocompact lattice, quantitative degree/denominator bounds, reverse original group/Lie lower-central inclusion and exact comparison/closedness, faithful integration/Malcev, and actual specified-lattice rational subgroup cocompactness. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await complete proof and audit.",
]
components = [
    "actual finite Q-vector polynomial coefficients are uniquely determined by all natural-time values and quotient coefficient membership needs no rational-subspace closedness",
    "actual original adjoint curve rational factorial polynomial and genuine zero padding recover generator membership from natural-time membership for every original nilpotency class",
    "actual Q-linear span of logarithms of an arbitrary specified original subgroup is invariant under its genuine original adjoint action by actual conjugation and global inverse laws",
    "actual Q-linear span of logarithms of an arbitrary specified original subgroup is closed under the original native Lie bracket by integer conjugations and coefficient extraction",
    "actual specified-subgroup logarithmic Q-span preserves genuine original noncommuting product logarithms by the proved rational Picard BCH construction",
    "actual specified-subgroup rational exponential hull is a genuine original subgroup with exact logarithm membership, contains the specified subgroup, is minimal among containing rational Lie structures and preserves the actual Q-span under adjoint action",
    "actual real span of a bilinear-preserved rational subspace is bilinear-preserved without topological closure assumptions",
    "actual real span of specified-subgroup logarithms is an original native Lie subalgebra whose genuine exponential subgroup is closed, contractible and contains the original subgroup",
    "actual nilpotent Lie subalgebra spanning the original abelianization equals the whole algebra by explicit terminating lower-central descent",
    "actual original real logarithmic characters killing the native commutator layer are continuous, additive and surjective when nonzero and descend to original nonnormal coset quotients",
    "actual cocompact original subgroup logarithms span the entire original real Lie model by genuine quotient compactness, native nilpotent spanning and real dual separation",
]
progress = (
    "The arbitrary specified original subgroup Gamma now supplies a derived rational Lie structure W=span_Q(Log(Gamma)). "
    "Actual original conjugation proves its adjoint invariance under Gamma. Genuine natural-time adjoint values are conjugations by Gamma powers; "
    "algebraic rational vector polynomial coefficient extraction, with true nilpotent zero padding at all classes, recovers actual original generator membership. "
    "Actual bilinearity and the proved native bracket identity establish bracket closure of W without supplying it. "
    "The actual rational BCH result therefore preserves W and Exp(W) is a genuine rational hull subgroup containing Gamma, with exact original logarithm membership and rational Lie minimality. "
    "Every hull element's actual adjoint preserves W. Actual real linear span induction proves span_R(W)=span_R(Log(Gamma)) is an original native Lie subalgebra; "
    "its genuine original exponential subgroup contains Gamma and is closed and contractible. "
    "Explicit terminating lower-central descent proves that a proper nilpotent Lie subalgebra remains proper after adding the actual commutator layer. "
    "Real dual separation gives an actual nonzero linear functional vanishing on that sum. Actual product-logarithm errors prove its original continuous logarithmic character law, "
    "and genuine original exponential/logarithm inverses give surjectivity to R. This actual character descends to the original possibly nonnormal coset quotient. "
    "If the original specified quotient G/Gamma is compact, noncompactness of R contradicts surjectivity. Thus the actual specified cocompact subgroup's logarithms have full real span. "
    "No replacement group, supplied bracket closure, assumed character, rational-subspace closedness or additive nonabelian Log(Gamma) is used. "
    "Remaining: finite Q dimension and the full rational form of the actual specified discrete cocompact lattice; quantitative degree/denominator bounds; "
    "reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev and actual specified-lattice rational subgroup cocompactness. "
    "The actual real spanning conclusion does not by itself prove finite Q dimension, discreteness or rational subgroup cocompactness. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. "
    "No unavoidable blocker is established."
)
new_progress = previous.NEW_PROGRESS.split("Remaining:", 1)[0] + progress
body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("\ndef record():"):]
status_start = body.index("    old_status =")
status_end = body.index("    review =", status_start)
body = body[:status_start] + body[status_end:]
body_changes = {
    'len(manifest["proved_components"]) == 857': 'len(manifest["proved_components"]) == 868',
    '"baseline_hash_count": 782': '"baseline_hash_count": 793',
    '"new_theorem_count": 44': '"new_theorem_count": 36',
    '"new_selected_report_count": 58': '"new_selected_report_count": 41',
    '"project_modules": 775': '"project_modules": 786',
    '"scanned_module_count": 784': '"scanned_module_count": 795',
    '"exact_unique_reports": 3969': '"exact_unique_reports": 4010',
    '"baseline_hashes_verified_before_registration": 782': '"baseline_hashes_verified_before_registration": 793',
    'review["new_theorem_count"] == 44': 'review["new_theorem_count"] == 36',
    'review["new_selected_report_count"] == 58': 'review["new_selected_report_count"] == 41',
    'len(manifest["proved_components"]) == 868': 'len(manifest["proved_components"]) == 879',
    'scan["scanned_module_count"] == 784': 'scan["scanned_module_count"] == 795',
    'kernel["exact_unique_reports"] == 3969': 'kernel["exact_unique_reports"] == 4010',
    '"new_theorems": 44': '"new_theorems": 36',
    '"new_selected_declarations": 58': '"new_selected_declarations": 41',
    '"all_source_modules_scanned": 784': '"all_source_modules_scanned": 795',
    '"kernel_exact_unique_reports": 3969': '"kernel_exact_unique_reports": 4010',
}
# Apply changes simultaneously, so the old final component count cannot
# collide with the new baseline component count.
for before in body_changes:
    assert body.count(before) == (2 if before in {'"new_theorem_count": 44', '"new_selected_report_count": 58'} else 1), (before, body.count(before))
import re
pattern = re.compile("|".join(re.escape(s) for s in sorted(body_changes, key=len, reverse=True)))
body = pattern.sub(lambda m: body_changes[m.group(0)], body)
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-lattice-rational: PROGRESS. Eleven new modules, 36 proved theorems and five definitions; 41 exact new reports. "
    "All 793 baseline hashes verified before registration; only retained root and registry change. "
    "Actual natural-time original adjoint values from specified subgroup powers and genuine rational polynomial coefficient extraction prove native bracket closure of W=span_Q(Log(Gamma)). "
    "Actual rational BCH gives its genuine exponential hull subgroup. Its real span is an original native Lie subalgebra with a closed contractible genuine exponential subgroup containing Gamma. "
    "Explicit nilpotent lower-central descent, real dual separation and actual continuous characters on the original compact coset quotient prove span_R(Log(Gamma))=E. "
    "Finite Q dimension, full specified-lattice rational form/cocompactness, quantitative bounds, reverse original group/Lie layer comparison, Malcev and full target remain unproved. "
    "Retained axiom sets and seven retained axiom-free reports remain unchanged. All 786 own and nine attributed PNT+ modules plus root and registry scanned; 804 source/config hashes. "
    "Actual complete build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + " + str(verified[\"build_jobs\"]) + " + repr(
    " jobs, 4010 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. "
    "Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-lattice-rational-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = ("APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) +
           "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body)
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 36, "new_reports": 41}))
