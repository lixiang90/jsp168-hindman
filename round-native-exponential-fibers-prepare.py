from pathlib import Path
import ast
import json
import re

prefix = "round-native-exponential-fibers"
old_prefix = "round-native-local-inverse"
modules = ["Hindman168/" + name + ".lean" for name in [
    "VectorPolynomialNatUniqueness", "NilpotentBanachExponentialInjective",
    "NativeLieExponentialFiberGenerators", "NativeLieExponentialCommutingAdd",
    "NativeLieExponentialPeriods", "NativeLieExponentialRangeCovering",
]]

def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)

register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-dexp-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = re.sub(r"\b(?:747|40|35)\b", lambda m: {"747": "753", "40": "27", "35": "25"}[m[0]], register)
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")

head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-local-inverse"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-dexp"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 747 and len(new_modules) == 6': 'len(baseline["files"]) == 753 and len(new_modules) == 6',
    'len(own) == 735 and len(pnt) == 9': 'len(own) == 741 and len(pnt) == 9',
    'len(names) == len(set(names)) == 40': 'len(names) == len(set(names)) == 27',
    'sum(c["theorems"] for c in module_counts.values()) == 35': 'sum(c["theorems"] for c in module_counts.values()) == 25',
    'len(registered) == len(set(registered)) == len(actual) == 3772': 'len(registered) == len(set(registered)) == len(actual) == 3799',
    'len(previous) == 3732': 'len(previous) == 3772',
    'len(source_files) == len({f["path"] for f in source_files}) == 753': 'len(source_files) == len({f["path"] for f in source_files}) == 759',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)

application = [
    "PROGRESS: the preceding authoritative proof round was freshly rechecked before the new baseline and edits. All 753 baseline source/config hashes are verified before registration. Retained proof sources, StrongStatement, pins and attribution stay unchanged; only root imports and the exact-name registry change among retained sources. No official or remote updates are checked. No unavoidable blocker is established.",
    "VectorPolynomialNatUniqueness proves a genuine finite real vector polynomial is determined coefficient by coefficient by all its natural-number values. Actual algebraic duals reduce it to true scalar polynomial equality on the infinite injective natural-number set. The exact vector coefficient equality follows from actual dual separation; no vector polynomial identity is assumed.",
    "NilpotentBanachExponentialInjective derives the actual real finite exponential curve by vanishing of every term beyond the genuine nilpotent cutoff. If two actual Banach exponentials are equal, their actual natural-number powers are equal, hence the finite curves agree at every natural number. The proved vector polynomial coefficient uniqueness at degree one recovers the original elements. A common cutoff of max(ka,kb)+2 includes degree one even in a trivial algebra. The two elements are not assumed to commute; no logarithm or matrix model is supplied.",
    "NativeLieExponentialFiberGenerators applies this true Banach exponential injectivity to the actual original adjoint generators, whose nilpotency is already proved at the original group nilpotencyClass. Equal original exponential values imply equal actual generators, zero generator for their difference, zero original native bracket between the two vectors, and zero bracket of their difference with every original vector. Actual native tangent aliases are aligned with canonical original model variables without options or transparency changes.",
    "NativeLieExponentialCommutingAdd uses the true original global adjoint differential equation to show a vector killed by the actual generator is fixed by the actual entire adjoint curve. Original conjugation then proves the two actual one-parameter curves commute at all independent times. Their genuine group-valued product is a one-parameter subgroup with the actual sum zero-time velocity, from the retained actual identity multiplication derivative. Original global integral-curve uniqueness identifies it with the actual sum curve. Thus the original exponential respects addition when the original bracket is zero. No BCH or global inverse is supplied, and this result does not require original group nilpotency.",
    "NativeLieExponentialPeriods constructs the actual additive subgroup K={p:Exp(p)=1} in the original model E. Actual zero, inverse and commuting-addition laws prove its subgroup laws. The actual zero period generator proves Exp(p+v)=Exp(v) for every actual period and every v. Equal exponential values imply Exp(v-w)=1 using the proved common generator and actual inverse law; the reverse implication uses the actual period translation law. Thus Exp(v)=Exp(w) iff v-w is in K, and every actual fiber is the true affine K-coset. The retained actual fiber topology proves K is closed discrete. Genuine local injectivity and actual period invariance prove local neighborhoods disjoint from all their nonzero period translates.",
    "NativeLieExponentialRangeCovering is the actual original exponential with codomain restricted to its actual range, not a replacement group. Its actual continuity, openness and tautological surjectivity onto that range make it a genuine quotient map. Actual fiber equality and proved actual period discreteness instantiate the original additive-subgroup quotient covering theorem, so this actual range map is genuinely a covering map by K. No image subgroup, whole-group surjectivity, whole-group covering, period elimination or global inverse is claimed. Simply connectedness of the original group is not silently transferred to an open subset.",
    "Six new modules, 25 proved theorems and two definitions give 27 exact new kernel reports. Actual full-build and kernel terminal exit-zero records, raw byte logs and hashes, current oleans, exact imports and exact report names are required. All 741 own and nine attributed PNT+ modules plus root and registry are scanned for executable trust bypasses. Retained axiom sets and six retained axiom-free reports remain unchanged; only the standard axioms are permitted. Fixed local paper objects are checked without updates.",
    "Remaining: actual whole-group exponential surjectivity, elimination of the genuine central period group from original simply connectedness, the original global inverse/BCH, individual group/Lie lower-central layer comparison, faithful integration/Malcev comparison and arbitrary specified-lattice rational subgroup cocompactness. The next surjectivity approach is to construct actual product logarithms by nilpotent lower-central Picard iteration, deriving rather than supplying both the termination and actual differential equation. The actual range covering alone does not prove the range is a subgroup or all of G. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and prize submission await full proof and audit.",
]
components = [
    "genuine finite real vector polynomial coefficients are uniquely determined by all actual natural-number values through true scalar polynomial and dual separation proofs",
    "actual Banach-algebra exponential is injective on original nilpotent elements without assuming their commutation or supplying a logarithm",
    "equal actual original native exponential values have identical actual adjoint generators and their vector difference has zero original bracket with every vector",
    "actual original commuting native infinitesimal directions have commuting full one-parameter curves and genuine exponential addition laws from actual initial derivatives and original integral-curve uniqueness",
    "actual original native exponential periods form a closed discrete additive subgroup and original fibers are exactly its affine cosets with genuine disjoint local period translates",
    "actual original native exponential onto its actual range is a genuine additive-period quotient covering map without asserting surjectivity onto the whole original group",
]
previous = ast.parse(Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig"))
old_progress = next(ast.literal_eval(n.value) for n in previous.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "NEW_PROGRESS" for t in n.targets))
progress = old_progress + " True scalar polynomial uniqueness on all natural-number values and algebraic dual separation now prove finite real vector polynomial coefficient uniqueness. The actual Banach exponential is proved injective on nilpotent elements by actual finite exponential curves and equal natural powers, without assuming the two elements commute. Hence equal original native exponential values have equal actual adjoint generators and their difference has zero original bracket with every vector. Actual original adjoint ODE, original conjugation, actual identity multiplication derivative and genuine global integral-curve uniqueness prove the true exponential addition law for commuting original infinitesimal directions. The actual periods K={p:Exp(p)=1} are now proved to form a closed discrete additive subgroup of the original E, with Exp(p+v)=Exp(v), and Exp(v)=Exp(w) iff v-w is in K. Original fibers are exactly affine K-cosets, with true disjoint local period translates. The actual original exponential restricted only in codomain to its actual range is a proved genuine quotient covering map by K. Whole-group surjectivity, range subgroup closure and elimination of K remain unproved; original simply connectedness is not assumed to pass to the open exponential range. A genuine finite lower-central Picard construction of product logarithms is the next surjectivity route, not an input assumption."

body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
body = re.sub(r"\b(?:822|828|35|40|735|744|3772)\b", lambda m: {
    "822": "828", "828": "834", "35": "25", "40": "27", "735": "741", "744": "750", "3772": "3799",
}[m[0]], body)
body = replace_exact(body, '"baseline_hash_count": 747', '"baseline_hash_count": 753')
body = replace_exact(body, '"baseline_hashes_verified_before_registration": 747', '"baseline_hashes_verified_before_registration": 753')
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-native-exponential-fibers: PROGRESS. Six new modules, 25 proved theorems and two definitions; 27 exact new reports. All 753 baseline source/config hashes verified before registration. Retained proof sources, pins and attribution unchanged; only root and registry changed. Genuine natural-number scalar polynomial uniqueness and actual dual separation determine finite vector polynomial coefficients. Actual finite nilpotent exponential curves and equality of natural powers prove true Banach exponential injectivity on nilpotents without assuming commutation. Equal original native exponential values have equal original adjoint generators, and their vector difference is a native central direction. Actual global adjoint ODE, original conjugation, actual zero-time product derivative and genuine original integral-curve uniqueness prove commuting-direction exponential addition. The actual period set K is a closed discrete additive subgroup; original exponential fibers are exactly its affine cosets and local period translates are disjoint. The actual original exponential onto its actual range is now a genuine quotient covering map by K. Whole-group surjectivity, elimination of K and global inverse/BCH remain unproved; the original simply connected premise is not transferred to its open range. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3799 exact unique standard-axiom reports; retained axiom sets and six retained axiom-free reports unchanged. Scanned all 741 own and nine attributed PNT+ modules plus root and registry, with 759 current source/config hashes. New modules warning-free and oleans current; fixed local paper matches pinned objects, no remote updates. StrongConjecture and prize target unproved. No unavoidable blocker. Review: round-native-exponential-fibers-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "new_modules": len(modules), "new_theorems": 25, "new_reports": 27}))
