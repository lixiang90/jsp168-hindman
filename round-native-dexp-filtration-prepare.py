"""Prepare exact registration and audits without weakening retained checks."""
from pathlib import Path
import ast
import json
import re

prefix = "round-native-dexp-filtration"
old_prefix = "round-native-exponential-fibers"
modules = ["Hindman168/" + n + ".lean" for n in [
    "NativeLieLowerCentralModel", "NativeLieDexpDefectFiltration",
    "OperatorPowerFiltrationDifference", "NativeLieDexpInverseFiltration",
    "NativeLieLogarithmVectorField", "ClosedSubmoduleIntervalIntegral",
    "ContinuousPicardIteration", "NativeLieLogarithmPicard",
    "NativeLieExponentialProductLog", "NativeLieExponentialSurjective",
    "NativeLieExponentialCovering",
]]


def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)


register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-local-inverse-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = re.sub(r"\b(?:753|27|25)\b", lambda m: {"753": "759", "27": "55", "25": "48"}[m[0]], register)
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")

head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-exponential-fibers"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-local-inverse"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 753 and len(new_modules) == 6': 'len(baseline["files"]) == 759 and len(new_modules) == 11',
    'len(own) == 741 and len(pnt) == 9': 'len(own) == 752 and len(pnt) == 9',
    'len(names) == len(set(names)) == 27': 'len(names) == len(set(names)) == 55',
    'sum(c["theorems"] for c in module_counts.values()) == 25': 'sum(c["theorems"] for c in module_counts.values()) == 48',
    'len(registered) == len(set(registered)) == len(actual) == 3799': 'len(registered) == len(set(registered)) == len(actual) == 3854',
    'len(previous) == 3772': 'len(previous) == 3799',
    'len(source_files) == len({f["path"] for f in source_files}) == 759': 'len(source_files) == len({f["path"] for f in source_files}) == 770',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)

application = [
    "PROGRESS: the previous authoritative proof round was freshly rechecked before the saved 759-file baseline and current proof edits. All baseline source/config hashes are checked before registration. Retained proofs, StrongStatement, pins and attribution are unchanged; only root imports and exact-name registry change. No official/remote updates are checked and no unavoidable blocker is established.",
    "NativeLieLowerCentralModel uses exactly the native Lie lower central series of the original arbitrary Lie group, viewed in its original real model E. Actual original bracket identification proves the native adjoint generator sends layer j into j+1, its nth power sends j into j+n, and a parameter difference in layer j changes its action into j+1. Original Group.IsNilpotent gives actual termination at the original group nilpotencyClass, not a supplied filtration or separate Lie nilpotency hypothesis.",
    "NativeLieDexpDefectFiltration sets W_v=1-D_v for the actual original left-trivialized exponential differential. The retained actual finite differential formula gives the genuine positive-power defect formula. W_v lowers the original filtration by one; actual original termination implies W_v^c=0, including c=0. The true finite geometric sum U_v=sum(n<c) W_v^n satisfies both D_v U_v=1 and U_v D_v=1; no inverse formula is supplied.",
    "OperatorPowerFiltrationDifference proves the true difference identity for powers of two original continuous operators without assuming commutation. NativeLieDexpInverseFiltration instantiates it with the actual adjoint generators and actual defects, proving that parameter differences in layer j change every finite inverse action into j+1. The genuine two-sided inverse identities also identify the actual continuous-linear inverse with U_v. The actual finite inverse preserves every original lower-central layer.",
    "NativeLieLogarithmVectorField defines F_w(v)=U_v(w) using only the proved actual finite inverse. Actual polynomial operator formulas prove native C-infinity regularity. True D_v(F_w(v))=w and the strictly improving lower-central parameter difference are proved, with no nonlinear flow, Picard termination or derivative formula supplied.",
    "ClosedSubmoduleIntervalIntegral derives interval-integral membership through the true continuous quotient map of an actual closed submodule and true integral commutation. In the original finite-dimensional model, every original native lower-central layer is genuinely closed. This is the original paper's finite-dimensional Lie-group scope, not a replacement model or a supplied closure assumption.",
    "ContinuousPicardIteration constructs actual global iterated real interval integrals for a continuous field, with true continuity, exact initial value and actual fundamental-theorem-of-calculus derivatives. It does not assume convergence, termination or an existing solution.",
    "NativeLieLogarithmPicard instantiates the actual iterates with the actual original F_w. Their nth consecutive difference belongs to the original nth lower-central layer by genuine integral closure and the proved strictly improving field difference. Actual termination at the original group class c gives equality of iterate c+1 and iterate c at every real time. The actual iterate c+1 therefore has exact initial value u and satisfies the genuine global logarithm-lifting ODE. The c=0 case is included and does not rely on a derivative for iterate zero.",
    "NativeLieExponentialProductLog applies the actual manifold chain rule to the constructed original-model curve. The true native exponential differential and D_v(F_w(v))=w show its original exponential is a genuine integral curve of the original invariant field. Actual global original-group curve uniqueness identifies it with Exp(u)*gamma_w(t). At time one the true finite Picard curve provides a logarithm for Exp(u)*Exp(w), without supplied BCH or a global inverse.",
    "NativeLieExponentialSurjective constructs a genuine subgroup whose carrier is exactly the original exponential range. The actual Picard product logarithm proves product closure; original zero/inverse laws prove the other subgroup axioms. The actual open-map theorem and original connectedness force this open-and-closed subgroup to be the whole original G. Thus original native exponential surjectivity is proved, without silently transferring original simply connectedness to an open subset.",
    "NativeLieExponentialCovering combines this genuine whole-group surjectivity, actual original openness/continuity and proved original period fibers. The true original E-to-G map is a quotient map and a genuine additive-period quotient covering map. Whole-group covering is proved, but central period elimination and global injectivity/inverse remain unproved.",
    "Eleven new modules, 48 proved theorems and seven definitions give 55 exact new kernel reports. Actual terminal exit-zero full build/kernel records, raw byte logs and hashes, current oleans, exact imports/names and all-source trust scans are required. All 752 own and nine attributed PNT+ modules, plus root and registry, are covered. Retained axioms and six retained axiom-free reports stay unchanged. Only standard axioms are allowed; the fixed local paper and dependency pins are checked without updates.",
    "Remaining: eliminate the genuine central period group from the original simply connectedness, derive the original global inverse/BCH, compare individual original group/Lie lower-central layers and prove faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. The original nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and prize submission await full proof and audit.",
]
components = [
    "actual original native Lie lower-central model and genuine bracket-generator filtration improvement at the original group nilpotency cutoff",
    "actual original dexp defect is nilpotent and its true finite geometric sum is a proved two-sided inverse",
    "genuine noncommuting continuous-operator power differences remain in the actual invariant submodule",
    "actual original dexp inverse preserves original lower-central layers and improves parameter differences by one layer",
    "actual original logarithm lifting vector field is C-infinity and genuinely inverts the original left-trivialized exponential differential",
    "actual closed-submodule interval integrals stay in the original submodule and original finite-dimensional native lower-central layers are proved closed",
    "actual global continuous Picard iterates have proved initial values continuity and fundamental-theorem-of-calculus derivatives",
    "actual original logarithm Picard iterates strictly improve lower-central differences and stabilize at the original group nilpotency class yielding a genuine global solution",
    "actual original native exponential of the finite Picard curve equals the original left-translated invariant curve and supplies a true product logarithm",
    "actual original native exponential range is a genuine open subgroup and original connectedness proves whole-group surjectivity",
    "actual original native exponential onto the whole original connected nilpotent finite-dimensional Lie group is a genuine additive-period quotient covering map",
]
progress = (
    "The actual original native adjoint differential is the native bracket, and original group nilpotency proves native Lie lower-central termination at the original group class c. The actual original native exponential is built from genuine global invariant integral curves, with actual native C-infinity regularity, actual differential, local C-infinity inverse and open/local-homeomorphism properties. Genuine mixed derivatives and the original relative-curve cocycle give the actual finite dexp formula. Actual finite nilpotent Banach exponential injectivity and true commuting-direction addition identify original fibers exactly as affine cosets of the actual closed discrete central period subgroup K={p:Exp(p)=1}. These previously proved statements remain valid. "
    "The actual original native lower-central layers S_j are now used directly in the original model E. The actual dexp defect W_v=1-D_v maps S_j into S_(j+1) and has W_v^c=0. Its genuine finite geometric sum U_v is proved to be the actual two-sided differential inverse. Actual noncommuting power identities prove U_v preserves every S_j and v-z in S_j implies U_v(w)-U_z(w) in S_(j+1). Thus the actual field F_w(v)=U_v(w) is C-infinity, has D_v(F_w(v))=w and the strict filtration improvement. Original finite-dimensionality proves every S_j closed; genuine continuous quotient-map integral commutation proves integrals remain in these actual layers. "
    "Actual global Picard iterates gamma_0(t)=u and gamma_(n+1)(t)=u+integral(0..t,F_w(gamma_n(s))) are now constructed. Actual FTC gives their derivatives and original integral/filtration improvement proves gamma_(n+1)-gamma_n in S_n. The genuine original cutoff proves gamma_(c+1)=gamma_c at every real time, so gamma_(c+1) satisfies the actual global logarithm ODE from u, including c=0. Actual manifold chain rules and the genuine dexp inverse identity make Exp(gamma(t)) a true original invariant integral curve. Original global uniqueness proves Exp(gamma(t))=Exp(u)*gamma_w(t); its time-one value is an actual product logarithm. The original exponential range is therefore a genuine subgroup. Its original open-map property and original connectedness prove the range is all of G. The actual whole-group exponential is now genuinely surjective and a quotient covering map by the original closed discrete period group K. No BCH, nonlinear global flow, Picard termination, supplied filtration or replacement matrix group is assumed. "
    "Whole-group surjectivity and covering no longer remain open tasks. Genuine elimination of K from the original simply connectedness, global injectivity and the original global C-infinity inverse/BCH still remain unproved. Individual original group/Lie lower-central layer comparison, faithful integration/Malcev comparison, arbitrary specified-lattice rational subgroup cocompactness and full calibration/Alignment/arithmetic witnesses also remain unproved. The original nonabelian lattice logarithms are not assumed additive. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established."
)

body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
numeric = {"828": "834", "834": "845", "25": "48", "27": "55", "741": "752", "750": "761", "3799": "3854", "753": "759", "6": "11"}
body = re.sub(r"\b(?:" + "|".join(numeric) + r")\b", lambda m: numeric[m[0]], body)
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-native-dexp-filtration: PROGRESS. Eleven new modules, 48 proved theorems and seven definitions; 55 exact new reports. All 759 baseline source/config hashes checked before registration. Retained proof sources, pins and attribution unchanged; only root and registry changed. Original native lower-central layers, true dexp defect nilpotency and true two-sided finite inverse give a C-infinity logarithm lifting field with strict filtration improvement. Actual integral closure in original finite-dimensional layers proves consecutive global Picard differences deepen one layer per step. Original group class c kills the next difference, deriving actual finite stabilization and the genuine global logarithm ODE. Original manifold chain rules and original global invariant-curve uniqueness give Exp(gamma(t))=Exp(u)*gamma_w(t), and an actual product logarithm. The actual original exponential range is now a subgroup; its openness and original connectedness prove whole-group surjectivity. The actual E-to-G exponential is a genuine quotient covering map by K. Original simply connectedness has not yet eliminated K; injectivity/global inverse/BCH remain unproved. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3854 exact unique standard-axiom reports. Retained axiom sets and six retained axiom-free reports unchanged. All 752 own and nine attributed PNT+ modules plus root and registry scanned; 770 current source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match, no remote updates. StrongConjecture and prize target unproved. No unavoidable blocker. Review: round-native-dexp-filtration-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "modules": len(modules), "theorems": 48, "reports": 55}))
