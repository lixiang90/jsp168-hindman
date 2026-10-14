"""Preserve the previous exact verification gates for native Lie subgroups."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import io
import json
import re
import tokenize

prefix = "round-native-lie-subgroups"
old_prefix = "round-native-global-inverse"
modules = [
    "Hindman168/NativeLieSubalgebraModel.lean",
    "Hindman168/NativeLieSubalgebraPicard.lean",
    "Hindman168/NativeLieSubalgebraSubgroup.lean",
    "Hindman168/NativeLieSubalgebraTopology.lean",
    "Hindman168/NativeLieIdealSubgroup.lean",
    "Hindman168/NativeLieLowerCentralSubgroups.lean",
    "Hindman168/NativeLieLogarithmAffineLayer.lean",
    "Hindman168/NativeLieAdjointLayer.lean",
    "Hindman168/NativeLieGroupLowerCentralComparison.lean",
    "Hindman168/NativeLieGlobalProductLog.lean",
]


def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)


spec = spec_from_file_location("previous_native_audit", old_prefix + "-audit.py")
previous = module_from_spec(spec)
spec.loader.exec_module(previous)
baseline = previous.obj(prefix + "-baseline.json")
assert baseline == previous.obj("verification-manifest.json")
assert len(baseline["files"]) == 772
assert all(previous.digest(f["path"]) == f["sha256"] for f in baseline["files"])
decls = [d for p in modules for d in previous.declarations(p)]
assert len(decls) == 47 and sum(k in {"theorem", "lemma"} for k, _ in decls) == 43
assert all(not Path(p).as_posix() in {f["path"] for f in baseline["files"]} for p in modules)
register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-dexp-filtration-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register_numeric = {"770": "772", "10": "47", "8": "43"}
register_tokens = list(tokenize.generate_tokens(io.StringIO(register).readline))
register = tokenize.untokenize([
    token._replace(string=register_numeric[token.string])
    if token.type == tokenize.NUMBER and token.string in register_numeric else token
    for token in register_tokens
])
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")
head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-global-inverse"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-dexp-filtration"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 770 and len(new_modules) == 2': 'len(baseline["files"]) == 772 and len(new_modules) == 10',
    'len(own) == 754 and len(pnt) == 9': 'len(own) == 764 and len(pnt) == 9',
    'len(names) == len(set(names)) == 10': 'len(names) == len(set(names)) == 47',
    'sum(c["theorems"] for c in module_counts.values()) == 8': 'sum(c["theorems"] for c in module_counts.values()) == 43',
    'len(registered) == len(set(registered)) == len(actual) == 3864': 'len(registered) == len(set(registered)) == len(actual) == 3911',
    'len(previous) == 3854': 'len(previous) == 3864',
    'len(source_files) == len({f["path"] for f in source_files}) == 772': 'len(source_files) == len({f["path"] for f in source_files}) == 782',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)
application = [
    "PROGRESS: the preceding original global exponential diffeomorphism round was recorded and freshly rechecked before the saved 772-file baseline and these edits. All baseline hashes are reverified before registration. Retained proofs, StrongStatement, pins and attribution are unchanged; only root and exact-name registry change. No remote official updates are checked. No unavoidable blocker is established.",
    "NativeLieSubalgebraModel is the actual underlying real submodule of an arbitrary original native Lie subalgebra. Its finite-dimensional closure is proved. The original adjoint generator equals the actual original bracket, so actual internal parameters preserve the subalgebra under generator powers, genuine dexp defect powers, finite inverse and true logarithm vector field. No provided substitute Lie algebra or BCH closure is used.",
    "NativeLieSubalgebraPicard uses real finite-dimensional closure and actual interval integral membership to keep every genuine finite Picard iterate in the original subalgebra. The actual stabilized lift therefore stays inside it. NativeLieSubalgebraSubgroup uses the already proved actual product logarithm, zero and inverse laws to show that the original exponential image itself is an original subgroup, not merely a generated or closed envelope. Original global inverse laws give the exact subgroup/logarithm membership correspondence.",
    "NativeLieSubalgebraTopology constructs the actual restricted exponential/global-logarithm homeomorphism with natural subtype topologies. The subgroup is genuinely closed by the actual logarithm preimage of the closed model; actual convexity and the true homeomorphism give contractibility, connectedness and simply connectedness. This does not prove the required specified-lattice cocompactness, rationality or smooth subgroup manifold structure.",
    "NativeLieIdealSubgroup proves invariance under every original conjugation from the actual finite adjoint formula, true original exponential surjectivity and genuine conjugation/exponential identity. The exponential of any actual original native Lie ideal is normal. NativeLieLowerCentralSubgroups exponentiates each original native Lie lower-central layer and proves antitonicity, original-class termination, zeroth top, normality and, in the original simply connected case, closedness and contractibility. These exponentiated layers are not silently identified with the algebraic group lower central series.",
    "NativeLieLogarithmAffineLayer proves that the actual logarithm vector field differs from its layer-j velocity by an element of layer j+1: the finite inverse preserves j, its true dexp equation converts the defect into the difference, and the proved defect lowers layers. Actual Picard integral subtraction proves the true lift differs from u+t*w in j+1. The actual product logarithm then proves membership in the next exponential layer when u+w is in that layer.",
    "NativeLieAdjointLayer pads the actual finite adjoint series by a zero terminal power and removes its identity term, giving a true positive-power formula even in class zero. Original generator powers lower the original Lie layers, hence Ad(g)(w)-w lies in layer j+1 for every original g and w in j. NativeLieGroupLowerCentralComparison combines this fact, actual conjugation and genuine product logarithms to place actual commutators [g,Exp(w)] in the next exponential layer. Actual subgroup commutator generation and induction give Group.lowerCentralSeries(j) <= Exp(Lie.lowerCentralSeries(j)). Reverse inclusion, equality and algebraic group layer closedness remain unproved.",
    "NativeLieGlobalProductLog proves that the actually constructed global logarithm of Exp(u)*Exp(w) equals the genuine finite Picard lift. Consequently the true logarithm product error lies in the next layer, and for all original g,h the actual log(g*h)-log(g)-log(h) belongs to the actual first Lie commutator layer. Actual original group lower-central elements have logarithms in the corresponding native Lie layers. No rational Lie-polynomial BCH coefficient claim is made.",
    "Ten new modules, 43 proved theorems and four definitions give 47 exact new reports. Require full build and kernel terminal exit zero with real byte logs and hashes, current oleans, exact source names/imports, retained axiom sets and six retained axiom-free reports, all-source trust scans, pinned dependencies and fixed local paper objects. All 764 own and nine attributed PNT+ modules plus root and registry are covered. No new option overrides or dependency source edits are introduced.",
    "Remaining: actual rational Lie-polynomial BCH structure, reverse individual group/Lie layer inclusion and exact series comparison, faithful integration/Malcev, arbitrary specified-lattice rational subgroup cocompactness, full calibration/Alignment and original ordered positive arithmetic witnesses. Original nonabelian lattice logarithms are not treated as additive. StrongConjecture and the full prize target remain unproved; publication and prize submission await full proof and audit.",
]
components = [
    "actual original native Lie subalgebras are closed in finite dimension and preserved internally by true adjoint generator powers, dexp defect powers and finite inverse logarithm fields",
    "actual global finite Picard logarithm iterates and stabilized lifts remain inside every original native Lie subalgebra by true closed-submodule integrals",
    "actual exponential image of every original native Lie subalgebra is itself a genuine original subgroup with exact actual global-logarithm membership",
    "actual original Lie-subalgebra exponential image is naturally homeomorphic to its model and is closed, contractible, connected and simply connected",
    "actual exponential image of every original native Lie ideal is normal by original finite adjoint invariance and actual group conjugation",
    "actual original native Lie lower-central layers exponentiate to a decreasing normal filtration terminating at original group class and closed contractible layers in the simply connected case",
    "actual logarithm-lifting field and finite Picard product lift have additive errors in the next original native lower-central layer",
    "actual original group adjoint acts as identity modulo the next original native Lie lower-central layer via its true positive-power finite formula",
    "actual original group lower central series is contained in the exponentials of original native Lie lower-central layers by genuine commutator identities and generation",
    "actual original global logarithm of multiplication equals the finite Picard lift and is additive modulo the original native first commutator layer",
]
progress = previous.NEW_PROGRESS.split("Remaining:", 1)[0] + (
    "Every original native real Lie subalgebra is now proved closed in finite dimension and preserved by the genuine finite inverse field and actual Picard integrals. Its actual exponential image itself is a subgroup. The actual restricted exponential and global logarithm form a natural subtype homeomorphism, proving genuine closedness and contractibility, hence connectedness and simply connectedness. Every original native Lie ideal exponentiates to a normal original subgroup by actual finite adjoint invariance. The original native Lie lower-central layers S_j exponentiate to a decreasing normal filtration H_j with H_0=G, H_c=1 and closed contractible terms in the original simply connected case. Actual dexp equations prove F_w(v)-w lies in S_(j+1) when w lies in S_j, and real Picard integrals give Lift(w,u,t)-(u+t*w) in S_(j+1). The actual finite adjoint formula, padded by its genuinely zero terminal power, gives Ad(g)(w)-w in S_(j+1). True conjugation and product-logarithm laws place [g,Exp(w)] in H_(j+1). Subgroup commutator generation and induction prove the one-sided inclusion of the original algebraic Group.lowerCentralSeries(j) in H_j. The actual global logarithm of Exp(u)*Exp(w) is the genuine finite Picard lift; its additive error lies in S_(j+1), and actual log(g*h)-log(g)-log(h) lies in S_1. These are statements about original arbitrary groups and original native brackets, not replacement matrix models. "
    "Remaining: prove the actual finite Picard product logarithm has the required rational Lie-polynomial BCH structure; prove reverse individual original group/Lie lower-central inclusion, exact comparison and algebraic group layer closedness; derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Closedness of exponentiated real subalgebras alone does not imply rationality or lattice cocompactness. Original nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and original ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established."
)
body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
start = body.index("    old_status = ")
end = body.index("    review = {", start)
body = body[:start] + body[end:]
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
body = body[:start] + "    note = __CURRENT_NOTE__" + body[end:]
numeric = {"845": "847", "847": "857", "8": "43", "10": "47", "754": "764", "763": "773", "3864": "3911", "770": "772"}
tokens = list(tokenize.generate_tokens(io.StringIO(body).readline))
body = tokenize.untokenize([
    token._replace(string=numeric[token.string])
    if token.type == tokenize.NUMBER and token.string in numeric else token
    for token in tokens
])
body = replace_exact(body, '"new_module_count": 2', '"new_module_count": 10')
body = replace_exact(body, '[-2:]', '[-10:]')
note1 = "\n2026-10-10 round-native-lie-subgroups: PROGRESS. Ten new modules, 43 proved theorems and four definitions; 47 exact new reports. All 772 baseline source/config hashes verified before registration. Only retained root and registry change. Actual original native real Lie subalgebras are preserved by the true finite inverse and Picard integrals; their exponential images are genuine closed contractible original subgroups with natural restricted exponential/logarithm homeomorphisms. Actual Lie ideals exponentiate to normal subgroups. Actual native lower-central layers exponentiate to a decreasing normal filtration with original-class termination. True inverse differential, genuine integrals and finite adjoint formula give actual next-layer additive errors and commutator membership. Original algebraic group lower-central layers are contained in the corresponding Lie exponential layers; reverse inclusion and equality remain unproved. Actual global product logarithms equal the genuine finite Picard lifts. Rational BCH and arbitrary specified-lattice cocompactness remain unproved, as does the full target. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3911 exact unique standard-axiom reports. Retained axioms and six retained axiom-free reports unchanged. All 764 own and nine attributed PNT+ modules plus root and registry scanned; 782 source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-lie-subgroups-review.json.\n\n"
body = replace_exact(body, "__CURRENT_NOTE__", "(" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")")
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "modules": len(modules), "theorems": 43, "reports": 47}))
