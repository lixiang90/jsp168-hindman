from pathlib import Path
import ast
import json
import re

prefix = "round-native-dexp"
old_prefix = "round-group-lie-nilpotency"
modules = ["Hindman168/" + name + ".lean" for name in [
    "NativeLieRelativeCurve", "NativeLieCurveParameterJacobian",
    "NativeLieParameterJacobianInitial", "NativeLieParameterJacobianCocycle",
    "AdjointPrimitivePolynomial", "NativeLieExponentialDifferential",
    "NativeLieNilpotentDexp", "NilpotentPolynomialUnit", "NativeLieDexpInvertible",
]]

def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)

register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-bracket-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = re.sub(r"\b(?:733|23|21)\b", lambda m: {"733": "738", "23": "45", "21": "40"}[m[0]], register)
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
build = replace_exact(build, old_prefix, prefix)
Path(prefix + "-build.py").write_text(build, encoding="utf-8")

head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-group-lie-nilpotency"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-bracket"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 733 and len(new_modules) == 5': 'len(baseline["files"]) == 738 and len(new_modules) == 9',
    'len(own) == 720 and len(pnt) == 9': 'len(own) == 729 and len(pnt) == 9',
    'len(names) == len(set(names)) == 23': 'len(names) == len(set(names)) == 45',
    'sum(c["theorems"] for c in module_counts.values()) == 21': 'sum(c["theorems"] for c in module_counts.values()) == 40',
    'len(registered) == len(set(registered)) == len(actual) == 3687': 'len(registered) == len(set(registered)) == len(actual) == 3732',
    'len(previous) == 3664': 'len(previous) == 3687',
    'len(source_files) == len({f["path"] for f in source_files}) == 738': 'len(source_files) == len({f["path"] for f in source_files}) == 747',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)

application = [
    "PROGRESS: the preceding authoritative round was independently rechecked before edits. All 738 baseline source/configuration hashes are revalidated before registration. Retained proofs, StrongConjecture, pins and attribution remain unchanged; only the root imports and exact-name kernel registry change among retained sources. No unavoidable blocker is established. The fixed local paper is compared with pinned Git objects, without remote or official updates.",
    "NativeLieRelativeCurve defines exactly r-v(t,w)=gamma-v(-t)*gamma-(v+w)(t), from the original chosen native integral curves. Actual one-parameter identities prove its zero-time and zero-state values and genuine group-valued cocycle r(t+s,w)=gamma(-t)*r(s,w)*gamma(t)*r(t,w). Original joint smoothness proves actual C-infinity regularity. Actual identity multiplication derivatives prove its zero-time velocity is exactly w. No relative curve, variation equation or logarithmic derivative is supplied.",
    "NativeLieCurveParameterJacobian defines K-v(t) as the actual original manifold parameter derivative of r-v(t,w) at w=0. The true identity chart and genuine manifold chain rule identify it with the actual coordinate Jacobian applied to the state inclusion. Actual coordinate regularity proves the operator-valued map K-v is C-infinity; its original zero-time value is zero. Canonical original model operators and explicit native tangent identifications reconcile Lean aliases without new options or transparency overrides.",
    "NativeLieParameterJacobianInitial derives the genuine coordinate time velocity w at time zero. Original joint C2 regularity and the proved actual time-velocity identity near zero instantiate the actual second-derivative symmetry lemma, proving the true time derivative of K-v(t) applied to every w is w at zero. Differentiating the actual operator action and derivative uniqueness then prove K-v'(0)=id. The mixed derivative is applied to the actual original relative curve, not a supplied flow.",
    "NativeLieParameterJacobianCocycle differentiates the genuine group cocycle at zero parameter. Both original product factors equal identity, so the actual identity multiplication derivative and actual original conjugation derivative give K-v(t+s)=Ad-gamma-v(-t)*K-v(s)+K-v(t). Actual time translation and the proved K-v'(0)=id then give the original global equation K-v'(t)=Ad-gamma-v(-t). Products remain in their actual order; no commutativity or variation equation is assumed.",
    "AdjointPrimitivePolynomial constructs P-B,k(t)=sum(j<k) ((-1)^j/(j+1)!)*t^(j+1) times B^j. Its actual scalar coefficients and finite sum are differentiated directly, yielding exactly the retained finite adjoint series at negative time. The genuine zero-derivative theorem and actual zero initial values show every actual K with that proved derivative equals this polynomial. This abstract primitive is actually instantiated with the original derivative-defined native bracket generator and original group nilpotencyClass.",
    "NativeLieExponentialDifferential defines nativeLieDexp by the actual original exponential manifold derivative followed by the actual inverse left-translation derivative. Genuine native chain rules for the actual parameter shift and the original exponential identify it with K-v(1). Actual inverse translation identities prove that the full original exponential derivative is genuine left translation composed with this nativeLieDexp; the action formula is the original native invariant field. No exponential differential formula or invertible derivative is an input.",
    "NativeLieNilpotentDexp applies original Group.IsNilpotent and the previously proved original group-class adjoint cutoff to the actual global K equation. It proves K-v(t)=P-B-v,c(t), hence nativeLieDexp-v=sum(j<c) (-1)^j/(j+1)! times B-v^j, with c the original Group.nilpotencyClass and B-v the actual generator already proved to act as the original native Lie bracket. It does not require separately supplied native Lie-algebra nilpotency or replace the original group by a matrix model.",
    "NilpotentPolynomialUnit proves that a finite polynomial with constant coefficient one evaluated at a genuinely nilpotent element is a true unit. Its positive-degree terms are individually nilpotent and commute as powers of one element, so their finite sum is nilpotent. The zero-cutoff case is proved separately using B^0=0, hence 1=0; no nontriviality or positive group-class premise is silently imposed. NativeLieDexpInvertible actually instantiates this with the original group-class cutoff. It proves nativeLieDexp is a unit and bijective at every original vector. Both genuine inverse left-translation derivative identities prove the original translation derivative is a true two-sided unit, hence the full original exponential derivative is a unit and bijective at every vector. These are differential conclusions, not global exponential bijectivity.",
    "All nine new modules, 40 proved theorems and five definitions are registered in the actual root and exact-name kernel audit, yielding 45 exact new reports. Full build and full kernel processes must terminate with exit zero before recording; raw byte evidence and hashes are retained. New modules are warning-free with current oleans. Retained exact axiom sets, including the six retained axiom-free declarations, remain unchanged, and all reports use only propext, Classical.choice and Quot.sound. All 729 own and nine attributed PNT+ modules plus root and registry are scanned for executable trust bypasses. Pins and attributed sources stay unchanged.",
    "Remaining: actual group/Lie lower-central layer identification, global exponential inverse/BCH for arbitrary connected simply connected nilpotent Lie groups, faithful integration/Malcev comparison and arbitrary specified-lattice rational subgroup cocompactness. Pointwise invertible exponential differentials alone do not establish a global inverse. Nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witness extraction remain unproved. StrongConjecture and the prize target remain unproved; public repository, prize PR and application await full formalization and audit.",
]
components = [
    "actual original relative parameter curve has genuine zero values, C-infinity regularity, zero-time velocity and original group-valued time cocycle",
    "actual original relative parameter derivative is the identity-chart state Jacobian and is C-infinity with original zero initial value",
    "actual original relative Jacobian initial time derivative is identity by genuine mixed differentiation of the actual relative coordinate curve",
    "actual original relative Jacobian cocycle and global time derivative equal negative-time original native adjoint, derived from actual group multiplication and conjugation",
    "actual finite adjoint-series polynomial primitive is directly differentiated and identified by genuine zero-derivative uniqueness",
    "original native exponential left-trivialized differential is the actual relative parameter Jacobian at time one and reconstructs the complete original manifold derivative",
    "actual original native exponential differential has the finite bracket-generator formula at original group nilpotencyClass without supplied native Lie nilpotency",
    "actual finite polynomial with constant coefficient one evaluated at a nilpotent element is a unit, including the zero-cutoff trivial-ring case",
    "actual original native dexp and complete original exponential differential are two-sided units and bijective at every original model vector under original group nilpotency",
]
progress = "The actual original native adjoint generators act as the original native Lie bracket. Original group lower-central termination forces every same-length ordered generator product to vanish and hence native Lie lower-central termination at the same cutoff. Thus original Group.IsNilpotent proves native LieModule.IsNilpotent, and genuine original adjoints have finite formulas at original Group.nilpotencyClass. The actual relative curve r-v(t,w)=gamma-v(-t)*gamma-(v+w)(t) now has proved original group cocycle, actual C-infinity regularity and zero-time velocity w. Its genuine original manifold state derivative K-v(t) is identified with its actual identity-chart Jacobian, is C-infinity and has actual initial value zero. Genuine mixed second-derivative symmetry applied to this original relative curve proves K-v'(0)=id. Differentiating the actual group cocycle proves K-v(t+s)=Ad-gamma-v(-t)*K-v(s)+K-v(t), and real time translation gives the actual global derivative K-v'(t)=Ad-gamma-v(-t). A directly differentiated finite polynomial primitive and actual zero-derivative uniqueness prove K-v(t)=sum(j<c) ((-1)^j/(j+1)!)*t^(j+1) times B-v^j, where c is the original group nilpotencyClass and B-v is the actual native bracket generator. Original manifold chain rules identify K-v(1) with the actual original exponential differential followed by actual inverse left translation. Thus the original native dexp now has its genuine finite formula sum(j<c) (-1)^j/(j+1)! times B-v^j, and the full original exponential derivative is actual left translation composed with that operator. Nilpotency and the actual constant-one finite polynomial prove native dexp is a genuine two-sided unit and bijective at every original model vector; actual inverse translation derivatives prove the complete original exponential derivative is likewise a two-sided unit and bijective. The zero group-class case is covered through the proved identity 1=0 for the resulting operator ring, without a nontriviality premise. No dexp formula, variation equation, derivative invertibility, native Lie nilpotency or matrix replacement is supplied. Individual group/Lie lower-central layer identification and global exponential invertibility/BCH still remain unproved; pointwise invertible derivatives alone do not give a global inverse."

body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
body = replace_exact(body, 'len(manifest["proved_components"]) == 808', 'len(manifest["proved_components"]) == 813')
body = replace_exact(body, 'len(manifest["proved_components"]) == 813 and manifest["proved_components"][-5:]', 'len(manifest["proved_components"]) == 822 and manifest["proved_components"][-9:]')
numeric = {"733": "738", "21": "40", "23": "45", "720": "729", "729": "738", "3687": "3732"}
body = re.sub(r"\b(?:733|21|23|720|729|3687)\b", lambda m: numeric[m[0]], body)
body = replace_exact(body, '"new_module_count": 5', '"new_module_count": 9')
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-native-dexp: PROGRESS. Nine new modules, 40 proved theorems and five definitions; 45 exact new reports. All 738 baseline source/config hashes revalidated before registration; only root and registry change among retained sources. The original relative curve has a genuine group cocycle and actual zero-time velocity. Its actual manifold parameter Jacobian is C-infinity with K(0)=0. Genuine mixed derivatives prove K'(0)=id; actual cocycle differentiation and time translation prove K'(t)=Ad-gamma(-t). A directly differentiated finite primitive gives the actual original group-class polynomial for K. Actual original native chain rules identify K(1) with native dexp, the actual inverse-left-trivialized original exponential differential, and reconstruct the full derivative by actual left translation. Original group nilpotency gives the exact finite native bracket-generator formula. Nilpotent constant-one polynomials and genuine inverse translation derivatives prove native dexp and the complete original exponential differential are two-sided units and bijective at every original vector, including the zero-cutoff case. No global inverse or BCH is supplied. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3732 exact unique standard-axiom reports; all retained axiom sets and six retained axiom-free reports unchanged. Scanned 729 own and nine attributed PNT+ modules plus root/registry; 747 current source/config hashes. New modules warning-free and oleans current; fixed local paper objects match, no remote updates checked. Group/Lie layer comparison, global inverse/BCH, arbitrary specified-lattice transfer, full calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-native-dexp-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "new_modules": len(modules), "new_theorems": 40, "new_reports": 45}))
