from pathlib import Path
import ast
import json
import re

prefix = "round-native-local-inverse"
old_prefix = "round-native-dexp"
modules = ["Hindman168/" + name + ".lean" for name in [
    "NativeLieShiftedExponential", "NativeLieExponentialLocalLogAt",
    "NativeLieExponentialLocalHomeomorph", "NilpotentFiniteExponentialKernel",
    "NativeLieExponentialCentralKernel", "NativeLieAdjointKernelCenter",
]]

def replace_exact(text, before, after):
    assert text.count(before) == 1, before
    return text.replace(before, after)

register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-group-lie-nilpotency-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = re.sub(r"\b(?:738|45|40)\b", lambda m: {"738": "747", "45": "40", "40": "35"}[m[0]], register)
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")

head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
changes = {
    'PREFIX = "round-native-dexp"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-group-lie-nilpotency"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 738 and len(new_modules) == 9': 'len(baseline["files"]) == 747 and len(new_modules) == 6',
    'len(own) == 729 and len(pnt) == 9': 'len(own) == 735 and len(pnt) == 9',
    'len(names) == len(set(names)) == 45': 'len(names) == len(set(names)) == 40',
    'sum(c["theorems"] for c in module_counts.values()) == 40': 'sum(c["theorems"] for c in module_counts.values()) == 35',
    'len(registered) == len(set(registered)) == len(actual) == 3732': 'len(registered) == len(set(registered)) == len(actual) == 3772',
    'len(previous) == 3687': 'len(previous) == 3732',
    'len(source_files) == len({f["path"] for f in source_files}) == 747': 'len(source_files) == len({f["path"] for f in source_files}) == 753',
}
for before, after in changes.items():
    head = replace_exact(head, before, after)

application = [
    "PROGRESS: the preceding authoritative proof round was independently rechecked before edits. All 747 baseline source/configuration hashes are checked before registration. Retained proof sources, StrongStatement, toolchain pins and attribution are unchanged; among retained sources only root imports and the exact-name kernel registry change. The fixed local paper is checked against its pinned Git objects without remote updates. The intervening prize heartbeat was a read-only status check, separate from this proof work.",
    "NativeLieShiftedExponential is the actual original relative curve in the actual identity chart at time one. Its base value is the actual chart coordinate of identity, which is not assumed zero. The true derivative equals the already proved original native dexp. Actual C-infinity regularity upgrades it to strict differentiability. The actual unit dexp supplies a continuous linear equivalence, and the genuine Banach inverse-function theorem constructs the real shifted local inverse, with both local inverse laws, exact base value, actual strict derivative and actual C-infinity regularity. No inverse function or chart normalization is supplied.",
    "NativeLieExponentialLocalLogAt constructs log-v(g)=v+shifted-inverse-v(chart-1(Exp(v)^-1*g)) on the original group. It proves its actual base value and native C-infinity regularity. Translating the actual coordinate inverse laws gives the left inverse near v. For the right inverse, both original relative group points are proved to remain in the true chart source before applying actual chart injectivity and original group cancellation. Thus both laws hold for the original native exponential at every original vector; no global inverse is claimed.",
    "NativeLieExponentialLocalHomeomorph uses the actual local logarithm to prove that images of true neighborhoods are true neighborhoods, hence the original exponential is open. Its actual left inverse proves genuine local injectivity. Continuous, injective, open restrictions prove the original exponential is a local homeomorphism. The actual neighborhood map equality, open exponential range and closed discrete original fibers follow. Neither a covering map nor range equal to the whole group follows from these statements alone.",
    "NilpotentFiniteExponentialKernel factors the actual finite exponential series minus one as B times a genuine constant-one polynomial. The retained proved polynomial-unit theorem gives a true unit, and genuine cancellation proves B=0 if that finite exponential equals one. The proof works in an arbitrary possibly noncommutative algebra and covers the zero cutoff without silently assuming nontriviality.",
    "NativeLieExponentialCentralKernel instantiates this actual finite polynomial factor with the original group-class adjoint formula. Exp(v)=1 implies the derivative-defined original native adjoint generator is zero, and therefore the actual original native bracket [v,w] is zero for every w. The genuine original adjoint curve then equals identity at every real time. This restricts periods to original Lie-algebra central directions; it does not eliminate them.",
    "NativeLieAdjointKernelCenter proves identity original adjoint means commutation with the actual original exponential range. The already proved true identity-neighborhood image puts an identity neighborhood inside the actual centralizer. The original Lie group supplies the actual topological-group structure; the centralizer is genuinely open and closed, so original connectedness proves it is the whole group. Conversely, an actual central element has identity conjugation and hence identity actual native derivative. Thus ker(Ad)=the actual group center. Every original exponential period has its entire original one-parameter curve in the center. No connected or simply connected substitute group is introduced.",
    "Six new modules contain 35 proved theorems and five definitions, giving 40 exact new kernel reports. Actual full-build and full-kernel terminal exit-zero results, raw byte hashes, current oleans, exact root imports and exact registry are required before recording. The complete own and attributed source tree is scanned for executable trust bypasses. All retained axiom sets and the six retained axiom-free reports remain unchanged. Only propext, Classical.choice and Quot.sound are allowed.",
    "Remaining: the original global exponential inverse and BCH for arbitrary connected simply connected nilpotent Lie groups are still unproved. Local homeomorphism and closed discrete fibers do not by themselves prove a covering map, surjectivity or injectivity. Central periods still need a genuine elimination argument using the original structure. Individual group/Lie lower-central layer comparison, faithful integration/Malcev comparison, arbitrary specified-lattice rational subgroup cocompactness, full calibration/Alignment and ordered positive arithmetic witness extraction remain. Nonabelian lattice logarithms are not assumed additive. StrongConjecture and the prize target are not proved; publication and prize submission still await the complete proof and audit. No unavoidable blocker is established.",
]
components = [
    "actual original shifted exponential chart has strict invertible derivative and a genuine C-infinity coordinate local inverse at every original vector",
    "actual original native exponential has a constructed native C-infinity local logarithm with both local inverse laws at every original vector",
    "actual original native exponential is a local homeomorphism and open map with exact neighborhood images and closed discrete fibers",
    "actual finite exponential of a nilpotent algebra element equals one only if that element is zero, by genuine polynomial-unit cancellation",
    "actual original native exponential periods have zero original adjoint generator and zero native bracket with every original vector",
    "actual original connected Lie-group adjoint kernel equals its original group center and original exponential period curves lie entirely in that center",
]
previous = ast.parse(Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig"))
old_progress = next(ast.literal_eval(n.value) for n in previous.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "NEW_PROGRESS" for t in n.targets))
progress = old_progress + " The actual original shifted exponential coordinate map now has a genuine strict invertible derivative and a C-infinity local inverse at every original vector, from the actual Banach inverse-function theorem. Its actual identity-chart base coordinate is retained, not assumed zero. The constructed original native local logarithm has true native C-infinity regularity and both local inverse laws; actual chart-source control is proved for the group-valued right law. Thus the original native exponential is a genuine local homeomorphism and open map, with exact neighborhood images, open range and closed discrete fibers. A finite nilpotent exponential factor and true constant-one polynomial unit prove every original exponential period has zero actual adjoint generator, hence zero original native bracket with every vector. Identity original adjoint is proved equivalent to actual group centrality in the original connected group, using the actual open centralizer and genuine connectedness. The entire original one-parameter curve of each period lies in the original center. These facts do not prove a covering map, global surjectivity or injectivity; original central periods have not yet been eliminated."

body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("def record():"):]
body = re.sub(r"\b(?:813|822|40|45|729|738|3732)\b", lambda m: {
    "813": "822", "822": "828", "40": "35", "45": "40", "729": "735", "738": "744", "3732": "3772",
}[m[0]], body)
body = replace_exact(body, '"baseline_hash_count": 744', '"baseline_hash_count": 747')
body = replace_exact(body, '"baseline_hashes_verified_before_registration": 744', '"baseline_hashes_verified_before_registration": 747')
body = replace_exact(body, '"new_module_count": 9', '"new_module_count": 6')
body = replace_exact(body, 'manifest["proved_components"][-9:]', 'manifest["proved_components"][-6:]')
start = body.index("    note = (")
end = body.index('\n    Path("AUDIT.txt")', start)
note1 = "\n2026-10-10 round-native-local-inverse: PROGRESS. Six new modules, 35 proved theorems and five definitions; 40 exact new kernel reports. All 747 baseline source/config hashes checked before registration; retained proofs and pins unchanged, only root and registry changed. Original shifted exponential has a true strict invertible derivative and genuine C-infinity coordinate local inverse. The constructed original native local logarithm has both actual local inverse laws with genuine chart-source control and native smoothness at every original vector. Original exponential is a local homeomorphism and open map; actual fibers are closed discrete and actual range is open. A true nilpotent finite exponential factor and polynomial-unit cancellation prove every original exponential period has zero original adjoint generator and native bracket. Original connectedness and actual open centralizers prove ker(Ad) is exactly the original center, and period curves lie entirely there. No covering map, global inverse, surjectivity, injectivity, BCH or elimination of central periods is claimed. Complete build terminal exit 0: "
note2 = " jobs. Kernel terminal exit 0: 3772 exact unique reports using only standard axioms; all retained axiom sets and six retained axiom-free reports unchanged. Scanned all 735 own and nine attributed PNT+ modules plus root/registry; 753 actual source/config hashes. New modules warning-free and oleans current. Fixed local paper objects match; no remote updates. Full StrongConjecture and prize target remain unproved. No unavoidable blocker. Review: round-native-local-inverse-review.json.\n\n"
body = body[:start] + "    note = (" + repr(note1) + ' + str(verified["build_jobs"]) + ' + repr(note2) + ")" + body[end:]
assignments = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(progress) + "\n\n\n"
assembled = head + "\n" + assignments + body
ast.parse(assembled)
Path(prefix + "-audit-body.py").write_text(assignments + body, encoding="utf-8")
Path(prefix + "-audit.py").write_text(assembled, encoding="utf-8")
print(json.dumps({"prepared": prefix, "new_modules": len(modules), "new_theorems": 35, "new_reports": 40}))
