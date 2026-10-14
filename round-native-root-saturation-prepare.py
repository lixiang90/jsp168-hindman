"""Extend exact current-state auditing to original center lattice construction."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json
import re

prefix = "round-native-root-saturation"
old_prefix = "round-native-lattice-finite"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
old = module_from_spec(spec)
spec.loader.exec_module(old)
baseline = old.obj(prefix + "-baseline.json")
assert baseline == old.obj("verification-manifest.json")
assert len(baseline["files"]) == 813
assert all(old.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in old.declarations(p)]
assert len(modules) == 10 and len(decls) == 25
assert all(k in {"theorem", "lemma"} for k, _ in decls)


def exact(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before), count)
    return text.replace(before, after)


def simultaneous(text, changes):
    for before, (after, count) in changes.items():
        assert text.count(before) == count, (before, text.count(before), count)
    pattern = re.compile("|".join(re.escape(s) for s in sorted(changes, key=len, reverse=True)))
    return pattern.sub(lambda m: changes[m.group(0)][0], text)


register = old.read(old_prefix + "-register.py")
register = exact(register, '"round-native-lattice-rational-audit.py"', '"' + old_prefix + '-audit.py"')
register = exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = exact(register, 'len(baseline["files"]) == 804', 'len(baseline["files"]) == 813')
register = exact(register, 'len(names) == len(set(names)) == 29', 'len(names) == len(set(names)) == 25')
register = exact(register, 'sum(c["theorems"] for c in counts.values()) == 24', 'sum(c["theorems"] for c in counts.values()) == 25')
register = exact(register, '"baseline_hashes_verified_before_registration": 804', '"baseline_hashes_verified_before_registration": 813')
register = exact(register, '"new_theorems": 24', '"new_theorems": 25')
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
Path(prefix + "-build.py").write_text(exact(old.read(old_prefix + "-build.py"), old_prefix, prefix), encoding="utf-8")
head = old.read(old_prefix + "-audit.py").split("\nAPPLICATION =", 1)[0]
start = head.index("NEW_AXIOM_FREE =")
end = head.index("\n\n\ndef read", start)
head = head[:start] + "AXIOM_FREE = AXIOM_FREE | " + repr(old.NEW_AXIOM_FREE) + "\nNEW_AXIOM_FREE = set()\nAXIOM_FREE = AXIOM_FREE | NEW_AXIOM_FREE" + head[end:]
head = simultaneous(head, {
    'PREFIX = "' + old_prefix + '"': ('PREFIX = "' + prefix + '"', 1),
    'OLD = "round-native-lattice-rational"': ('OLD = "' + old_prefix + '"', 1),
    'len(baseline["files"]) == 804 and len(new_modules) == 9': ('len(baseline["files"]) == 813 and len(new_modules) == 10', 1),
    'len(own) == 795 and len(pnt) == 9': ('len(own) == 805 and len(pnt) == 9', 1),
    'len(names) == len(set(names)) == 29': ('len(names) == len(set(names)) == 25', 1),
    'sum(c["theorems"] for c in module_counts.values()) == 24': ('sum(c["theorems"] for c in module_counts.values()) == 25', 1),
    'len(registered) == len(set(registered)) == len(actual) == 4039': ('len(registered) == len(set(registered)) == len(actual) == 4064', 1),
    'len(previous) == 4010': ('len(previous) == 4039', 1),
    'len(source_files) == len({f["path"] for f in source_files}) == 813': ('len(source_files) == len({f["path"] for f in source_files}) == 823', 1),
})
application = [
    "PROGRESS: freshly rechecked the previous original lattice finite-generation round, including exact source hashes, terminal build/kernel records, retained axiom sets, fixed local paper and actual dependency pins. The 813-file baseline still matches every byte before registration. Only retained root and registry change. No remote updates or unavoidable blocker.",
    "NilpotentFiniteExponentialFixedVector factors the actual finite exponential minus identity as B*Q. The genuine constant-one polynomial Q is a proved unit even at cutoff zero and commutes with B. Applying the factorization to the actual fixed vector and the actual invertible continuous linear operator proves B(w)=0. No fixed-vector kernel equality is supplied as a premise.",
    "NativeLieExponentialCommuteIff uses original group conjugation and true exponential injectivity to turn actual commuting exponentials into an actual adjoint-fixed logarithm vector. The genuine finite adjoint formula and the preceding nilpotent fixed-vector proof give actual B_v(w)=0. The retained true adjoint ODE proves the reverse implication. The resulting equivalence uses the original native Lie bracket, not a matrix replacement or assumed BCH formula.",
    "NativeLiePowerRoots derives Exp(n*v)=Exp(v)^n from the genuine one-parameter law, and Log(g^n)=n*Log(g) from both actual inverse laws. It constructs a root Exp(n^-1*Log(g)) for every positive natural n and proves uniqueness by actual logarithm scalar injectivity. It does not assert closure of the root-saturation set of a specified subgroup.",
    "NativeLatticeCentralizer proves actual center membership of Exp(v) is equivalent to the true adjoint generator being zero. For an element centralizing actual Gamma, genuine commuting detection puts every actual Gamma logarithm in the real-linear generator kernel. The retained proved full real span makes that kernel the original entire model. True global exponential surjectivity then gives centralizer(Gamma)=center(G). Discreteness and finite generation are not used for this equality; actual ambient quotient compactness is.",
    "FiniteCoordinateRecords bounds complete records by an actual finite product of finite coordinate-image subtypes, then proves every finite image has finitely many representatives in its original source. CentralCommutatorRecords proves original central products k*gamma identify the actual commutator [gamma,s] with [k^-1,s]. Equal records on actual subgroup generators extend to the actual generated subgroup by equality of original conjugation homomorphisms, so delta^-1*gamma centralizes Gamma.",
    "DiscreteCentralCommutatorRecords uses actual original continuous commutator images of compact K. Their intersections with actual discrete Gamma are finite by the retained actual discrete compact-intersection theorem. For every finite original generator set the actual central translate records therefore have a finite complete image. No finite commutator record set is assumed.",
    "CenterCompactRepresentatives chooses finite representatives of actual commutator records of Gamma elements with central K-translates. Equal records yield actual central differences through the proved centralizer equality. Every original central element is a finite representative translate times an element in Gamma intersect center(G). The actual finite union of compact K translates, intersected with the actual closed center, is compact. Its actual closed-subtype pullback gives genuine compact representatives inside the natural original center subtype.",
    "CenterLatticeCocompactness proves compactness of any natural coset quotient from actual compact representatives. It also derives discreteness of the actual center intersection using its genuine continuous injective map to the original discrete Gamma. Ambient original compact quotient and local compactness provide the actual K via the proved open quotient representative construction. Combining the actual finite commutator proof gives compactness of center(G)/(Gamma intersect center(G)) under the stated actual centralizer and finite-generation hypotheses.",
    "NativeCenterLattice discharges these generic hypotheses for the actual original arbitrary connected simply connected finite-dimensional nilpotent Lie group and specified lattice. Original Lie smoothness supplies the true topological-group instance; actual exponential diffeomorphism supplies local compactness; retained actual lattice finite generation and the new true centralizer equality give the natural center quotient CompactSpace. No restricted center compactness, replacement lattice, supplied rational form or additive nonabelian Log(Gamma) is assumed.",
    "Ten new modules and 25 proved theorems give 25 exact new reports. Require actual terminal exit-zero full build and kernel records, byte log hashes, exact registration names, all-source trust scan, current new oleans and unchanged retained axioms. All 805 own plus nine attributed PNT+ modules and root/registry are covered; 823 source/config hashes. Eleven retained axiom-free reports remain unchanged; new empty axiom reports are checked against actual output. No new option overrides or proof placeholders.",
    "The actual specified lattice now restricts to a discrete cocompact subgroup of the actual original center. This is a necessary step for central induction on full lattice rational form; it alone does not prove real independence of the original finite Q-basis or cocompactness for every rational subgroup. Positive root uniqueness is proved, but root saturation subgroup closure remains unproved. Full scalar-extension injectivity, arbitrary rational subgroup lattice-intersection cocompactness, quantitative bounds, reverse original group/Lie lower-central comparison, Malcev, full calibration/Alignment and positive ordered arithmetic witnesses remain. StrongConjecture and the full prize target are unproved; publication/submission await full proof and audit.",
]
components = [
    "actual finite exponentials of nilpotent continuous linear operators fix only actual kernel vectors through a proved constant-one polynomial unit",
    "actual commuting exponentials in the original simply connected nilpotent Lie group are equivalent to zero actual native brackets",
    "actual original natural power logarithm identities and explicit unique positive-degree roots follow from true one-parameter and global inverse laws",
    "actual original center membership is zero actual adjoint generator and actual cocompact subgroup centralizers equal the entire original group center",
    "actual finite coordinate images give finite complete commutator records with finite representatives in the original source",
    "actual equal generator commutator records detect differences in the original generated subgroup centralizer",
    "actual discrete original subgroups have finite central compact-translate commutator records by compact image intersections",
    "actual center compact representatives are constructed from finite original commutator record representatives and genuine finite compact translates",
    "actual natural center intersection subgroups are discrete and their natural coset quotients are compact from actual center representatives",
    "actual arbitrary specified original nilpotent Lie group lattices intersect the original center in genuine discrete cocompact center subgroups",
]
progress = (
    "Actual commuting exponentials in the original simply connected nilpotent Lie group now imply zero actual native bracket. "
    "Genuine conjugation and exponential injectivity give an actual adjoint-fixed vector; actual finite adjoint factorization through a proved invertible constant-one polynomial gives the true generator kernel. "
    "The retained genuine adjoint ODE gives the reverse direction. Actual natural powers have Log(g^n)=n*Log(g), and explicit original Exp(n^-1*Log(g)) gives the unique positive-degree root. "
    "Actual center membership is exactly zero actual generator. The actual generator kernel of any Gamma-centralizing element contains every original Gamma logarithm; actual full real spanning therefore makes it zero. "
    "Thus the actual original cocompact subgroup has centralizer equal to the original group center. Original finite group generators give genuine finite commutator records of Gamma elements with central compact K-translates. "
    "Every coordinate equals an actual original compact commutator image value and remains in discrete Gamma, so its actual image is finite. Genuine finite coordinate products give finite complete records and finite source representatives. "
    "Equal actual generator commutator records give equal original conjugation homomorphisms on generated Gamma and hence actual differences centralizing Gamma, which lie in the original center. "
    "The actual finite union of compact K translates by record representatives, intersected with the actual closed original center, therefore supplies compact center representatives modulo the actual Gamma-center intersection. "
    "Actual closed-subtype pullback and the original quotient map prove genuine CompactSpace of center(G)/(Gamma intersect center(G)); a genuine continuous injection into Gamma proves actual restricted lattice discreteness. "
    "For the arbitrary original connected simply connected finite-dimensional real nilpotent Lie group, actual original local compactness, actual specified lattice finite generation and the proved original centralizer equality discharge every auxiliary hypothesis. "
    "No restricted center compactness, supplied full rational form, replacement matrix group, different lattice or additive nonabelian Log(Gamma) is assumed. "
    "Remaining: actual real scalar-extension injectivity and full specified-lattice rational form, including real linear independence of a Q-basis and actual central induction; "
    "arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Positive root uniqueness does not itself prove root-saturation subgroup closure, which remains unproved. Finite Q dimension and full real span do not themselves prove real Q-basis independence. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
new_progress = old.NEW_PROGRESS.split("Remaining:", 1)[0] + progress
body = old.read(old_prefix + "-audit.py")
body = body[body.index("\ndef record():"):]
body = simultaneous(body, {
    'len(manifest["proved_components"]) == 879': ('len(manifest["proved_components"]) == 888', 1),
    '"baseline_hash_count": 804': ('"baseline_hash_count": 813', 1),
    '"new_theorem_count": 24': ('"new_theorem_count": 25', 2),
    '"new_selected_report_count": 29': ('"new_selected_report_count": 25', 2),
    '"new_module_count": 9': ('"new_module_count": 10', 1),
    '"project_modules": 795': ('"project_modules": 805', 1),
    '"scanned_module_count": 804': ('"scanned_module_count": 814', 1),
    '"exact_unique_reports": 4039': ('"exact_unique_reports": 4064', 1),
    '"baseline_hashes_verified_before_registration": 804': ('"baseline_hashes_verified_before_registration": 813', 1),
    'review["new_theorem_count"] == 24': ('review["new_theorem_count"] == 25', 1),
    'review["new_selected_report_count"] == 29': ('review["new_selected_report_count"] == 25', 1),
    'len(manifest["proved_components"]) == 888': ('len(manifest["proved_components"]) == 898', 1),
    'manifest["proved_components"][-9:]': ('manifest["proved_components"][-10:]', 1),
    'len(registration["new_modules"]) == 9': ('len(registration["new_modules"]) == 10', 1),
    'scan["scanned_module_count"] == 804': ('scan["scanned_module_count"] == 814', 1),
    'kernel["exact_unique_reports"] == 4039': ('kernel["exact_unique_reports"] == 4064', 1),
    '"new_theorems": 24': ('"new_theorems": 25', 1),
    '"new_selected_declarations": 29': ('"new_selected_declarations": 25', 1),
    '"all_source_modules_scanned": 804': ('"all_source_modules_scanned": 814', 1),
    '"kernel_exact_unique_reports": 4039': ('"kernel_exact_unique_reports": 4064', 1),
})
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-root-saturation: PROGRESS. Ten new modules, 25 proved theorems and 25 exact new reports. "
    "All 813 baseline hashes verified before registration; only retained root/registry change. True nilpotent finite adjoint fixed-vector kernel and original global exponential injectivity prove commuting iff native bracket zero. "
    "Actual natural power/logarithm identities give explicit unique positive-degree roots. Actual cocompact logarithmic full real span proves centralizer(Gamma)=center(G). "
    "Actual discrete compact commutator images give finite records on original finite generators. Equal records give actual central differences. "
    "An actual finite union of compact translates intersected with the actual closed center constructs genuine compact center representatives. Actual natural quotient image proves center(G)/(Gamma intersect center(G)) compact, and actual subgroup injection proves intersection discreteness. "
    "The arbitrary original nilpotent Lie group and specified lattice discharge all auxiliary hypotheses. Root-saturation subgroup closure, full rational form/real Q-basis independence, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. "
    "Eleven retained axiom-free reports and all retained axiom sets unchanged; actual new empty reports separately checked. All 805 own and nine attributed PNT+ modules plus root/registry scanned; 823 source/config hashes. Actual full build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + ' + str(verified["build_jobs"]) + ' + repr(
    " jobs, 4064 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-root-saturation-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = "APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) + "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 25, "new_reports": 25}))
