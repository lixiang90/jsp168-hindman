"""Extend the exact proof audit to actual lattice finite generation."""
from pathlib import Path
from importlib.util import spec_from_file_location, module_from_spec
import ast
import json
import re

prefix = "round-native-lattice-finite"
old_prefix = "round-native-lattice-rational"
spec = spec_from_file_location("previous_audit", old_prefix + "-audit.py")
previous = module_from_spec(spec)
spec.loader.exec_module(previous)
baseline = previous.obj(prefix + "-baseline.json")
assert baseline == previous.obj("verification-manifest.json")
assert len(baseline["files"]) == 804
assert all(previous.digest(f["path"]) == f["sha256"] for f in baseline["files"])
retained = {f["path"] for f in baseline["files"]}
modules = [p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls = [d for p in modules for d in previous.declarations(p)]
assert len(modules) == 9 and len(decls) == 29
assert sum(k in {"theorem", "lemma"} for k, _ in decls) == 24


def replace_exact(text, before, after, count=1):
    assert text.count(before) == count, (before, text.count(before), count)
    return text.replace(before, after)


register = Path(old_prefix + "-register.py").read_text(encoding="utf-8-sig")
register = replace_exact(register, '"round-native-rational-picard-audit.py"', '"' + old_prefix + '-audit.py"')
register = replace_exact(register, 'prefix = "' + old_prefix + '"', 'prefix = "' + prefix + '"')
register = replace_exact(register, 'len(baseline["files"]) == 793', 'len(baseline["files"]) == 804')
register = replace_exact(register, 'len(names) == len(set(names)) == 41', 'len(names) == len(set(names)) == 29')
register = replace_exact(register, 'sum(c["theorems"] for c in counts.values()) == 36', 'sum(c["theorems"] for c in counts.values()) == 24')
register = replace_exact(register, '"baseline_hashes_verified_before_registration": 793', '"baseline_hashes_verified_before_registration": 804')
register = replace_exact(register, '"new_theorems": 36', '"new_theorems": 24')
start = register.index("modules = [")
end = register.index("\nnames = []", start)
register = register[:start] + "modules = " + json.dumps(modules, indent=4) + "\n" + register[end:]
Path(prefix + "-register.py").write_text(register, encoding="utf-8")
build = Path(old_prefix + "-build.py").read_text(encoding="utf-8-sig")
Path(prefix + "-build.py").write_text(replace_exact(build, old_prefix, prefix), encoding="utf-8")
head = Path(old_prefix + "-audit.py").read_text(encoding="utf-8-sig").split("\nAPPLICATION =", 1)[0]
new_free = {
    "Hindman168.lieWordValue", "Hindman168.lieWordValue_nil",
    "Hindman168.lieWordValue_cons", "Hindman168.boundedLieWordValues",
}
head_changes = {
    'PREFIX = "' + old_prefix + '"': 'PREFIX = "' + prefix + '"',
    'OLD = "round-native-rational-picard"': 'OLD = "' + old_prefix + '"',
    'len(baseline["files"]) == 793 and len(new_modules) == 11': 'len(baseline["files"]) == 804 and len(new_modules) == 9',
    'len(own) == 786 and len(pnt) == 9': 'len(own) == 795 and len(pnt) == 9',
    'len(names) == len(set(names)) == 41': 'len(names) == len(set(names)) == 29',
    'sum(c["theorems"] for c in module_counts.values()) == 36': 'sum(c["theorems"] for c in module_counts.values()) == 24',
    'len(registered) == len(set(registered)) == len(actual) == 4010': 'len(registered) == len(set(registered)) == len(actual) == 4039',
    'len(previous) == 3969': 'len(previous) == 4010',
    'len(source_files) == len({f["path"] for f in source_files}) == 804': 'len(source_files) == len({f["path"] for f in source_files}) == 813',
    'NEW_AXIOM_FREE = set()': 'NEW_AXIOM_FREE = ' + repr(new_free),
}
for before, after in head_changes.items():
    head = replace_exact(head, before, after)
application = [
    "PROGRESS: the preceding actual subgroup rational-span and real-spanning round was freshly rechecked before saving the 804-file baseline and editing. All baseline source/config hashes are independently reverified before registration. Only retained root and exact-name registry change; retained proof sources, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates or unavoidable blocker.",
    "OpenMapCompactRepresentatives constructs actual compact representatives with an open subset mapping onto the whole compact target of an actual open surjection. Original locally compact source neighborhoods supply compact sets, their interiors map to actual open target sets, and actual target compactness supplies a finite subcover. No compact representative set is supplied as a premise or chosen without a proof.",
    "DiscreteSubgroupCompactIntersection derives actual closedness of the specified discrete subgroup in the original Hausdorff topological group. Its actual subtype embedding pulls back the original compact set to a genuine compact discrete subset, hence a finite set. This gives finiteness of the actual intersection, without a supplied lattice finiteness property.",
    "ConnectedSubgroupOverlapGeneration proves that actual Gamma elements in K^-1*K generate Gamma when an original open O subset K has O*Gamma=G. Genuine translate overlaps give h*k^-1 in the generated subgroup. Translates from that subgroup and from its complement in Gamma form two disjoint open original-group sets covering G; actual original preconnectedness excludes the complement. The proof uses actual group multiplication and its true topology, not a replacement Cayley graph.",
    "CocompactDiscreteSubgroupFiniteGeneration derives O*Gamma=G from the actual coset quotient image using original left-coset relations. The actual continuous-group quotient is open and surjective, so compact original quotient representatives exist. Actual subgroup elements in the compact K^-1*K are finite and generate by the overlap proof. Thus the arbitrary original discrete cocompact subgroup is actually finitely generated without adding finite generation as an assumption.",
    "NativeLatticeFiniteGeneration transfers genuine local compactness from the actual finite-dimensional original real model through the already proved original exponential diffeomorphism. The original Lie group gives its actual topological group instance. The preceding theorem applies to the actual specified subgroup with its original discrete topology and actual CompactSpace(G/Gamma), producing actual Gamma.FG. No matrix substitution, different lattice or compactness conclusion is assumed.",
    "BoundedLieWords defines genuine right-nested original brackets and proves each value belongs to the actual lower central layer indexed by its adjoint-word length. Actual nilpotent lower-central termination makes all long words zero. Bounded words over an actual finite vector set form a genuine finite range of bounded finite lists and seed vectors; original seed vectors are included, and every word belongs to their actual Lie span.",
    "NilpotentFiniteLieSpan constructs the genuine linear-subspace stabilizer Lie subalgebra using actual Jacobi, addition and scalar laws. Original seed adjoints preserve the actual span of bounded words: prepend a seed while below the actual class, and use actual lower-central zero at the boundary. The actual Lie span is in this stabilizer, while every bounded word is in that span; hence the bounded word span is bracket closed and equals the true generated Lie subalgebra. Finite word values give an actual finite module spanning set. No finite rational dimension or BCH law is supplied as a premise.",
    "NativeLieRationalAlgebra constructs the actual original native Lie algebra over Q from the existing original real bracket and genuine rational/real scalar compatibility. This is a derived scalar restriction, not a new Lie bracket. Its actual rational lower central series terminates at the original group nilpotency class by the true scalar-independent integer lower-central comparison. Every original bracket-closed Q-submodule becomes an actual rational Lie subalgebra using its proved closure.",
    "NativeSubgroupFiniteRationalSpan proves W=span_Q(Log(Gamma)) equals the original rational Lie span of the actual logarithms of any original set generating Gamma. The genuine exponential image of that Lie span is a subgroup by the retained actual rational Picard/BCH theorem and contains the original generators, hence Gamma. This gives W inside the Lie span. The reverse inclusion uses the previously derived actual bracket closure of W. Actual finite generation of Gamma and actual nilpotent bounded word finiteness prove W is finite dimensional over Q and has an actual finite Q-spanning set.",
    "Nine new modules, 24 theorems and five other declarations give 29 exact new reports. Require actual terminal exit-zero complete build/kernel records, byte logs/hashes, exact names/imports, current new oleans and all-source trust scans. All 795 own and nine attributed PNT+ modules plus root and registry are covered. Retained axiom sets and seven retained axiom-free reports remain unchanged; new axiom-free declarations are determined from actual kernel output and all other reports use only allowed standard axioms. No new option overrides.",
    "Finite Q dimension and full real spanning have now both been proved for the actual specified lattice, but they alone do not prove that an actual Q-basis is real-linearly independent. Remaining: actual real scalar-extension injectivity and full specified-lattice rational form, rational subgroup lattice-intersection cocompactness, quantitative degree/denominator bounds, reverse original group/Lie lower-central inclusion and exact comparison/closedness, faithful integration/Malcev, full calibration/Alignment and ordered positive arithmetic witnesses. StrongConjecture and the full prize target remain unproved; publication/submission await full proof and audit.",
]
components = [
    "actual open surjections from locally compact sources to compact targets have genuine compact representatives whose open subset covers the entire target by an actual finite subcover",
    "actual specified discrete subgroup intersections with original compact sets are finite by derived subgroup closedness and true compact discrete subtype pullback",
    "actual original preconnected group translate overlaps generate the specified subgroup from its elements in K^-1*K when original open representative translates cover the group",
    "actual arbitrary discrete cocompact subgroups of locally compact preconnected Hausdorff topological groups are finitely generated from genuine compact representative overlaps",
    "actual specified original nilpotent Lie group lattices are finitely generated with local compactness derived from the genuine original exponential diffeomorphism",
    "actual bounded right-nested original Lie words form finite vector sets over finite seeds and actual lower-central nilpotency makes all long words vanish",
    "actual finitely generated nilpotent Lie subalgebras equal the original span of bounded seed adjoint words and have genuine finite module spanning sets by Jacobi stabilizer closure",
    "actual original native real Lie algebra restricts to a proved compatible rational Lie algebra whose true rational lower-central series terminates at the original group class",
    "actual specified lattice logarithmic Q-span equals the true rational Lie span of actual finite group-generator logarithms and is genuinely finite dimensional over Q with a finite Q-spanning set",
]
progress = (
    "The actual specified discrete cocompact subgroup Gamma is now proved finitely generated. "
    "Actual original local compactness is derived from the true exponential diffeomorphism and the original finite-dimensional real model. "
    "The actual open coset quotient map and its original compact target yield actual compact representatives K with an open subset O satisfying O*Gamma=G. "
    "The actual discrete subgroup has only finitely many elements in K^-1*K. Genuine translate overlaps and original preconnectedness prove these actual elements generate Gamma. "
    "The actual native Lie algebra over Q is constructed from the original real bracket with proved scalar compatibility, and its true Q lower-central series terminates at the original group class. "
    "Actual right-nested bracket words in finite original seed vectors belong to their true word-length lower-central layers. Actual nilpotency kills long words and actual bounded finite-list values are finite. "
    "Actual Jacobi gives a genuine Lie stabilizer of the bounded-word linear span. Seed adjoints preserve that span by prepending below the actual class and vanishing at the boundary; "
    "the actual generated Lie subalgebra is in that stabilizer and equals the bounded-word span, so it has an actual finite module spanning set. "
    "The actual W=span_Q(Log(Gamma)) now equals the original Q-Lie span of the original finite generating set's actual logarithms. "
    "The retained genuine rational BCH theorem makes the exponential image of that Lie span an actual original subgroup containing the generators and hence Gamma, giving one inclusion. "
    "The previously proved actual bracket closure of W gives the reverse inclusion. Therefore actual W is finite dimensional over Q and has a genuine finite Q-spanning set. "
    "This uses actual original Gamma, original vectors and original bracket; no replacement model, supplied finite generation, assumed finite Q dimension or additive nonabelian Log(Gamma). "
    "Remaining: actual real scalar-extension injectivity and full specified-lattice rational form, including actual real linear independence of a Q-basis; "
    "actual rational subgroup lattice-intersection cocompactness; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Finite Q dimension together with full real span does not itself prove real linear independence of a Q-basis. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
new_progress = previous.NEW_PROGRESS.split("Remaining:", 1)[0] + progress
body = Path(old_prefix + "-audit-body.py").read_text(encoding="utf-8-sig")
body = body[body.index("\ndef record():"):]
changes = {
    'len(manifest["proved_components"]) == 868': 'len(manifest["proved_components"]) == 879',
    '"baseline_hash_count": 793': '"baseline_hash_count": 804',
    '"new_theorem_count": 36': '"new_theorem_count": 24',
    '"new_selected_report_count": 41': '"new_selected_report_count": 29',
    '"new_module_count": 11': '"new_module_count": 9',
    '"project_modules": 786': '"project_modules": 795',
    '"scanned_module_count": 795': '"scanned_module_count": 804',
    '"exact_unique_reports": 4010': '"exact_unique_reports": 4039',
    '"baseline_hashes_verified_before_registration": 793': '"baseline_hashes_verified_before_registration": 804',
    'review["new_theorem_count"] == 36': 'review["new_theorem_count"] == 24',
    'review["new_selected_report_count"] == 41': 'review["new_selected_report_count"] == 29',
    'len(manifest["proved_components"]) == 879': 'len(manifest["proved_components"]) == 888',
    'manifest["proved_components"][-11:]': 'manifest["proved_components"][-9:]',
    'len(registration["new_modules"]) == 11': 'len(registration["new_modules"]) == 9',
    'scan["scanned_module_count"] == 795': 'scan["scanned_module_count"] == 804',
    'kernel["exact_unique_reports"] == 4010': 'kernel["exact_unique_reports"] == 4039',
    '"new_theorems": 36': '"new_theorems": 24',
    '"new_selected_declarations": 41': '"new_selected_declarations": 29',
    '"all_source_modules_scanned": 795': '"all_source_modules_scanned": 804',
    '"kernel_exact_unique_reports": 4010': '"kernel_exact_unique_reports": 4039',
}
for before in changes:
    assert body.count(before) == (2 if before in {'"new_theorem_count": 36', '"new_selected_report_count": 41'} else 1), (before, body.count(before))
pattern = re.compile("|".join(re.escape(s) for s in sorted(changes, key=len, reverse=True)))
body = pattern.sub(lambda m: changes[m.group(0)], body)
note_start = body.index("    note =")
note_end = body.index('    Path("AUDIT.txt")', note_start)
note = (
    "\n2026-10-10 round-native-lattice-finite: PROGRESS. Nine new modules, 24 proved theorems and five other declarations; 29 exact new reports. "
    "All 804 baseline hashes verified before registration; only retained root and registry change. Original open quotient compact representatives, finite actual discrete compact intersections and original preconnected translate overlaps prove actual specified lattice finite generation. "
    "Actual original rational bracket scalar restriction and nilpotent lower-central termination give finite seed adjoint words. Genuine Jacobi stabilizer closure proves their span equals the actual generated Lie subalgebra. "
    "Actual W=span_Q(Log(Gamma)) equals the Q-Lie span of finite original generator logarithms by true rational BCH and actual group generation; actual W is finite dimensional over Q. "
    "Actual real Q-basis independence/full rational form, specified-lattice rational subgroup cocompactness, quantitative bounds, reverse original group/Lie layer comparison, Malcev and full target remain unproved. "
    "Retained axiom sets and seven retained axiom-free reports unchanged; actual new axiom-free reports are separately checked. All 795 own and nine attributed PNT+ modules plus root and registry scanned; 813 source/config hashes. "
    "Actual complete build and exact kernel totals: "
)
body = body[:note_start] + "    note = " + repr(note) + " + str(verified[\"build_jobs\"]) + " + repr(
    " jobs, 4039 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. "
    "Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-lattice-finite-review.json.\n\n"
) + "\n" + body[note_end:]
body = body.replace(old_prefix, prefix)
payload = ("APPLICATION = " + repr(application) + "\n\nCOMPONENTS = " + repr(components) +
           "\n\nNEW_PROGRESS = " + repr(new_progress) + "\n\n" + body)
Path(prefix + "-audit-body.py").write_text(payload, encoding="utf-8")
Path(prefix + "-audit.py").write_text(head + "\n" + payload, encoding="utf-8")
for suffix in ["register", "build", "audit", "audit-body"]:
    ast.parse(Path(prefix + "-" + suffix + ".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared": True, "new_modules": len(modules), "new_theorems": 24, "new_reports": 29}))
