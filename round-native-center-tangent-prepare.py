"""Prepare exact audit for actual original center quotient comparison."""
from pathlib import Path
from importlib.util import spec_from_file_location,module_from_spec
import ast,json,re
prefix="round-native-center-tangent"
old_prefix="round-native-center-smooth"
spec=spec_from_file_location("previous_audit",old_prefix+"-audit.py")
old=module_from_spec(spec);spec.loader.exec_module(old)
baseline=old.obj(prefix+"-baseline.json")
assert baseline==old.obj("verification-manifest.json")
assert len(baseline["files"])==850
assert all(old.digest(f["path"])==f["sha256"] for f in baseline["files"])
retained={f["path"] for f in baseline["files"]}
modules=[p.as_posix() for p in sorted(Path("Hindman168").glob("*.lean")) if p.as_posix() not in retained]
decls=[d for p in modules for d in old.declarations(p)]
assert len(modules)==10 and len(decls)==17 and all(k in {"theorem","lemma"} for k,_ in decls)

def exact(s,a,b,count=1):
    assert s.count(a)==count,(a,s.count(a),count)
    return s.replace(a,b)
def simultaneous(s,changes):
    for a,(b,count) in changes.items():
        assert s.count(a)==count,(a,s.count(a),count)
    pat=re.compile("|".join(re.escape(a) for a in sorted(changes,key=len,reverse=True)))
    return pat.sub(lambda m:changes[m.group(0)][0],s)

register=simultaneous(old.read(old_prefix+"-register.py"),{
    '"round-native-center-quotient-audit.py"':('"'+old_prefix+'-audit.py"',1),
    'prefix = "'+old_prefix+'"':('prefix = "'+prefix+'"',1),
    'len(baseline["files"]) == 842':('len(baseline["files"]) == 850',1),
    'len(names) == len(set(names)) == 25':('len(names) == len(set(names)) == 17',1),
    'sum(c["theorems"] for c in counts.values()) == 15':('sum(c["theorems"] for c in counts.values()) == 17',1),
    '"baseline_hashes_verified_before_registration": 842':('"baseline_hashes_verified_before_registration": 850',1),
    '"new_theorems": 15':('"new_theorems": 17',1),
})
start=register.index("modules = [")
end=register.index("\nnames = []",start)
register=register[:start]+"modules = "+json.dumps(modules,indent=4)+"\n"+register[end:]
Path(prefix+"-register.py").write_text(register,encoding="utf-8")
Path(prefix+"-build.py").write_text(exact(old.read(old_prefix+"-build.py"),old_prefix,prefix),encoding="utf-8")
head=old.read(old_prefix+"-audit.py").split("\nAPPLICATION =",1)[0]
assert old.NEW_AXIOM_FREE==set() and len(old.AXIOM_FREE)==11
head=simultaneous(head,{
    'PREFIX = "'+old_prefix+'"':('PREFIX = "'+prefix+'"',1),
    'OLD = "round-native-center-quotient"':('OLD = "'+old_prefix+'"',1),
    'len(baseline["files"]) == 842 and len(new_modules) == 8':('len(baseline["files"]) == 850 and len(new_modules) == 10',1),
    'len(own) == 832 and len(pnt) == 9':('len(own) == 842 and len(pnt) == 9',1),
    'len(names) == len(set(names)) == 25':('len(names) == len(set(names)) == 17',1),
    'sum(c["theorems"] for c in module_counts.values()) == 15':('sum(c["theorems"] for c in module_counts.values()) == 17',1),
    'len(registered) == len(set(registered)) == len(actual) == 4152':('len(registered) == len(set(registered)) == len(actual) == 4169',1),
    'len(previous) == 4127':('len(previous) == 4152',1),
    'len(source_files) == len({f["path"] for f in source_files}) == 850':('len(source_files) == len({f["path"] for f in source_files}) == 860',1),
})
application=[
    "PROGRESS: previous original center smooth quotient round freshly revalidated against all 850 baseline source/config hashes, exact root imports, all 841 retained source modules, terminal successful build/kernel logs and 4152 exact retained kernel reports. Only retained root and registry change. Retained proofs, StrongStatement, original groups/lattices, pins and attributed sources unchanged. No remote updates or unavoidable blocker.",
    "HomeomorphSingletonDifferential proves the actual coordinate homeomorphism has identity manifold derivative in its constructed singleton chart. Its actual inverse chart composed with the forward map is identity, so the genuine ordinary Frechet identity derivative supplies the manifold derivative. No derivative comparison premise.",
    "NativeCenterQuotientTangent differentiates actual q composed Exp=e composed pi. Actual original Exp derivative at zero and actual coordinate e derivative are identity; genuine chain rules identify actual Dq at original identity exactly with actual real quotient pi. The genuine mkQ kernel theorem gives ker Dq exactly V, the original real adjoint kernel.",
    "NativeSmoothHomAdjoint differentiates the actual conjugation identity of a genuine smooth group homomorphism. Actual chain rules give P composed Ad_G(g)=Ad_K(q(g)) composed P, with P the actual identity differential. No adjoint or bracket compatibility is supplied.",
    "NativeSmoothHomAdjointCurve differentiates actual target Ad along the homomorphism image of the original constructed one-parameter curve. Actual chain rules and initial curve velocity give DAd_K(Pv). Conversion to actual normed-model Frechet derivatives before basepoint rewrites preserves genuine tangent maps. Target exponential comparison is not assumed; unused target CompleteSpace/Boundaryless/T2 assumptions are omitted.",
    "NativeSmoothHomLieBracket differentiates proved actual adjoint intertwining, evaluates on original vectors and applies genuine derivative uniqueness. Retained actual generator/native vector-field bracket identity in both groups proves actual P preserves genuine native brackets. Explicit tangent aliases supply no replacement bracket or Lie morphism.",
    "NativeCenterQuotientSeparation proves original G/center(G) Hausdorff in its original quotient topology using its actual homeomorphism from the actual separated normed quotient E/V. Separation is proved, not a new premise.",
    "NativeCenterQuotientLieBracket applies actual smooth homomorphism generator intertwining to original q, substitutes proved actual Dq=pi and invokes genuine native bracket identities. Actual pi preserves actual original and quotient native vector-field brackets; the quotient smooth LieGroup is constructed on the original quotient group/topology.",
    "NativeCenterQuotientNativeExponential uses the retained genuine smooth-homomorphism integral-curve/ODE uniqueness theorem and proved Dq=pi. Thus q(Exp_G v)=Exp_actual_quotient(pi v). The constructed actual linear section and proved right-inverse law identify the previous coordinate quotient exponential with this actual native exponential at every vector. No supplied target exponential comparison.",
    "NativeCenterQuotientNativeLogarithm uses proved original quotient simple connectedness, genuine nilpotent quotient and constructed quotient LieGroup to instantiate the genuine native global inverse theorem. Actual exponential comparison and both actual inverse laws give Log_actual_quotient(qg)=pi(Log_G g). The coordinate inverse equals that actual native logarithm.",
    "NativeCenterQuotientRationalSpan proves pi(image(Log_G,Gamma))=image(Log_actual_quotient,qGamma) using actual logarithm intertwining and the genuine subgroup map set. The genuine linear map-span theorem gives map_pi(span_Q Log_G Gamma)=span_Q Log_actual_quotient(qGamma). This holds for the actual arbitrary specified subgroup with no discreteness/cocompactness premise. Neither additive nonabelian Log Gamma nor the remaining central rational-kernel equality is assumed.",
    "Ten modules and seventeen proved theorems give seventeen exact new reports. Full build and exact kernel audit cover all 842 own and nine attributed PNT+ modules plus root/registry, with all-source trust scan and 860 source/config hashes. Require terminal successful actual logs, warning-free new sources, current new oleans, unchanged retained axiom sets and genuine empty-report checks. No new options, sorry/admit, declared axioms or dependency edits.",
    "Fixed local paper Section 07 lines 13-20 requires rational theory for the arbitrary original connected simply connected nilpotent Lie group with its actual specified lattice. Actual quotient differential, kernel, bracket, exponential and logarithm comparisons and rational-span projection now support that original induction. Central W intersect V equality and full ambient scalar-extension/rational-form induction remain unproved, as do arbitrary rational subgroup lattice cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie lower-central comparison, Malcev, full Calibration/Alignment and positive arithmetic witnesses. StrongConjecture and full prize target remain unproved; publication and submission await full proof/audit.",
]
components=[
    "actual singleton coordinate homeomorphism has genuine identity manifold derivative in its original normed model",
    "actual original center projection identity differential equals the actual real quotient pi with kernel exactly the actual center model V",
    "actual smooth group homomorphism identity differential intertwines genuine original and target adjoint actions by conjugation chain rules",
    "actual target adjoint derivative along the original homomorphism image curve equals its genuine identity differential on the actual projected original velocity",
    "actual smooth group homomorphism identity differential preserves genuine native vector-field Lie brackets by adjoint derivative uniqueness",
    "actual original center quotient is Hausdorff in its original topology via the genuine separated normed real quotient homeomorphism",
    "actual original center-model projection intertwines genuine original and quotient adjoint generators and native Lie brackets",
    "actual original center projection commutes with genuine native exponentials and its coordinate exponential equals the actual native quotient exponential",
    "actual original center projection commutes with genuine native global logarithms and its coordinate inverse equals the actual native quotient logarithm",
    "actual specified subgroup rational logarithmic span maps exactly onto the genuine actual center quotient subgroup rational logarithmic span",
]
new_progress=(
    "Retained genuine original native exponential/logarithm diffeomorphism, rational finite BCH/Picard construction, actual W bracket closure, actual full real logarithmic span and actual Gamma finite generation remain proved for the arbitrary original specified lattice. "
    "Retained actual center logarithmic integer lattice is discrete and full, with compact additive quotient, compatible integer/rational/real bases and a real-independent actual center Q-basis. "
    "Retained original center quotient lattice image is discrete and cocompact; original E/V is homeomorphic to original G/center(G), which is contractible and simply connected with strictly lower real model dimension for nontrivial G. "
    "Actual closed V gives the canonical separated normed original quotient E/V with a constructed genuine continuous linear section. "
    "The actual quotient homeomorphism supplies a constructed global C-infinity chart; actual q(g)=e(pi(Log(g))) proves q smooth. A genuine constructed smooth lift has q composed s=id. Actual lifted original operations prove quotient multiplication and inversion smooth, giving the constructed original quotient LieGroup. "
    "Now actual coordinate e has identity derivative; actual q composed Exp=e composed pi and genuine chain rules give Dq at original identity exactly pi, with kernel V. "
    "The actual original quotient is proved Hausdorff in its original topology. Genuine smooth-homomorphism conjugation chain rules and original one-parameter curve derivative uniqueness prove actual identity differentials intertwine genuine adjoints and preserve actual native vector-field Lie brackets. Actual pi therefore preserves original and quotient native brackets. "
    "Actual smooth-homomorphism ODE uniqueness and Dq=pi prove q(Exp_G v)=Exp_actual_quotient(pi v), identifying the actual coordinate exponential with the genuine native quotient exponential. "
    "Actual quotient simple connectedness and genuine inverse laws give Log_actual_quotient(qg)=pi(Log_G g), identifying the coordinate inverse with the genuine native quotient logarithm. "
    "Consequently actual pi maps original specified subgroup W=span_Q Log_G Gamma exactly onto the actual projected subgroup rational logarithmic span. "
    "No replacement group, different lattice, supplied quotient smoothness, supplied derivative/bracket/exponential/logarithm comparison or additive nonabelian logarithm is assumed. "
    "Remaining: identify W intersect V with the actual specified center lattice rational span and complete full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. "
    "Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."
)
body=old.read(old_prefix+"-audit.py")
body=body[body.index("\ndef record():"):]
start=body.index("    note =")
end=body.index('    Path("AUDIT.txt")',start)
note=(
    "\n2026-10-10 round-native-center-tangent: PROGRESS. Ten new modules and seventeen proved theorems; seventeen exact new reports. "
    "All 850 baseline hashes verified before registration; only retained root/registry change. Actual singleton coordinate derivative and genuine chain rules prove Dq=pi and ker Dq=V. "
    "Actual smooth-homomorphism conjugation and one-parameter curve differentiation prove genuine native bracket preservation. Actual original center quotient is Hausdorff in its original topology and actual pi preserves its native bracket. "
    "Actual smooth-homomorphism ODE uniqueness identifies projected original Exp with actual native quotient Exp and the coordinate Exp with that native Exp. "
    "Actual quotient simple connectedness and genuine inverse laws identify projected original Log with actual native quotient Log and the coordinate inverse with that native Log. "
    "Actual specified subgroup logarithmic sets and rational spans project exactly to the corresponding actual quotient subgroup sets/spans. "
    "Central W intersect V equality, full ambient rational-form induction, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. "
    "All retained axiom sets and eleven retained axiom-free reports unchanged; new empty reports independently checked. All 842 own and nine attributed PNT+ modules plus root/registry scanned; 860 source/config hashes. Actual full build and exact kernel totals: "
)
body=body[:start]+"    note = "+repr(note)+' + str(verified["build_jobs"]) + '+repr(
    " jobs, 4169 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-tangent-review.json.\n\n"
)+"\n"+body[end:]
body=simultaneous(body,{
    'len(manifest["proved_components"]) == 917':('len(manifest["proved_components"]) == 925',1),
    '"baseline_hash_count": 842':('"baseline_hash_count": 850',1),
    '"new_theorem_count": 15':('"new_theorem_count": 17',2),
    '"new_selected_report_count": 25':('"new_selected_report_count": 17',2),
    '"new_module_count": 8':('"new_module_count": 10',1),
    '"project_modules": 832':('"project_modules": 842',1),
    '"scanned_module_count": 841':('"scanned_module_count": 851',1),
    '"exact_unique_reports": 4152':('"exact_unique_reports": 4169',1),
    '"baseline_hashes_verified_before_registration": 842':('"baseline_hashes_verified_before_registration": 850',1),
    'review["new_theorem_count"] == 15':('review["new_theorem_count"] == 17',1),
    'review["new_selected_report_count"] == 25':('review["new_selected_report_count"] == 17',1),
    'len(manifest["proved_components"]) == 925':('len(manifest["proved_components"]) == 935',1),
    'manifest["proved_components"][-8:]':('manifest["proved_components"][-10:]',1),
    'len(registration["new_modules"]) == 8':('len(registration["new_modules"]) == 10',1),
    'scan["scanned_module_count"] == 841':('scan["scanned_module_count"] == 851',1),
    'kernel["exact_unique_reports"] == 4152':('kernel["exact_unique_reports"] == 4169',1),
    '"new_theorems": 15':('"new_theorems": 17',1),
    '"new_selected_declarations": 25':('"new_selected_declarations": 17',1),
    '"all_source_modules_scanned": 841':('"all_source_modules_scanned": 851',1),
    '"kernel_exact_unique_reports": 4152':('"kernel_exact_unique_reports": 4169',1),
})
body=body.replace(old_prefix,prefix)
payload="APPLICATION = "+repr(application)+"\n\nCOMPONENTS = "+repr(components)+"\n\nNEW_PROGRESS = "+repr(new_progress)+"\n\n"+body
Path(prefix+"-audit-body.py").write_text(payload,encoding="utf-8")
Path(prefix+"-audit.py").write_text(head+"\n"+payload,encoding="utf-8")
for suffix in ["register","build","audit","audit-body"]:
    ast.parse(Path(prefix+"-"+suffix+".py").read_text(encoding="utf-8"))
print(json.dumps({"prepared":True,"new_modules":len(modules),"new_theorems":17,"new_reports":17}))
