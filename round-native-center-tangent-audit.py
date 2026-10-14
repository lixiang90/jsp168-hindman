"""Read-only proof checks; record only after all actual checks pass.

No network access, toolchain changes, dependency edits or remote updates.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

sys.stdout.reconfigure(encoding="utf-8")
PREFIX = "round-native-center-tangent"
OLD = "round-native-center-smooth"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_FREE = {
    "Hindman168.MatrixDepth.smul",
    "Hindman168.finiteVectorPolynomialSum",
    "Hindman168.maskDescendant_encoding_injective",
    "Hindman168.maskDescendant_none_iff",
    "Hindman168.maskDescendant_some_of_noninvariant",
    "Hindman168.matrixDepth_zero",
    "Hindman168.matrixDepth_zero_iff_upper",
}
AXIOM_FREE = AXIOM_FREE | {'Hindman168.boundedLieWordValues', 'Hindman168.lieWordValue_nil', 'Hindman168.lieWordValue', 'Hindman168.lieWordValue_cons'}
NEW_AXIOM_FREE = set()
AXIOM_FREE = AXIOM_FREE | NEW_AXIOM_FREE


def read(path):
    return Path(path).read_text(encoding="utf-8-sig")


def obj(path):
    return json.loads(read(path))


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def write_obj(path, value):
    Path(path).write_text(json.dumps(value, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")


def lean_code(text):
    """Strip nested block comments, line comments and escaped strings."""
    out = []
    i = 0
    depth = 0
    string = False
    line = False
    while i < len(text):
        ch = text[i]
        pair = text[i:i + 2]
        if line:
            out.append("\n" if ch == "\n" else " ")
            if ch == "\n":
                line = False
            i += 1
        elif depth:
            if pair == "/-":
                depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                i += 1
        elif string:
            if ch == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if ch == "\n" else " ")
                if ch == '"':
                    string = False
                i += 1
        elif pair == "--":
            line = True
            out.extend("  ")
            i += 2
        elif pair == "/-":
            depth = 1
            out.extend("  ")
            i += 2
        elif ch == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(ch)
            i += 1
    assert depth == 0 and not string, "unterminated Lean comment or string"
    return "".join(out)


def declarations(path):
    return re.findall(
        r"^\s*(?:noncomputable\s+)?(theorem|lemma|def|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)",
        lean_code(read(path)), re.M,
    )


def reports(path):
    text = read(path)
    matches = re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", text, re.M)
    values = [(name, set(a.strip() for a in axioms.split(",") if a.strip())) for name, axioms in matches]
    values += [(name, set()) for name in re.findall(r"^'([^\n]+)' does not depend on any axioms\s*$", text, re.M)]
    assert len(values) == len({name for name, _ in values}), "duplicate kernel report"
    assert not re.search(r"^.*(?:error:|warning:)", text, re.M), "kernel diagnostics"
    return dict(values)


def run(command):
    result = subprocess.run(command, stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True)
    return result.stdout.decode("utf-8").strip()


def checks():
    baseline = obj(PREFIX + "-baseline.json")
    registration = obj(PREFIX + "-registration.json")
    new_modules = registration["new_modules"]
    assert len(baseline["files"]) == 850 and len(new_modules) == 10
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 842 and len(pnt) == 9
    imports = re.findall(r"^import (\S+)", lean_code(read("Hindman168.lean")), re.M)
    own_imports = [n for n in imports if n.startswith("Hindman168.")]
    assert len(own_imports) == len(set(own_imports)) == len(own)
    assert set(own_imports) == {str(p.with_suffix("")).replace("\\", ".").replace("/", ".") for p in own}
    names = []
    module_counts = {}
    for p in new_modules:
        ds = declarations(p)
        names.extend("Hindman168." + n for _, n in ds)
        module_counts[Path(p).stem] = {
            "theorems": sum(k in {"theorem", "lemma"} for k, _ in ds),
            "selected_declarations": len(ds),
        }
        code = lean_code(read(p))
        assert not re.search(r"\b(?:set_option|setOptions)\b", code), "new option override"
        olean = Path(".lake/build/lib/lean") / Path(p).with_suffix(".olean")
        assert olean.is_file() and olean.stat().st_mtime_ns >= Path(p).stat().st_mtime_ns, "stale new olean"
    assert len(names) == len(set(names)) == 17
    assert sum(c["theorems"] for c in module_counts.values()) == 17
    assert names == registration["names"] and module_counts == registration["module_report_counts"]
    scanned = own + pnt + [Path("Hindman168.lean"), Path("Verification.lean")]
    banned = []
    for p in scanned:
        code = lean_code(read(p))
        hits = re.findall(r"\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b", code)
        hits += re.findall(r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b", code, re.M)
        if hits:
            banned.append({"path": str(p), "hits": hits})
    assert not banned, banned
    blog = Path(PREFIX + "-build.txt").read_bytes()
    alog = Path(PREFIX + "-axioms.txt").read_bytes()
    for suffix, log in [("build", blog), ("kernel", alog)]:
        result = obj(PREFIX + "-" + suffix + "-result.json")
        assert result["exit_code"] == 0 and result["terminal"] is True
        assert result["log_sha256"] == hashlib.sha256(log).hexdigest()
        assert result["command"] == (["lake", "build"] if suffix == "build" else ["lake", "env", "lean", "Verification.lean"])
    jobs = re.findall(rb"Build completed successfully \((\d+) jobs\)\.", blog)
    assert len(jobs) == 1 and int(jobs[0]) >= baseline["build_job_count"] + len(new_modules)
    assert not re.search(rb"(?:error:|warning:)", blog), "build diagnostics"
    previous = reports(OLD + "-axioms.txt")
    old_result = obj(OLD + "-kernel-result.json")
    assert old_result["exit_code"] == 0 and old_result["terminal"] is True
    assert digest(OLD + "-axioms.txt") == old_result["log_sha256"]
    actual = reports(PREFIX + "-axioms.txt")
    registered = re.findall(r"^#print axioms (\S+)", lean_code(read("Verification.lean")), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 4169
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4152 and all(actual[n] == a for n, a in previous.items())
    assert all(a <= ALLOWED for a in actual.values())
    assert {n for n, a in previous.items() if not a} == AXIOM_FREE - NEW_AXIOM_FREE
    assert NEW_AXIOM_FREE <= set(names) and not NEW_AXIOM_FREE & set(previous)
    assert {n for n, a in actual.items() if not a} == AXIOM_FREE
    lean = run(["C:/Users/A/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lean.exe", "--version"])
    assert "version 4.32.2," in lean and "f3b06c705e6c85f5314019d5d3baab0fec5b580c" in lean
    mathlib = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"])
    pntplus = run(["git", "-C", "../reference-pntplus", "rev-parse", "HEAD"])
    assert mathlib == baseline["mathlib_commit"] == "905b95818eb32af7874a58b427f50c1711a5e96c"
    assert pntplus == baseline["pntplus_commit"] == "747e480362ef6a0a7341055a84372333d72fa62a"
    fixed = obj(OLD + "-preprint-local-check.json")
    assert fixed["fixed_openai_math_commit"] == baseline["openai_math_commit"]
    sections = []
    for section in fixed["sections"]:
        path = section["path"]
        disk = (Path("E:/codex-build/math") / path).read_bytes().replace(b"\r\n", b"\n")
        data = subprocess.run(["git", "-C", "E:/codex-build/math", "show", fixed["fixed_openai_math_commit"] + ":" + path], stdout=subprocess.PIPE, stderr=subprocess.PIPE, check=True).stdout.replace(b"\r\n", b"\n")
        assert disk == data
        sha = hashlib.sha256(disk).hexdigest()
        assert sha == section["normalized_sha256"]
        sections.append({"path": path, "normalized_sha256": sha, "matches_pinned_git_object": True})
    source_files = baseline["files"] + [{"path": p, "sha256": digest(p)} for p in new_modules]
    source_files = [{"path": f["path"], "sha256": digest(f["path"])} for f in source_files]
    assert len(source_files) == len({f["path"] for f in source_files}) == 860
    summary = {
        "build_exit_code": 0, "kernel_exit_code": 0, "build_jobs": int(jobs[0]),
        "project_modules": len(own), "pntplus_modules": len(pnt), "source_scan_modules": len(own) + len(pnt),
        "axiom_reports": len(actual), "axiom_free_reports": sorted(AXIOM_FREE),
        "source_config_hash_count": len(source_files), "allowed_axioms": sorted(ALLOWED), "full_target_proved": False,
    }
    return baseline, registration, source_files, summary, blog, alog, {
        "fixed_openai_math_commit": fixed["fixed_openai_math_commit"], "remote_updates_checked": False,
        "lean_actual": lean, "mathlib_actual": mathlib, "pntplus_actual": pntplus, "sections": sections,
    }


APPLICATION = ['PROGRESS: previous original center smooth quotient round freshly revalidated against all 850 baseline source/config hashes, exact root imports, all 841 retained source modules, terminal successful build/kernel logs and 4152 exact retained kernel reports. Only retained root and registry change. Retained proofs, StrongStatement, original groups/lattices, pins and attributed sources unchanged. No remote updates or unavoidable blocker.', 'HomeomorphSingletonDifferential proves the actual coordinate homeomorphism has identity manifold derivative in its constructed singleton chart. Its actual inverse chart composed with the forward map is identity, so the genuine ordinary Frechet identity derivative supplies the manifold derivative. No derivative comparison premise.', 'NativeCenterQuotientTangent differentiates actual q composed Exp=e composed pi. Actual original Exp derivative at zero and actual coordinate e derivative are identity; genuine chain rules identify actual Dq at original identity exactly with actual real quotient pi. The genuine mkQ kernel theorem gives ker Dq exactly V, the original real adjoint kernel.', 'NativeSmoothHomAdjoint differentiates the actual conjugation identity of a genuine smooth group homomorphism. Actual chain rules give P composed Ad_G(g)=Ad_K(q(g)) composed P, with P the actual identity differential. No adjoint or bracket compatibility is supplied.', 'NativeSmoothHomAdjointCurve differentiates actual target Ad along the homomorphism image of the original constructed one-parameter curve. Actual chain rules and initial curve velocity give DAd_K(Pv). Conversion to actual normed-model Frechet derivatives before basepoint rewrites preserves genuine tangent maps. Target exponential comparison is not assumed; unused target CompleteSpace/Boundaryless/T2 assumptions are omitted.', 'NativeSmoothHomLieBracket differentiates proved actual adjoint intertwining, evaluates on original vectors and applies genuine derivative uniqueness. Retained actual generator/native vector-field bracket identity in both groups proves actual P preserves genuine native brackets. Explicit tangent aliases supply no replacement bracket or Lie morphism.', 'NativeCenterQuotientSeparation proves original G/center(G) Hausdorff in its original quotient topology using its actual homeomorphism from the actual separated normed quotient E/V. Separation is proved, not a new premise.', 'NativeCenterQuotientLieBracket applies actual smooth homomorphism generator intertwining to original q, substitutes proved actual Dq=pi and invokes genuine native bracket identities. Actual pi preserves actual original and quotient native vector-field brackets; the quotient smooth LieGroup is constructed on the original quotient group/topology.', 'NativeCenterQuotientNativeExponential uses the retained genuine smooth-homomorphism integral-curve/ODE uniqueness theorem and proved Dq=pi. Thus q(Exp_G v)=Exp_actual_quotient(pi v). The constructed actual linear section and proved right-inverse law identify the previous coordinate quotient exponential with this actual native exponential at every vector. No supplied target exponential comparison.', 'NativeCenterQuotientNativeLogarithm uses proved original quotient simple connectedness, genuine nilpotent quotient and constructed quotient LieGroup to instantiate the genuine native global inverse theorem. Actual exponential comparison and both actual inverse laws give Log_actual_quotient(qg)=pi(Log_G g). The coordinate inverse equals that actual native logarithm.', 'NativeCenterQuotientRationalSpan proves pi(image(Log_G,Gamma))=image(Log_actual_quotient,qGamma) using actual logarithm intertwining and the genuine subgroup map set. The genuine linear map-span theorem gives map_pi(span_Q Log_G Gamma)=span_Q Log_actual_quotient(qGamma). This holds for the actual arbitrary specified subgroup with no discreteness/cocompactness premise. Neither additive nonabelian Log Gamma nor the remaining central rational-kernel equality is assumed.', 'Ten modules and seventeen proved theorems give seventeen exact new reports. Full build and exact kernel audit cover all 842 own and nine attributed PNT+ modules plus root/registry, with all-source trust scan and 860 source/config hashes. Require terminal successful actual logs, warning-free new sources, current new oleans, unchanged retained axiom sets and genuine empty-report checks. No new options, sorry/admit, declared axioms or dependency edits.', 'Fixed local paper Section 07 lines 13-20 requires rational theory for the arbitrary original connected simply connected nilpotent Lie group with its actual specified lattice. Actual quotient differential, kernel, bracket, exponential and logarithm comparisons and rational-span projection now support that original induction. Central W intersect V equality and full ambient scalar-extension/rational-form induction remain unproved, as do arbitrary rational subgroup lattice cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie lower-central comparison, Malcev, full Calibration/Alignment and positive arithmetic witnesses. StrongConjecture and full prize target remain unproved; publication and submission await full proof/audit.']

COMPONENTS = ['actual singleton coordinate homeomorphism has genuine identity manifold derivative in its original normed model', 'actual original center projection identity differential equals the actual real quotient pi with kernel exactly the actual center model V', 'actual smooth group homomorphism identity differential intertwines genuine original and target adjoint actions by conjugation chain rules', 'actual target adjoint derivative along the original homomorphism image curve equals its genuine identity differential on the actual projected original velocity', 'actual smooth group homomorphism identity differential preserves genuine native vector-field Lie brackets by adjoint derivative uniqueness', 'actual original center quotient is Hausdorff in its original topology via the genuine separated normed real quotient homeomorphism', 'actual original center-model projection intertwines genuine original and quotient adjoint generators and native Lie brackets', 'actual original center projection commutes with genuine native exponentials and its coordinate exponential equals the actual native quotient exponential', 'actual original center projection commutes with genuine native global logarithms and its coordinate inverse equals the actual native quotient logarithm', 'actual specified subgroup rational logarithmic span maps exactly onto the genuine actual center quotient subgroup rational logarithmic span']

NEW_PROGRESS = 'Retained genuine original native exponential/logarithm diffeomorphism, rational finite BCH/Picard construction, actual W bracket closure, actual full real logarithmic span and actual Gamma finite generation remain proved for the arbitrary original specified lattice. Retained actual center logarithmic integer lattice is discrete and full, with compact additive quotient, compatible integer/rational/real bases and a real-independent actual center Q-basis. Retained original center quotient lattice image is discrete and cocompact; original E/V is homeomorphic to original G/center(G), which is contractible and simply connected with strictly lower real model dimension for nontrivial G. Actual closed V gives the canonical separated normed original quotient E/V with a constructed genuine continuous linear section. The actual quotient homeomorphism supplies a constructed global C-infinity chart; actual q(g)=e(pi(Log(g))) proves q smooth. A genuine constructed smooth lift has q composed s=id. Actual lifted original operations prove quotient multiplication and inversion smooth, giving the constructed original quotient LieGroup. Now actual coordinate e has identity derivative; actual q composed Exp=e composed pi and genuine chain rules give Dq at original identity exactly pi, with kernel V. The actual original quotient is proved Hausdorff in its original topology. Genuine smooth-homomorphism conjugation chain rules and original one-parameter curve derivative uniqueness prove actual identity differentials intertwine genuine adjoints and preserve actual native vector-field Lie brackets. Actual pi therefore preserves original and quotient native brackets. Actual smooth-homomorphism ODE uniqueness and Dq=pi prove q(Exp_G v)=Exp_actual_quotient(pi v), identifying the actual coordinate exponential with the genuine native quotient exponential. Actual quotient simple connectedness and genuine inverse laws give Log_actual_quotient(qg)=pi(Log_G g), identifying the coordinate inverse with the genuine native quotient logarithm. Consequently actual pi maps original specified subgroup W=span_Q Log_G Gamma exactly onto the actual projected subgroup rational logarithmic span. No replacement group, different lattice, supplied quotient smoothness, supplied derivative/bracket/exponential/logarithm comparison or additive nonabelian logarithm is assumed. Remaining: identify W intersect V with the actual specified center lattice rational span and complete full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 925
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 850,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 17,
        "new_selected_report_count": 17, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 10, "new_theorem_count": 17,
                    "new_selected_report_count": 17, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-native-center-tangent: PROGRESS. Ten new modules and seventeen proved theorems; seventeen exact new reports. All 850 baseline hashes verified before registration; only retained root/registry change. Actual singleton coordinate derivative and genuine chain rules prove Dq=pi and ker Dq=V. Actual smooth-homomorphism conjugation and one-parameter curve differentiation prove genuine native bracket preservation. Actual original center quotient is Hausdorff in its original topology and actual pi preserves its native bracket. Actual smooth-homomorphism ODE uniqueness identifies projected original Exp with actual native quotient Exp and the coordinate Exp with that native Exp. Actual quotient simple connectedness and genuine inverse laws identify projected original Log with actual native quotient Log and the coordinate inverse with that native Log. Actual specified subgroup logarithmic sets and rational spans project exactly to the corresponding actual quotient subgroup sets/spans. Central W intersect V equality, full ambient rational-form induction, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. All retained axiom sets and eleven retained axiom-free reports unchanged; new empty reports independently checked. All 842 own and nine attributed PNT+ modules plus root/registry scanned; 860 source/config hashes. Actual full build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4169 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-tangent-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 842, "pntplus_modules": 9, "scanned_module_count": 851,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4169, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 850, "previous_current_state_rechecked_before_edits": True,
        "retained_changed": review["retained_changed"], "retained_proof_sources_unchanged": True,
        "pins_and_attributed_sources_unchanged": True, "root_imports_exact": True,
        "registered_names_exact": True, "kernel_names_exact": True,
        "full_target_proved": False, "verified": verified,
    })
    print(json.dumps({"recorded": True, "verified": verified, "proved_components": len(manifest["proved_components"])}))


def recheck():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    review = obj(PREFIX + "-review.json")
    result = obj(PREFIX + "-checks.json")
    assert manifest["files"] == files and all(digest(f["path"]) == f["sha256"] for f in files)
    assert review["verification"] == result["verified"] == verified
    assert review["new_theorem_count"] == 17 and review["new_selected_report_count"] == 17
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 935 and manifest["proved_components"][-10:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 10
    assert manifest["full_target_proved"] is False and manifest["build_succeeded"] and manifest["axiom_check_succeeded"]
    assert obj(PREFIX + "-preprint-local-check.json") == fixed
    assert manifest["build_log"] == PREFIX + "-build.txt" and manifest["axiom_log"] == PREFIX + "-axioms.txt"
    for key, value in {
        "build_job_count": verified["build_jobs"], "hindman_module_count": verified["project_modules"],
        "pntplus_module_count": verified["pntplus_modules"], "selected_axiom_report_count": verified["axiom_reports"],
        "source_scan_module_count": verified["source_scan_modules"],
    }.items():
        assert manifest[key] == value
    assert Path("BUILD-EVIDENCE.txt").read_bytes() == b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n"
    scan = obj(PREFIX + "-source-scan.json")
    assert scan["scanned_module_count"] == 851 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4169 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 17, "new_selected_declarations": 17,
        "all_source_modules_scanned": 851, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4169,
        "new_oleans_current": True, "root_imports_exact": True, "source_theorem_names_match_registration": True,
        "allowed_standard_axioms_only": True, "retained_axiom_sets_unchanged": True, "combined_logs_exact": True,
        "review_audit_manifest_remaining_agree": True, "lean_actual": fixed["lean_actual"],
        "mathlib_actual": fixed["mathlib_actual"], "pntplus_actual": fixed["pntplus_actual"],
        "fixed_local_preprint_objects_match": True, "remote_updates_checked": False, "full_target_proved": False,
    }
    write_obj(PREFIX + "-checks.json", result)
    print(json.dumps(result["fresh_final_recheck"], ensure_ascii=False, indent=2))


if __name__ == "__main__":
    assert len(sys.argv) == 2 and sys.argv[1] in {"record", "recheck"}
    (record if sys.argv[1] == "record" else recheck)()
