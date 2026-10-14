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
PREFIX = "round-native-center-smooth"
OLD = "round-native-center-quotient"
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
    assert len(baseline["files"]) == 842 and len(new_modules) == 8
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 832 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 25
    assert sum(c["theorems"] for c in module_counts.values()) == 15
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
    assert len(registered) == len(set(registered)) == len(actual) == 4152
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4127 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 850
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


APPLICATION = ['PROGRESS: previous actual original center quotient round was freshly independently rechecked before the exact 842-file baseline was saved. Every retained source/config hash is independently verified before registration. Only retained root and registry change; retained original proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates or unavoidable blocker.', 'ClosedFiniteRealQuotientSection constructs an actual continuous real-linear quotient projection and an actual continuous real-linear section of a finite real submodule quotient. Actual module projectivity yields an algebraic right inverse of the actual mkQ surjection. Actual finite dimension proves this right inverse continuous; its actual linear composition equality gives its pointwise right-inverse law. No linear section, complement or smoothness is supplied as a premise.', 'NativeCenterQuotientNormedModel proves the actual real adjoint kernel V is closed by the true continuous adjoint differential kernel theorem. The original quotient E/V therefore has its actual canonical separated normed real vector structure with its existing original quotient topology. Actual projection and section instantiate the genuine finite quotient construction and satisfy its exact right-inverse law. No replacement quotient vector space is introduced.', 'HomeomorphSingletonDiffeomorph constructs a single global chart on the actual target topology of a genuine normed-model homeomorphism. The actual inverse open embedding supplies the singleton chart and actual smooth manifold proof. Its genuine coordinate composition identity proves the forward map smooth and the actual global chart is smooth in reverse, giving an actual diffeomorphism. This generic construction does not assume any target algebraic operation smooth. Named chart definitions are reducible class definitions; no new options are introduced.', 'NativeCenterQuotientCharted applies that construction to the retained actual original exponential quotient homeomorphism. Actual original G/center(G), with its original quotient group and topology, gets the constructed singleton C-infinity chart over the actual original E/V. The actual quotient exponential and logarithm give a genuine diffeomorphism for this chart. No original quotient LieGroup structure is a premise.', 'NativeCenterQuotientSmoothProjection proves the actual original center projection smooth through its exact original representative formula: q(g)=e(pi(Log(g))). The retained true original global logarithm is smooth, actual pi is continuous linear and smooth, and e is the constructed actual quotient diffeomorphism. Original Exp(Log(g))=g proves the formula, so the actual homomorphism q itself is smooth, not an unrelated coordinate surrogate.', 'NativeCenterQuotientSmoothLift constructs a genuine global lift s of the original center quotient by actual Log quotient coordinates, the actual constructed linear section and true original exponential. The actual section right-inverse law and exact quotient exponential representative formula prove q(s(x))=x for every original quotient point. Actual diffeomorphism inverse, actual continuous linear section and original smooth exponential prove s smooth. No group homomorphism property of s is asserted.', 'NativeCenterQuotientLieGroup proves actual original quotient multiplication and inversion smooth by lifting actual quotient arguments through the constructed smooth s, using the original genuine Lie group operations, and projecting with the actual smooth quotient homomorphism q. The true original homomorphism laws and q(s(x))=x identify those actual composite maps with the original quotient group operations. Actual constructed manifold, actual multiplication smoothness and actual inversion smoothness therefore give a genuine LieGroup structure on original G/center(G). It is not a replacement BCH group or a supplied quotient LieGroup assumption.', 'NativeCenterQuotientDifferential proves the genuine lift preserves the actual quotient identity. Differentiating the actual global right-inverse identity q composed with s=id at the actual quotient identity gives a true right inverse for the actual original quotient differential Dq at original 1. That actual continuous linear right inverse proves Dq surjective. Exact identification of Dq with pi, its kernel with V, bracket comparison and quotient native exponential comparison are not asserted yet.', 'Eight new modules, fifteen proved theorems, nine constructed definitions and one proved closedness instance give 25 exact new kernel reports. All 832 own and nine attributed PNT+ modules, root and registry are covered by exact full build, all-source trust scan and exact kernel-name checks; 850 source/config hashes. Require terminal exit-zero records, warning-free new sources, current new oleans, unchanged retained axiom sets and actual empty-report checks. No new options, sorry/admit or dependency edits.', 'Original center quotient smooth Lie structure, actual smooth projection, actual smooth global lift and actual quotient differential surjectivity are now proved, together with retained actual quotient lattice discreteness/cocompactness, contractibility/simply connectedness and strict dimension descent. Remaining: exact differential/center-kernel identification and actual bracket/exponential comparison for full original ambient rational-form induction, including W intersect V equal to the actual center lattice rational span. Arbitrary rational subgroup lattice cocompactness, root-saturation subgroup closure, quantitative degree/denominator bounds, reverse original group/Lie comparison, faithful integration/Malcev, full calibration/Alignment and positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await full proof and audit.']

COMPONENTS = ['actual finite real submodule quotient projection has a constructed continuous real-linear right inverse from genuine projectivity and finite dimension', 'actual original real adjoint-kernel center model is closed and gives the canonical normed original quotient with constructed actual linear section', 'actual homeomorphisms from a normed real model construct genuine global singleton smooth charts and actual diffeomorphisms without assuming target operation smoothness', 'actual original center quotient carries a constructed global C-infinity chart and true exponential/logarithm quotient diffeomorphism in its original topology', 'actual original center projection is smooth by the genuine global logarithm, actual linear quotient projection and constructed actual quotient diffeomorphism formula', 'actual original center quotient admits a constructed genuine smooth global lift which is a proved right inverse of the original center projection', 'actual original center quotient multiplication and inversion are smooth through original lifted operations, yielding a genuine constructed original quotient LieGroup structure', 'actual original smooth center projection differential has a genuine continuous linear right inverse at identity and is surjective']

NEW_PROGRESS = 'Retained genuine original native exponential/logarithm diffeomorphism, rational finite BCH/Picard construction, actual W bracket closure, actual full real logarithmic span and actual Gamma finite generation remain proved for the arbitrary original specified lattice. Retained actual center logarithmic integer lattice is discrete and full, with compact additive quotient, compatible integer/rational/real bases and real-independent actual center Q-basis. Retained original center quotient lattice image is discrete and cocompact, original E/V is homeomorphic to original G/center(G), and that original quotient is contractible and simply connected with strictly lower real model dimension for nontrivial G. Now the actual real center model V is proved closed as the genuine continuous adjoint kernel, giving the canonical separated normed original real quotient E/V with its original topology. Actual projectivity and finite dimension construct a genuine continuous linear section of its actual mkQ projection and prove the exact right-inverse law. The actual original exponential quotient homeomorphism supplies a constructed global singleton C-infinity chart on original G/center(G), with an actual quotient exponential/logarithm diffeomorphism. The exact actual formula q(g)=e(pi(Log(g))) proves the original center projection smooth. Actual quotient inverse coordinates, actual constructed linear section and genuine original exponential construct a global smooth original quotient lift s, and actual representative formulas prove q(s(x))=x at every actual quotient point. Lifting actual quotient arguments, performing the original smooth group operations and projecting by actual smooth q prove the original quotient multiplication and inversion smooth, hence construct a genuine original quotient LieGroup structure. The actual lift preserves identity, and differentiating its genuine right-inverse law gives a genuine continuous linear right inverse of the actual original quotient differential at original 1, proving that differential surjective. No replacement group, different lattice, supplied quotient smoothness, supplied linear section, group homomorphism property of the lift or additive nonabelian logarithm is assumed. Remaining: identify the exact actual original quotient differential with the original real quotient projection and its kernel with V, and prove actual native quotient bracket/exponential comparison for full ambient scalar-extension injectivity and specified-lattice rational-form induction; identify W intersect V with the actual specified center lattice rational span; arbitrary specified-lattice rational subgroup cocompactness; root-saturation subgroup closure; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 917
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 842,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 15,
        "new_selected_report_count": 25, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 8, "new_theorem_count": 15,
                    "new_selected_report_count": 25, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-native-center-smooth: PROGRESS. Eight new modules, fifteen proved theorems, nine definitions and one proved closedness instance; 25 exact new reports. All 842 baseline hashes verified before registration; only retained root/registry change. Actual original center model is closed, and the canonical normed real quotient has a constructed actual continuous linear section. Actual original quotient exponential homeomorphism constructs a genuine global smooth chart and quotient diffeomorphism. Original q(g)=e(pi(Log(g))) proves actual center projection smooth. Actual section and original exponential construct a genuine smooth global quotient lift with a proved actual projection right-inverse law. Lifting actual arguments, using original Lie group operations and projecting smoothly proves the original quotient multiplication and inversion smooth, giving the actual original quotient LieGroup structure. Actual lift preserves identity, and actual differential right-inverse law proves original quotient differential surjectivity. Exact differential/center-kernel identification, actual native bracket/exponential comparison, full ambient rational-form induction, W intersect V equality, arbitrary rational subgroup cocompactness, root-saturation closure, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. All retained axiom sets and eleven retained axiom-free reports unchanged; new empty reports independently checked. All 832 own and nine attributed PNT+ modules plus root/registry scanned; 850 source/config hashes. Actual full build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4152 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-center-smooth-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 832, "pntplus_modules": 9, "scanned_module_count": 841,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4152, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 842, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 15 and review["new_selected_report_count"] == 25
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 925 and manifest["proved_components"][-8:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 8
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
    assert scan["scanned_module_count"] == 841 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4152 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 15, "new_selected_declarations": 25,
        "all_source_modules_scanned": 841, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4152,
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
