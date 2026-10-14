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
PREFIX = "round-curve-regularity"
OLD = "round-native-exp-derivative"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_FREE = {
    "Hindman168.MatrixDepth.smul",
    "Hindman168.maskDescendant_encoding_injective",
    "Hindman168.maskDescendant_none_iff",
    "Hindman168.maskDescendant_some_of_noninvariant",
    "Hindman168.matrixDepth_zero",
    "Hindman168.matrixDepth_zero_iff_upper",
}


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
    assert len(baseline["files"]) == 711 and len(new_modules) == 8
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 701 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 32
    assert sum(c["theorems"] for c in module_counts.values()) == 30
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
    assert len(jobs) == 1 and int(jobs[0]) == 4649
    assert not re.search(rb"(?:error:|warning:)", blog), "build diagnostics"
    previous = reports(OLD + "-axioms.txt")
    old_result = obj(OLD + "-kernel-result.json")
    assert old_result["exit_code"] == 0 and old_result["terminal"] is True
    assert digest(OLD + "-axioms.txt") == old_result["log_sha256"]
    actual = reports(PREFIX + "-axioms.txt")
    registered = re.findall(r"^#print axioms (\S+)", lean_code(read("Verification.lean")), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 3573
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3541 and all(actual[n] == a for n, a in previous.items())
    assert all(a <= ALLOWED for a in actual.values())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 719
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


APPLICATION = [
    "All 711 baseline source/configuration hashes were verified before proof edits and again before registration. Only root imports and the exact-name axiom registry changed among retained files. All retained proofs, StrongConjecture, dependencies and attribution remain byte-identical. Fixed local paper objects are rechecked without checking remote or official updates. The previous formalization goal turn and this round make concrete proof progress; no unavoidable blocker is established.",
    "CurvePointwiseOperator constructs the actual bounded linear pointwise operator and its outer continuous linear map in the original supremum norms. QuadraticDerivativeRemainder derives the genuine quadratic remainder on a convex domain from a true Lipschitz derivative by the mean value theorem on the original segment. No supplied curve-space derivative or altered norm is used.",
    "CurveSuperpositionRemainder proves the uniform curve remainder and the actual derivative at every nonconstant curve in a smaller original ball. Continuity of each actual composition is proved, excluding the total-definition fallback. CurveSuperpositionSmooth derives the required derivative Lipschitz control from true C2 regularity and proves finite-order lifting by induction, generalizing the codomain to the continuous-linear-map space. Its one-order slack disappears for the C-infinity conclusion. The common universe of domain and codomain preserves the original E-times-E invariant-field application and imposes no finite-dimensional restriction.",
    "CurvePicardSmooth applies the proved smooth superposition and the original bounded Volterra integral operator to the retained Picard residual. The actual implicit function theorem proves smoothness of the retained chosen curvePicardImplicit and its genuine endpoints, with the square-zero state inverse already proved. No different flow, implicit inverse or smoothness premise is supplied in the Lie-group application.",
    "LieInvariantFieldSmooth derives genuine joint C-infinity regularity of the native invariant field from the tangent map of actual smooth multiplication. Original identity charts give true smooth coordinate and frozen-coordinate fields. The actual infinity LieGroup implies the retained minSmoothness(Real,3) LieGroup; this proved implication is only a local instance. No group operation, topology, norm, tangent space or manifold model is replaced.",
    "NativeLieExponentialSmoothAtZero transfers the real implicit-flow smoothness through the retained native uniqueness identification to the original time-one exponential in its identity chart. This proves original native exponential smoothness at zero. The genuine inverse-function regularity theorem also proves the retained coordinate inverse smooth at the identity coordinate and the retained native local logarithm smooth at the original group identity. These inverse conclusions remain local.",
    "NativeLieExponentialSmooth proves actual finite group powers smooth by induction using original multiplication in a possibly noncommutative group. For each finite order the proved exponential regularity at zero gives a genuine neighbourhood of that order. A sufficiently small positive reciprocal integer scales any chosen vector into it. The retained genuine one-parameter power law recovers the original exponential at every vector. Every finite order is proved and hence the original native exponential is globally C-infinity. Neither a false additive exponential law nor a commutative-group restriction is introduced. The original native curve is jointly smooth in tangent parameter and time, and its left-translated flow is jointly smooth in initial group point, parameter and time.",
    "All new general results retain arbitrary original real complete normed models, smooth native Lie groups, boundarylessness and Hausdorff structures where used. The finite-power lemma explicitly omits unused completeness, boundarylessness and Hausdorff assumptions. Typed maps and local convert! reconcile only definitional aliases. All new proof modules are warning-free, with no runtime, heartbeat, transparency or linter overrides. The full build includes every exact root import and the kernel audit includes all 32 new declarations, with retained axiom sets unchanged.",
    "Global exponential smoothness alone does not prove global injectivity or surjectivity for arbitrary connected simply connected nilpotent groups. Genuine nilpotent global invertibility, native BCH comparison or faithful integration/Malcev coordinates, original specified-lattice rational subgroup cocompactness, complete calibration/Alignment and ordered arithmetic witness extraction remain unproved. Arbitrary nonabelian lattice logarithms are not assumed additive and group/Lie lower-central equality is not assumed. StrongConjecture and the full prize target remain unproved.",
]

COMPONENTS = [
    "constructed actual continuous-curve pointwise linear operator and outer bounded linear map with original supremum norm bounds",
    "genuine convex-domain quadratic derivative remainder and uniform nonconstant-curve superposition remainder",
    "actual pointwise superposition derivative on a neighbourhood of the constant curve, derived from true C2 field regularity",
    "proved finite-order continuous-curve superposition lifting with one order of slack, hence genuine C-infinity lifting",
    "retained actual Picard residual, implicit curve and fixed-time endpoints proved C-infinity from the actual smooth field",
    "actual native invariant, identity-coordinate and frozen-coordinate fields proved jointly C-infinity from original smooth multiplication",
    "original native exponential C-infinity at zero and retained local coordinate inverse and native logarithm C-infinity at identity",
    "actual noncommutative finite powers smooth and original native exponential globally C-infinity by reciprocal-integer scaling and proved one-parameter power law",
    "original native one-parameter curve jointly C-infinity in parameter and time, and actual left-translated flow jointly C-infinity in initial group point, parameter and time",
]


def record():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    remaining = manifest["last_round"]["remaining"]
    old_sentence = "Full parameter differentiability away from zero and higher smoothness, global exponential invertibility for arbitrary connected simply connected nilpotent Lie groups, full faithful matrix integration or Malcev comparison, BCH comparison outside the concrete strict-matrix realization, and transfer to arbitrary original paper groups with their specified lattices remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted."
    assert remaining.count(old_sentence) == 1
    replacement = "The actual pointwise bounded operator on continuous-curve spaces, the genuine uniform quadratic remainder and derivative at every nearby nonconstant curve are now proved. Finite-order superposition lifting with one order of slack gives actual smooth superposition for smooth fields. The retained actual Picard implicit curve and endpoints are proved C-infinity. Actual native multiplication gives C-infinity invariant, identity-coordinate and frozen-coordinate fields. The retained native-flow uniqueness identification now proves the original exponential C-infinity at zero, and the original coordinate inverse and native local logarithm C-infinity at identity. Every actual finite group power is proved smooth without a commutativity assumption. For each finite order reciprocal-integer scaling into the genuine zero neighbourhood and the proved single-parameter power law extend exponential regularity to every original model vector. Thus the original native exponential is now globally C-infinity, its chosen native one-parameter curves are jointly C-infinity in parameter and time, and their actual left-translated flow is jointly C-infinity in group initial point, parameter and time. These regularity results supply no global inverse. Global exponential invertibility for arbitrary connected simply connected nilpotent Lie groups, full faithful matrix integration or Malcev comparison, BCH comparison outside the concrete strict-matrix realization, and transfer to arbitrary original paper groups with their specified lattices remain unproved; no universal group embedding or arbitrary rational subgroup theorem is asserted."
    remaining = remaining.replace(old_sentence, replacement)
    review = {
        "date": "2026-10-09", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": len(baseline["files"]),
        "retained_changed": ["Hindman168.lean", "Verification.lean"], "new_modules": registration["new_modules"],
        "new_theorem_count": 30, "new_selected_report_count": 32,
        "module_report_counts": registration["module_report_counts"], "application_review": APPLICATION,
        "verification": verified, "remaining": remaining,
    }
    assert len(manifest["proved_components"]) == 782 and not set(COMPONENTS) & set(manifest["proved_components"])
    manifest.update(
        date="2026-10-09", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 8, "new_theorem_count": 30,
                    "new_selected_report_count": 32, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = "\n2026-10-09 round-curve-regularity: PROGRESS. 8 new modules, 30 proved theorems and 2 audited bounded-operator definitions (32 new exact reports). All 711 baseline hashes verified before proof edits and before registration; retained proofs and pins unchanged, only root imports and registry changed. Actual nonconstant-curve derivatives and smooth superposition prove retained Picard implicit-flow smoothness. Actual native invariant-field smoothness and retained uniqueness identify the original exponential as C-infinity at zero. Reciprocal-integer scaling and the proved one-parameter power law extend it globally in the original possibly noncommutative group. Native curve and left-translated flow are jointly smooth. Native local logarithm remains local. Complete build terminal exit 0: 4649 jobs. Kernel terminal exit 0: 3573 exact unique reports, standard axioms only; all retained axiom sets and six axiom-free reports unchanged. Scanned all 701 own and 9 attributed PNT+ modules, plus root and registry. 719 current source/configuration hashes. Fixed local paper objects match; no remote update check. General nilpotent global invertibility, native BCH/Malcev comparison, specified-lattice transfer, calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-curve-regularity-review.json.\n\n"
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 701, "pntplus_modules": 9, "scanned_module_count": 710,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3573, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_edits": 711, "retained_changed": review["retained_changed"],
        "retained_proof_sources_unchanged": True, "pins_and_attributed_sources_unchanged": True,
        "root_imports_exact": True, "registered_names_exact": True, "kernel_names_exact": True,
        "full_target_proved": False, "verified": verified,
    })
    print(json.dumps({"recorded": True, "verified": verified, "proved_components": len(manifest["proved_components"])}, ensure_ascii=False))


def recheck():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    review = obj(PREFIX + "-review.json")
    result = obj(PREFIX + "-checks.json")
    assert manifest["files"] == files and all(digest(f["path"]) == f["sha256"] for f in files)
    assert review["verification"] == result["verified"] == verified
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 791 and manifest["proved_components"][-9:] == COMPONENTS
    assert manifest["full_target_proved"] is False and manifest["build_succeeded"] and manifest["axiom_check_succeeded"]
    assert obj(PREFIX + "-preprint-local-check.json") == fixed
    assert manifest["build_log"] == PREFIX + "-build.txt" and manifest["axiom_log"] == PREFIX + "-axioms.txt"
    assert manifest["build_job_count"] == verified["build_jobs"]
    assert manifest["hindman_module_count"] == verified["project_modules"]
    assert manifest["pntplus_module_count"] == verified["pntplus_modules"]
    assert manifest["selected_axiom_report_count"] == verified["axiom_reports"]
    assert manifest["source_scan_module_count"] == verified["source_scan_modules"]
    assert Path("BUILD-EVIDENCE.txt").read_bytes() == b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n"
    scan = obj(PREFIX + "-source-scan.json")
    assert scan["scanned_module_count"] == 710 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3573 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 30, "new_selected_declarations": 32,
        "all_source_modules_scanned": 710, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3573,
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
