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
PREFIX = "round-native-adjoint"
OLD = "round-curve-regularity"
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
    assert len(baseline["files"]) == 719 and len(new_modules) == 5
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 706 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 36
    assert sum(c["theorems"] for c in module_counts.values()) == 31
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
    assert len(registered) == len(set(registered)) == len(actual) == 3609
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3573 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 724
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
    "All 719 retained source/configuration hashes were verified before proof edits and again before registration. Only root imports and the exact-name axiom registry changed among retained files. All retained proof sources, StrongConjecture, dependency pins and attribution remain byte-identical. Fixed local paper objects are checked without checking remote or official updates. The preceding goal turn and this round make concrete proof progress; no unavoidable blocker is established.",
    "NativeLieAdjointDerivative defines the actual adjoint as the genuine native derivative at identity of original conjugation g*x*g-inverse. True smooth multiplication proves fixed and joint conjugation smooth. Original conjugation composition and the actual native chain rule prove the adjoint representation law, identity law, explicit inverse compositions, injectivity and surjectivity. No derivative inverse, representation law, Lie embedding or exponential compatibility is supplied.",
    "NativeLieAdjointEquiv constructs the actual continuous linear equivalence with inverse given by the proved adjoint of g-inverse. Native derivatives of both original inverse conjugations and their actual inverse identities prove the true inverse of conjugation's derivative at every group point. The retained actual homomorphism/invariant-field/ODE comparison proves the original native one-parameter and exponential conjugation formulas. The genuine one-parameter group law gives commuting values on a single ray; derivative uniqueness at zero proves the adjoint of each original ray element fixes that ray's tangent vector. No commutativity between different vectors or group elements is asserted.",
    "NativeLieAdjointBracket proves the true pullback of the original invariant field under original conjugation, using the actual derivative inverse and the retained homomorphism derivative law. Natural pullback of the actual manifold vector-field Lie bracket then proves preservation of the original native GroupLieAlgebra bracket. The genuine continuous linear adjoint equivalence is promoted to an actual native Lie equivalence, and the actual Lie lower-central series is preserved by its LieIdeal image. Completeness is used where the original native Lie algebra requires it. No equality with the group lower-central series or lattice-logarithm closure is assumed.",
    "NativeLieAdjointSmooth applies actual parameterized manifold derivative regularity to genuine joint conjugation. Both derivative base points equal the actual original group identity. Original tangent coordinate self-changes, verified pointwise, identify the coordinate derivative map with the original adjoint. The adjoint is thus genuinely C-infinity as a map into the original continuous-linear-map normed space, and its action is jointly C-infinity in group element and tangent vector. Boundarylessness, completeness, Hausdorffness and nilpotency are not required for this operator regularity.",
    "NativeLieAdjointCurve defines the actual operator-valued curve along the retained native one-parameter curve. Its zero value and noncommutative multiplicative time law are proved from the genuine original adjoint representation. Actual global curve and adjoint smoothness prove normed C-infinity regularity. Its infinitesimal generator is defined as its actual derivative at zero, and that derivative is proved to exist. Genuine time translation, the vector-valued chain rule and actual operator multiplication derive A'(t)=A(t)*B at every real time. This supplies no arbitrary generator and does not identify B with the native bracket operator; that identification and the resulting nilpotent finite exponential formula remain unproved.",
    "All general native statements retain the original arbitrary real normed model, smooth Lie group, native operations, topology and manifold charts. Complete, boundaryless and Hausdorff premises are used only where the retained native exponential requires them; unused LieGroup regularity is explicitly omitted for the raw evaluation and identity lemmas. Typed functions, local convert! and the original group inverse laws reconcile definitional tangent aliases only. All five new proof modules are warning-free. There are no new option, heartbeat, transparency or linter overrides. The actual full build contains every exact root import, and the kernel audit contains all 36 new exact declarations with unchanged retained axiom sets.",
    "Next identify the actual adjoint generator with the original Lie bracket, derive genuine native finite adjoint/exponential differential formulas in the nilpotent case, and continue general exponential/BCH and global inverse comparison. Original section 07 still concerns arbitrary connected simply connected rational nilpotent groups with arbitrary specified lattices. General global exponential invertibility, faithful integration/Malcev comparison, specified-lattice rational subgroup cocompactness, complete calibration/Alignment and ordered arithmetic witness extraction remain unproved. StrongConjecture and the full prize target remain unproved, so repository creation, award PR and application continue to await completion and audit.",
]

COMPONENTS = [
    "constructed actual native adjoint from original conjugation derivative, with genuine representation, inverse, injectivity and surjectivity laws",
    "constructed actual continuous linear adjoint equivalence and proved genuine inverse conjugation derivative at every original group point",
    "original native curve and exponential conjugation formulas, with actual adjoint fixing its own one-parameter tangent direction",
    "actual invariant-field pullback and native Lie bracket preservation, constructed native adjoint Lie equivalence and original Lie lower-central layer image invariance",
    "actual native adjoint C-infinity as an operator-valued map and its action jointly C-infinity in original group element and tangent vector",
    "actual native adjoint curve smooth with genuine multiplicative time law and derivative-defined generator satisfying the true global linear ODE A-prime=A-times-B",
]


def record():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    remaining = manifest["last_round"]["remaining"]
    marker_sentence = "These regularity results supply no global inverse."
    assert remaining.count(marker_sentence) == 1
    new_progress = "The native adjoint is now the constructed actual derivative at identity of original group conjugation, with proved multiplicative representation and explicit inverse laws. Its genuine continuous linear equivalence and the actual inverse conjugation derivative at every group point are proved. Actual homomorphism/ODE uniqueness proves original native one-parameter and exponential conjugation, and each original ray element's adjoint fixes that ray tangent. Genuine invariant-field pullback and vector-field bracket naturality now prove preservation of the original native Lie bracket, constructing an actual native adjoint Lie equivalence and proving its image preserves every original Lie lower-central layer. Actual parameterized derivative regularity and identity tangent coordinate changes prove operator-valued adjoint smoothness and joint action smoothness. The actual adjoint curve along each original one-parameter curve is C-infinity and has its genuine multiplicative time law. Its infinitesimal generator is its true zero-time derivative, and actual time translation proves the global linear ODE A'(t)=A(t)*B. Identifying this actual generator with the original native bracket operator, deriving its nilpotent finite exponential formula and the general native exponential differential formula remain unproved; no supplied generator or native finite adjoint formula is asserted. "
    remaining = remaining.replace(marker_sentence, marker_sentence + " " + new_progress)
    review = {
        "date": "2026-10-09", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 719,
        "retained_changed": ["Hindman168.lean", "Verification.lean"], "new_modules": registration["new_modules"],
        "new_theorem_count": 31, "new_selected_report_count": 36,
        "module_report_counts": registration["module_report_counts"], "application_review": APPLICATION,
        "verification": verified, "remaining": remaining,
    }
    assert len(manifest["proved_components"]) == 791 and not set(COMPONENTS) & set(manifest["proved_components"])
    manifest.update(
        date="2026-10-09", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 5, "new_theorem_count": 31,
                    "new_selected_report_count": 36, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ("\n2026-10-09 round-native-adjoint: PROGRESS. 5 new modules, 31 proved theorems and 5 audited definitions (36 new exact reports). All 719 baseline hashes verified before proof edits and before registration; retained proof sources, pins and attribution unchanged, only root imports and registry changed. Actual adjoint from original conjugation derivative has proved representation and explicit inverse laws. Actual conjugation derivative inverse and native exponential conjugation are proved. Genuine invariant-field pullback and native vector-field bracket naturality prove a native adjoint Lie equivalence preserving every original Lie lower-central layer. Operator-valued adjoint and joint action are C-infinity. The actual adjoint curve has its true derivative-defined generator and global linear ODE A-prime=A-times-B; generator identification with native bracket remains unproved. Complete build terminal exit 0: " + str(verified["build_jobs"]) + " jobs. Kernel terminal exit 0: 3609 exact unique reports, standard axioms only; retained axiom sets and six axiom-free reports unchanged. Scanned 706 own and 9 attributed PNT+ modules, plus root and registry. 724 current source/configuration hashes. Fixed local paper objects match; no remote update check. Native finite adjoint/dexp formulas, general nilpotent global inverse/BCH, specified-lattice transfer, calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-native-adjoint-review.json.\n\n")
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 706, "pntplus_modules": 9, "scanned_module_count": 715,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3609, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_edits": 719, "retained_changed": review["retained_changed"],
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
    assert len(manifest["proved_components"]) == 797 and manifest["proved_components"][-6:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 715 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3609 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 31, "new_selected_declarations": 36,
        "all_source_modules_scanned": 715, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3609,
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

