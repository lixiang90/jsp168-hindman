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
PREFIX = "round-adjoint-generator"
OLD = "round-native-adjoint"
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
    assert len(baseline["files"]) == 724 and len(new_modules) == 3
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 709 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 26
    assert sum(c["theorems"] for c in module_counts.values()) == 25
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
    assert len(registered) == len(set(registered)) == len(actual) == 3635
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3609 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 727
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
    "All 724 baseline source/configuration hashes were revalidated before registration, with the preceding authoritative round independently rechecked before proof edits. Only root imports and the exact-name axiom registry change among retained files. All retained proof sources, StrongConjecture, dependency pins and attribution are byte-identical. This round and the preceding goal turn constitute PROGRESS; no unavoidable blocker is established. The fixed local paper is compared with the retained Git objects without any remote or official-update check.",
    "NativeLieAdjointExponential proves actual global uniqueness for the unital real Banach-algebra equation f-prime=f-times-b with f(0)=1. Differentiating f(t)*exp(-t*b) gives zero without assuming commutativity, and the true exponential inverse product gives f(t)=exp(t*b). This theorem is instantiated with the retained actual native adjoint curve and its proved actual differential equation. Thus Ad(gamma-v(t)) equals the actual operator exponential of t times the actual derivative-defined generator. The native exponential's adjoint, commuting generator law and left-multiplication form of its actual derivative follow. No generator is supplied in place of proof; the local rational normed-algebra instance is the genuine scalar restriction from the original real normed algebra.",
    "NativeLieAdjointGenerator applies the original manifold chain rule to original smooth adjoint and the actual native curve's zero-time tangent derivative. Explicit normed operator targets reconcile actual tangent aliases; there is no transparency or linter override. The actual derivative-defined generator equals the actual native identity derivative of adjoint applied to its tangent parameter. Consequently it is linear and continuous in that parameter. Differentiating the true fact that each ray's adjoint fixes its ray tangent gives B-v(v)=0; linearity gives alternating action. Original conjugation of original curves and the genuine adjoint representation prove actual generator conjugation and equivariance, and the action is jointly continuous.",
    "Differentiating genuine generator equivariance along the actual native one-parameter curve proves B-u(B-v(w))=B-(B-u(v))(w)+B-v(B-u(w)). Operator extensionality gives the true operator commutator B-u*B-v-B-v*B-u=B-(B-u(v)). These conclusions concern the actual original generators. They do not identify B-v(w) with the original native vector-field Lie bracket or supply a Lie-nilpotency hypothesis.",
    "NativeLieRightTranslation derives the true two-sided inverse of every original right-translation derivative from the actual inverse translations and native chain rules. The original group identity R-g composed with L-x composed with conjugation-g equals L-(x*g); genuine native derivatives then prove the actual invariant-field transport formula. Applying the true inverse right derivative proves mpullback(R-g,V-v)=V-(Ad-g(v)). This is the original field on the original manifold, with no substitute matrix group, flow assumption, derivative inverse, bracket compatibility or metric supplied.",
    "All 3 new modules and 26 exact new declarations are in the actual root build and kernel registry. Complete build and kernel processes terminate with exit code zero, and original byte logs are retained. All new modules are warning-free and their oleans current. The exact old axiom sets and six axiom-free declarations are unchanged. New and old selected reports use only propext, Classical.choice and Quot.sound. All project and attributed PNT+ Lean sources, root and registry are scanned for executable trust bypasses. No dependency edits, new options, unlimited heartbeats, disabled linters or native_decide are introduced.",
    "Next compare the actual right-translation pullback with the original chart vector-field bracket by genuine mixed second derivatives, thereby proving B-v(w) equals the original native bracket. That equality, native nilpotent finite adjoint/dexp formulas, global exponential inverse/BCH for arbitrary connected simply connected nilpotent groups, arbitrary specified-lattice rational subgroup cocompactness, full calibration/Alignment and ordered arithmetic witness extraction remain unproved. Lattice logarithms are not assumed additive, and native group/Lie lower-central equality is not supplied. StrongConjecture remains unproved; the repository, award PR and prize application await complete formalization and audit.",
]

COMPONENTS = [
    "actual original native adjoint curve and exponential equal genuine Banach operator exponentials of their true derivative-defined generators, with left and right linear differential equations",
    "actual native adjoint generator equals actual identity manifold derivative of original adjoint, proving its parameter linearity and continuity",
    "actual derivative-defined generator action annihilates its own parameter, is alternating and jointly continuous, and is equivariant under original native adjoint",
    "actual native adjoint generators satisfy Leibniz action and operator commutator identities from differentiation of genuine original conjugation equivariance",
    "true original right-translation derivative inverse, genuine invariant-field transport and exact native pullback by the actual adjoint action",
]

OLD_REMAINING_SENTENCE = "Identifying this actual generator with the original native bracket operator, deriving its nilpotent finite exponential formula and the general native exponential differential formula remain unproved; no supplied generator or native finite adjoint formula is asserted."
NEW_PROGRESS = "The actual global linear equation now proves that the original adjoint curve and the adjoint of the original exponential equal genuine Banach-algebra operator exponentials of the derivative-defined generator; no generator is supplied. The actual manifold chain rule identifies this generator with the true native identity derivative of original adjoint applied to its tangent parameter, proving genuine parameter linearity and continuity. Its action annihilates its own parameter, is alternating and jointly continuous, and satisfies actual conjugation equivariance. Differentiating that genuine equivariance along the original native curve proves its Leibniz action and operator commutator identities. Original right translations have proved true inverse native derivatives and genuine invariant-field transport, giving the exact original pullback formula by the actual adjoint action. Identifying this actual generator action with the original native vector-field Lie bracket still requires genuine mixed-second-derivative comparison for the original chart flow and remains unproved. Native nilpotent finite adjoint/dexp formulas also remain unproved; generator nilpotency or original bracket compatibility is not supplied."


def record():
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and not manifest["full_target_proved"]
    assert len(manifest["proved_components"]) == 797
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(OLD_REMAINING_SENTENCE) == 1
    remaining = remaining.replace(OLD_REMAINING_SENTENCE, NEW_PROGRESS)
    review = {
        "date": "2026-10-09", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 724,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 25,
        "new_selected_report_count": 26, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-09", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 3, "new_theorem_count": 25,
                    "new_selected_report_count": 26, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ("\n2026-10-09 round-adjoint-generator: PROGRESS. 3 new modules, 25 proved theorems and 1 audited definition (26 exact new reports). All 724 baseline hashes verified before registration; previous current state independently rechecked before proof edits. Retained proof sources, pins and attribution unchanged; only root and registry changed. Actual global adjoint curve and original exponential adjoint equal genuine Banach operator exponentials of actual derivative-defined generators. Actual native chain rule identifies that generator with actual identity derivative of original adjoint, proving linearity, continuous alternating action and original conjugation equivariance. Differentiating real equivariance yields genuine Leibniz action and operator commutator formulas. Original right translations have true inverse native derivatives, original invariant-field transport and exact native pullback. Complete build terminal exit 0: " + str(verified["build_jobs"]) + " jobs. Kernel terminal exit 0: 3635 exact unique reports, standard axioms only; original axiom sets and six axiom-free reports unchanged. Scanned 709 own and 9 attributed PNT+ modules, root and registry. 727 current source/configuration hashes. New modules warning-free, oleans current. Fixed local paper objects match; no remote updates checked. Actual generator identification with original native vector-field bracket remains unproved; no native bracket compatibility or generator nilpotency is supplied. Native nilpotent finite adjoint/dexp, general nilpotent global inverse/BCH and specified-lattice transfer, calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-adjoint-generator-review.json.\n\n")
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 709, "pntplus_modules": 9, "scanned_module_count": 718,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3635, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 724, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 25 and review["new_selected_report_count"] == 26
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 802 and manifest["proved_components"][-5:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 718 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3635 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 25, "new_selected_declarations": 26,
        "all_source_modules_scanned": 718, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3635,
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
