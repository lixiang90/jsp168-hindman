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
PREFIX = "round-native-dexp"
OLD = "round-group-lie-nilpotency"
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
    assert len(baseline["files"]) == 738 and len(new_modules) == 9
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 729 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 45
    assert sum(c["theorems"] for c in module_counts.values()) == 40
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
    assert len(registered) == len(set(registered)) == len(actual) == 3732
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3687 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 747
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


APPLICATION = ['PROGRESS: the preceding authoritative round was independently rechecked before edits. All 738 baseline source/configuration hashes are revalidated before registration. Retained proofs, StrongConjecture, pins and attribution remain unchanged; only the root imports and exact-name kernel registry change among retained sources. No unavoidable blocker is established. The fixed local paper is compared with pinned Git objects, without remote or official updates.', 'NativeLieRelativeCurve defines exactly r-v(t,w)=gamma-v(-t)*gamma-(v+w)(t), from the original chosen native integral curves. Actual one-parameter identities prove its zero-time and zero-state values and genuine group-valued cocycle r(t+s,w)=gamma(-t)*r(s,w)*gamma(t)*r(t,w). Original joint smoothness proves actual C-infinity regularity. Actual identity multiplication derivatives prove its zero-time velocity is exactly w. No relative curve, variation equation or logarithmic derivative is supplied.', 'NativeLieCurveParameterJacobian defines K-v(t) as the actual original manifold parameter derivative of r-v(t,w) at w=0. The true identity chart and genuine manifold chain rule identify it with the actual coordinate Jacobian applied to the state inclusion. Actual coordinate regularity proves the operator-valued map K-v is C-infinity; its original zero-time value is zero. Canonical original model operators and explicit native tangent identifications reconcile Lean aliases without new options or transparency overrides.', "NativeLieParameterJacobianInitial derives the genuine coordinate time velocity w at time zero. Original joint C2 regularity and the proved actual time-velocity identity near zero instantiate the actual second-derivative symmetry lemma, proving the true time derivative of K-v(t) applied to every w is w at zero. Differentiating the actual operator action and derivative uniqueness then prove K-v'(0)=id. The mixed derivative is applied to the actual original relative curve, not a supplied flow.", "NativeLieParameterJacobianCocycle differentiates the genuine group cocycle at zero parameter. Both original product factors equal identity, so the actual identity multiplication derivative and actual original conjugation derivative give K-v(t+s)=Ad-gamma-v(-t)*K-v(s)+K-v(t). Actual time translation and the proved K-v'(0)=id then give the original global equation K-v'(t)=Ad-gamma-v(-t). Products remain in their actual order; no commutativity or variation equation is assumed.", 'AdjointPrimitivePolynomial constructs P-B,k(t)=sum(j<k) ((-1)^j/(j+1)!)*t^(j+1) times B^j. Its actual scalar coefficients and finite sum are differentiated directly, yielding exactly the retained finite adjoint series at negative time. The genuine zero-derivative theorem and actual zero initial values show every actual K with that proved derivative equals this polynomial. This abstract primitive is actually instantiated with the original derivative-defined native bracket generator and original group nilpotencyClass.', 'NativeLieExponentialDifferential defines nativeLieDexp by the actual original exponential manifold derivative followed by the actual inverse left-translation derivative. Genuine native chain rules for the actual parameter shift and the original exponential identify it with K-v(1). Actual inverse translation identities prove that the full original exponential derivative is genuine left translation composed with this nativeLieDexp; the action formula is the original native invariant field. No exponential differential formula or invertible derivative is an input.', 'NativeLieNilpotentDexp applies original Group.IsNilpotent and the previously proved original group-class adjoint cutoff to the actual global K equation. It proves K-v(t)=P-B-v,c(t), hence nativeLieDexp-v=sum(j<c) (-1)^j/(j+1)! times B-v^j, with c the original Group.nilpotencyClass and B-v the actual generator already proved to act as the original native Lie bracket. It does not require separately supplied native Lie-algebra nilpotency or replace the original group by a matrix model.', 'NilpotentPolynomialUnit proves that a finite polynomial with constant coefficient one evaluated at a genuinely nilpotent element is a true unit. Its positive-degree terms are individually nilpotent and commute as powers of one element, so their finite sum is nilpotent. The zero-cutoff case is proved separately using B^0=0, hence 1=0; no nontriviality or positive group-class premise is silently imposed. NativeLieDexpInvertible actually instantiates this with the original group-class cutoff. It proves nativeLieDexp is a unit and bijective at every original vector. Both genuine inverse left-translation derivative identities prove the original translation derivative is a true two-sided unit, hence the full original exponential derivative is a unit and bijective at every vector. These are differential conclusions, not global exponential bijectivity.', 'All nine new modules, 40 proved theorems and five definitions are registered in the actual root and exact-name kernel audit, yielding 45 exact new reports. Full build and full kernel processes must terminate with exit zero before recording; raw byte evidence and hashes are retained. New modules are warning-free with current oleans. Retained exact axiom sets, including the six retained axiom-free declarations, remain unchanged, and all reports use only propext, Classical.choice and Quot.sound. All 729 own and nine attributed PNT+ modules plus root and registry are scanned for executable trust bypasses. Pins and attributed sources stay unchanged.', 'Remaining: actual group/Lie lower-central layer identification, global exponential inverse/BCH for arbitrary connected simply connected nilpotent Lie groups, faithful integration/Malcev comparison and arbitrary specified-lattice rational subgroup cocompactness. Pointwise invertible exponential differentials alone do not establish a global inverse. Nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witness extraction remain unproved. StrongConjecture and the prize target remain unproved; public repository, prize PR and application await full formalization and audit.']

COMPONENTS = ['actual original relative parameter curve has genuine zero values, C-infinity regularity, zero-time velocity and original group-valued time cocycle', 'actual original relative parameter derivative is the identity-chart state Jacobian and is C-infinity with original zero initial value', 'actual original relative Jacobian initial time derivative is identity by genuine mixed differentiation of the actual relative coordinate curve', 'actual original relative Jacobian cocycle and global time derivative equal negative-time original native adjoint, derived from actual group multiplication and conjugation', 'actual finite adjoint-series polynomial primitive is directly differentiated and identified by genuine zero-derivative uniqueness', 'original native exponential left-trivialized differential is the actual relative parameter Jacobian at time one and reconstructs the complete original manifold derivative', 'actual original native exponential differential has the finite bracket-generator formula at original group nilpotencyClass without supplied native Lie nilpotency', 'actual finite polynomial with constant coefficient one evaluated at a nilpotent element is a unit, including the zero-cutoff trivial-ring case', 'actual original native dexp and complete original exponential differential are two-sided units and bijective at every original model vector under original group nilpotency']

NEW_PROGRESS = "The actual original native adjoint generators act as the original native Lie bracket. Original group lower-central termination forces every same-length ordered generator product to vanish and hence native Lie lower-central termination at the same cutoff. Thus original Group.IsNilpotent proves native LieModule.IsNilpotent, and genuine original adjoints have finite formulas at original Group.nilpotencyClass. The actual relative curve r-v(t,w)=gamma-v(-t)*gamma-(v+w)(t) now has proved original group cocycle, actual C-infinity regularity and zero-time velocity w. Its genuine original manifold state derivative K-v(t) is identified with its actual identity-chart Jacobian, is C-infinity and has actual initial value zero. Genuine mixed second-derivative symmetry applied to this original relative curve proves K-v'(0)=id. Differentiating the actual group cocycle proves K-v(t+s)=Ad-gamma-v(-t)*K-v(s)+K-v(t), and real time translation gives the actual global derivative K-v'(t)=Ad-gamma-v(-t). A directly differentiated finite polynomial primitive and actual zero-derivative uniqueness prove K-v(t)=sum(j<c) ((-1)^j/(j+1)!)*t^(j+1) times B-v^j, where c is the original group nilpotencyClass and B-v is the actual native bracket generator. Original manifold chain rules identify K-v(1) with the actual original exponential differential followed by actual inverse left translation. Thus the original native dexp now has its genuine finite formula sum(j<c) (-1)^j/(j+1)! times B-v^j, and the full original exponential derivative is actual left translation composed with that operator. Nilpotency and the actual constant-one finite polynomial prove native dexp is a genuine two-sided unit and bijective at every original model vector; actual inverse translation derivatives prove the complete original exponential derivative is likewise a two-sided unit and bijective. The zero group-class case is covered through the proved identity 1=0 for the resulting operator ring, without a nontriviality premise. No dexp formula, variation equation, derivative invertibility, native Lie nilpotency or matrix replacement is supplied. Individual group/Lie lower-central layer identification and global exponential invertibility/BCH still remain unproved; pointwise invertible derivatives alone do not give a global inverse."


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 813
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 738,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 40,
        "new_selected_report_count": 45, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 9, "new_theorem_count": 40,
                    "new_selected_report_count": 45, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ("\n2026-10-10 round-native-dexp: PROGRESS. Nine new modules, 40 proved theorems and five definitions; 45 exact new reports. All 738 baseline source/config hashes revalidated before registration; only root and registry change among retained sources. The original relative curve has a genuine group cocycle and actual zero-time velocity. Its actual manifold parameter Jacobian is C-infinity with K(0)=0. Genuine mixed derivatives prove K'(0)=id; actual cocycle differentiation and time translation prove K'(t)=Ad-gamma(-t). A directly differentiated finite primitive gives the actual original group-class polynomial for K. Actual original native chain rules identify K(1) with native dexp, the actual inverse-left-trivialized original exponential differential, and reconstruct the full derivative by actual left translation. Original group nilpotency gives the exact finite native bracket-generator formula. Nilpotent constant-one polynomials and genuine inverse translation derivatives prove native dexp and the complete original exponential differential are two-sided units and bijective at every original vector, including the zero-cutoff case. No global inverse or BCH is supplied. Complete build terminal exit 0: " + str(verified["build_jobs"]) + ' jobs. Kernel terminal exit 0: 3732 exact unique standard-axiom reports; all retained axiom sets and six retained axiom-free reports unchanged. Scanned 729 own and nine attributed PNT+ modules plus root/registry; 747 current source/config hashes. New modules warning-free and oleans current; fixed local paper objects match, no remote updates checked. Group/Lie layer comparison, global inverse/BCH, arbitrary specified-lattice transfer, full calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-native-dexp-review.json.\n\n')
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 729, "pntplus_modules": 9, "scanned_module_count": 738,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3732, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 738, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 40 and review["new_selected_report_count"] == 45
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 822 and manifest["proved_components"][-9:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 738 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3732 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 40, "new_selected_declarations": 45,
        "all_source_modules_scanned": 738, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3732,
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
