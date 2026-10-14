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
PREFIX = "round-group-lie-nilpotency"
OLD = "round-native-bracket"
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
    assert len(baseline["files"]) == 733 and len(new_modules) == 5
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 720 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 23
    assert sum(c["theorems"] for c in module_counts.values()) == 21
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
    assert len(registered) == len(set(registered)) == len(actual) == 3687
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3664 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 738
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


APPLICATION = ['PROGRESS: the preceding authoritative round was independently rechecked before proof edits. All 733 baseline source/configuration hashes are revalidated before registration. Retained proofs, StrongConjecture, dependencies and attribution remain byte-identical; only the root imports and exact-name axiom registry change among retained source/configuration files. No unavoidable blocker is established. The fixed local paper is compared to pinned Git objects; no remote or official updates are checked.', "NativeLieCommutatorDerivative constructs exactly the original group map c-g(x)=g*x*g-inverse*x-inverse. Actual multiplication is differentiated at the identity with its genuine two partial derivatives equal to identity. Differentiating the genuine identity c-g(x)*x=g*x*g-inverse then proves the actual original manifold derivative D c-g(1)=Ad-g-id. The commutator map's C-infinity regularity comes from original conjugation, multiplication and inverse. Native tangent aliases are reconciled with explicitly typed original model operators; there are no new source options, transparency or linter overrides.", 'NativeLieCommutatorWords constructs actual right-nested words in the original group. Induction and the original subgroup commutator law prove each word of length k lies in the actual original group lower-central layer k. Original chart chain rules compute its derivative at the identity as the ordered product of actual adjoint differences. If that original layer is bottom, the genuine word is identically the original identity; its actual derivative is zero. This proves the product cutoff from original group nilpotency without assuming an adjoint-difference or bracket relation.', "NativeLieCommutatorProducts differentiates those genuinely vanishing products along the original native one-parameter curves, replacing one adjoint difference at a time by its actual derivative-defined generator. Constants stay in their original multiplication order, with no commutativity assumed. An induction over the number of replacements proves that every ordered product of k actual generators is zero under the original group lower-central cutoff k. Repeated equal parameters give the actual generator's kth power zero with the same cutoff.", 'LieLowerCentralProductCutoff proves an algebraic implication for actual Lie modules: if every length-k ordered product of original toEnd actions vanishes, the original Lie lower-central series at k is bottom. The proof inducts through its actual linear span of brackets and places each preceding layer in the genuine kernel of every complementary action product. This lemma is actually instantiated in NativeLieGroupNilpotency, with products transported through the genuine continuous-to-linear ring homomorphism and the previously proved original generator=original native bracket identity.', 'NativeLieGroupNilpotency proves original group lower-central termination at k implies original native Lie lower-central termination at the same k. In particular Group.IsNilpotent supplies native LieModule.IsNilpotent with cutoff at most the original group nilpotencyClass. No separately supplied native Lie-nilpotency premise remains in the public original-group finite adjoint formulas: both original adjoint curves and original exponential adjoints truncate at the original group nilpotencyClass, using the actual operator exponential and proved actual generator. The result applies to the arbitrary original Lie group, not a concrete matrix replacement. It does not identify individual group/Lie lower-central layers or construct a global exponential inverse.', "All five new modules, 21 proved theorems and two definitions are in the actual root and exact-name kernel registry, with 23 exact new selected declarations. Complete build and kernel processes terminate with zero exit codes; raw byte logs and hash records are retained. All new modules are warning-free and oleans current. All retained reports' exact axiom sets and six axiom-free declarations remain unchanged; only propext, Classical.choice and Quot.sound occur. Every one of 720 own and nine attributed PNT+ modules plus root and registry is scanned for executable trust bypasses. Dependencies and pins remain unchanged.", 'Remaining: general native exponential differential formula, actual group/Lie lower-central layer identification, global inverse/BCH for arbitrary connected simply connected nilpotent Lie groups, faithful integration/Malcev comparison and arbitrary specified-lattice rational subgroup cocompactness. Nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and ordered positive arithmetic witness extraction remain unproved. StrongConjecture and the full prize target remain unproved; public repository creation, award PR and application await full formalization and audit.']

COMPONENTS = ['actual original group commutator identity derivative equals original adjoint minus identity, derived from actual multiplication and conjugation chain rules', 'actual original nested group commutators lie in original group lower-central layers and have genuine derivatives equal to ordered adjoint-difference products', 'original group lower-central termination forces every same-length ordered product of actual native bracket generators and same-cutoff powers to vanish by actual curve differentiation', 'actual Lie-action product cutoff controls original Lie lower-central series through its genuine bracket span and actual complementary-product kernels', 'original group nilpotency implies original native Lie-algebra nilpotency at the same cutoff, giving original native finite adjoint formulas at group nilpotencyClass without extra Lie-nilpotency premises']

NEW_PROGRESS = "The actual global linear equation identifies original adjoint curves and original exponential adjoints with genuine operator exponentials of their true derivative-defined generators. Original native chain rules identify the generators with the actual identity derivative of original adjoint; the genuine flow's mixed derivatives prove that their action equals the original native Lie bracket and their underlying linear maps equal original LieModule.toEnd. The actual original group commutator map now has proved native identity derivative Ad-g-id, derived from the genuine multiplication chain rule. Actual original nested commutator words have proved original group lower-central membership and derivatives equal to ordered actual adjoint-difference products. Original group lower-central termination makes each word identically identity and hence its derivative zero. Genuine differentiation along original native one-parameter curves replaces differences successively by actual bracket generators, proving that every same-length ordered generator product vanishes. The original Lie lower-central bracket-span definition and genuine operator kernels then show original native Lie lower-central termination at the same cutoff. Thus original Group.IsNilpotent now proves native LieModule.IsNilpotent without a supplied Lie-nilpotency premise. Actual original adjoint curves and exponential adjoints have finite formulas cut off at the original Group.nilpotencyClass. Individual group/Lie lower-central layer identification, the general native exponential differential formula, and global exponential invertibility/BCH still remain unproved."


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 808
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 733,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 21,
        "new_selected_report_count": 23, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 5, "new_theorem_count": 21,
                    "new_selected_report_count": 23, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ('\n2026-10-10 round-group-lie-nilpotency: PROGRESS. Five new modules, 21 proved theorems and two definitions; 23 exact new reports. All 733 baseline source/config hashes revalidated before registration; only root and registry change among retained files. Genuine original commutator derivative is Ad-id. Actual nested original group commutators lie in original group lower-central layers and differentiate to ordered adjoint-difference products. Original lower-central termination and genuine successive native curve derivatives prove all same-length bracket-generator products vanish. Actual Lie lower-central bracket spans and genuine product kernels prove original native Lie termination at the same cutoff. Original Group.IsNilpotent now gives native LieModule.IsNilpotent, and actual original finite adjoint formulas use Group.nilpotencyClass without an additional Lie-nilpotency premise. No individual group/Lie layer identification or global inverse/BCH is supplied. Complete build terminal exit 0: ' + str(verified["build_jobs"]) + ' jobs. Kernel terminal exit 0: 3687 exact unique standard-axiom reports; all retained axiom sets and six axiom-free reports unchanged. Scanned 720 own and nine attributed PNT+ modules plus root/registry; 738 current source/config hashes. New modules warning-free and oleans current; fixed local paper objects match, no remote updates checked. General native dexp, group/Lie layer comparison, global inverse/BCH, specified-lattice transfer, full calibration/Alignment and StrongConjecture remain unproved. No unavoidable blocker. Review: round-group-lie-nilpotency-review.json.\n\n')
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 720, "pntplus_modules": 9, "scanned_module_count": 729,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3687, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 733, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 21 and review["new_selected_report_count"] == 23
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 813 and manifest["proved_components"][-5:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 729 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3687 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 21, "new_selected_declarations": 23,
        "all_source_modules_scanned": 729, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3687,
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
