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
PREFIX = "round-native-center-roots"
OLD = "round-native-center-tangent"
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
    assert len(baseline["files"]) == 860 and len(new_modules) == 6
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 848 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 21
    assert sum(c["theorems"] for c in module_counts.values()) == 19
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
    assert len(registered) == len(set(registered)) == len(actual) == 4190
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4169 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 866
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


APPLICATION = ['PROGRESS: the previous original center quotient tangent round was independently rechecked before the pending proof edits, and all 860 baseline source/config hashes were verified before registration. Only retained root and registry change. Retained proof sources, StrongStatement, the original group and specified lattice, exact pins and attributed sources are unchanged. No remote updates.', 'PositiveSubgroupRoots defines the actual set of elements having a positive natural power in the specified subgroup. Actual group identities prove inclusion of the subgroup, inverse closure, repeated-root transitivity, conjugation by subgroup elements and multiplication closure for commuting roots. The common power for commuting products is the product of the two given powers. General noncommuting multiplication closure is not asserted.', 'CentralPositiveRootSubgroup constructs a genuine subgroup whose carrier is the intersection of that actual root set with the actual group center. Closure uses proved commuting-root multiplication and genuine center commutativity. No isolator-subgroup theorem is assumed.', 'RationalSpanPositiveDenominators strengthens retained integer denominator clearing to a positive natural denominator using the original integer submodule, absolute value and additive inverse closure. Conversely cancellation of a nonzero rational natural scalar proves span membership. This is an additive module theorem, not additive closure of nonabelian logarithms.', 'NativePositiveRootsRationalHull uses the genuine original Log(g^n)=n Log(g), real/rational scalar compatibility and rational scalar cancellation. Positive roots of the specified subgroup belong to its actual rational exponential hull; that hull is itself closed under positive roots and taking its rational log span again gives the original span. The reverse assertion that every hull element has a positive power in the specified subgroup remains unproved.', 'NativeCentralPowerRoots uses genuine original Log-center equivalence, power logarithms and nonzero real scalar cancellation in the actual real center model. An element is central exactly when any specified positive power is central. Therefore the roots of the actual Gamma-center intersection are exactly the actual central roots of Gamma.', 'NativeCenterRootSpan combines positive additive denominator clearing in the actual central integer logarithm lattice with the actual original exponential power law. The center rational log span consists exactly of vectors whose actual exponential has a positive power in Gamma. Retained genuine center-span inclusion and actual Exp/Log inverse laws identify its image with the logarithms of the actual central roots. The genuine rational exponential hull of Gamma intersect center is exactly the constructed central positive-root subgroup. The first theorem requires no global nilpotency/finite-dimensional/connected/simple-connected assumptions; those unused assumptions are explicitly omitted.', 'Six modules, nineteen proved theorems and two actual definitions give twenty-one exact new kernel reports. Actual complete build and exact kernel checks cover 848 own and nine attributed PNT+ source modules plus root/registry. All source/config hashes, retained axiom sets, actual empty reports, current new oleans and warning-free outputs are checked. No new options, unlimited heartbeats, disabled linters, proof placeholders or declared axioms.', 'Fixed local paper Section 07 lines 13-20 needs rational theory for the original arbitrary connected simply connected nilpotent group and its specified lattice. The proved exact center root-span result supplies the center denominator step of this induction. It does not identify W(Gamma) intersect the real center model with W(Gamma intersect center): that requires additional general noncommutative collection/root arguments. General root multiplication closure, full hull-to-Gamma positive powers, full ambient rational-form induction, arbitrary rational subgroup lattice cocompactness, quantitative bounds, reverse group/Lie lower-central comparison, Malcev, Calibration/Alignment and positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await the full proof and audit. No unavoidable blocker.']

COMPONENTS = ['actual specified subgroup positive-power root set has inverse, repeated-root, conjugation and commuting-product closure by genuine group power identities', 'actual specified subgroup positive roots inside the genuine center form a genuine central subgroup without assuming general isolator closure', 'actual rational span of an integer submodule equals vectors with a positive natural multiple in that original integer submodule', 'actual positive roots belong to the original rational exponential hull, which is root closed and has exactly the original rational logarithmic span', 'actual positive-power centrality is equivalent to original centrality and roots of the specified center intersection are precisely its central roots', 'actual specified center lattice rational logarithmic span and rational exponential hull exactly identify the genuine central positive-root subgroup']

NEW_PROGRESS = 'Retained genuine original native exponential/logarithm diffeomorphism, rational finite BCH/Picard construction, actual W bracket closure, full real logarithmic span and actual Gamma finite generation remain proved for the arbitrary original specified lattice. The actual center logarithmic integer lattice is discrete and full, with compact additive quotient and real-independent compatible rational basis. The actual center quotient image lattice is discrete and cocompact, and its original quotient group is contractible, simply connected and Hausdorff with a constructed genuine smooth LieGroup and strictly lower real model dimension. Actual Dq equals the original quotient pi with kernel the actual center model V; actual pi preserves genuine native Lie brackets. Genuine smooth-homomorphism ODE uniqueness and inverse laws identify the native quotient Exp/Log with the constructed coordinate maps. Hence pi maps the actual specified subgroup W=span_Q Log Gamma exactly onto the projected actual subgroup rational span. Now actual positive roots of Gamma lie in its actual rational exponential hull, and that hull is closed under positive roots with unchanged rational log span. Actual positive-power centrality is equivalent to centrality. Actual central roots of Gamma form a genuine subgroup; positive denominator clearing in the actual additive central integer lattice proves the rational exponential hull of Gamma intersect center equals that central root subgroup exactly. General nonabelian Log Gamma is never assumed additive. Remaining: prove W(Gamma) intersect V equals the actual specified center rational log span, general noncommuting positive-root multiplication closure and that every element of the full rational hull has a positive Gamma power; complete full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse original group/Lie lower-central comparison and algebraic layer closedness; faithful integration/Malcev. Full Calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and full prize target remain unproved; publication and submission await the full proof and audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 935
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 860,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 19,
        "new_selected_report_count": 21, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 6, "new_theorem_count": 19,
                    "new_selected_report_count": 21, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-native-center-roots: PROGRESS. Six new modules, nineteen proved theorems and two definitions; twenty-one exact new reports. All 860 baseline hashes verified before registration; only retained root/registry change. Genuine group identities prove inverse, repeated-root, subgroup-conjugation and commuting-product closure of actual positive roots. Actual central roots form a genuine subgroup. Positive natural denominator clearing in the actual additive central integer log lattice and genuine Exp/Log power and inverse laws identify W(Gamma intersect center) and its actual rational exponential hull exactly with the logs and elements of the central root subgroup. Positive powers detect actual centrality. All Gamma roots belong to the original rational hull; that hull is root closed with the original Q-log span. General noncommuting root multiplication, full hull-to-Gamma positive powers and W(Gamma) intersect V identification remain unproved. Full original ambient rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. All retained axiom sets and eleven retained axiom-free reports unchanged; exact new reports have no empty axiom sets. All 848 own and nine attributed PNT+ modules plus root/registry scanned; 866 source/config hashes. Actual full build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4190 exact unique allowed-standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Actual pins and fixed local paper match; no remote updates. No unavoidable blocker. Review: round-native-center-roots-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 848, "pntplus_modules": 9, "scanned_module_count": 857,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4190, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 860, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 19 and review["new_selected_report_count"] == 21
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 941 and manifest["proved_components"][-6:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 6
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
    assert scan["scanned_module_count"] == 857 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4190 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 19, "new_selected_declarations": 21,
        "all_source_modules_scanned": 857, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4190,
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
