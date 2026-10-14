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
PREFIX = "round-rational-bch-layers"
OLD = "round-noncommuting-power-collection"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_FREE = {'Hindman168.lieWordValue', 'Hindman168.maskDescendant_some_of_noninvariant', 'Hindman168.finiteVectorPolynomialSum', 'Hindman168.boundedLieWordValues', 'Hindman168.lieWordValue_cons', 'Hindman168.maskDescendant_encoding_injective', 'Hindman168.lowerCentralCommutatorGenerators', 'Hindman168.matrixDepth_zero_iff_upper', 'Hindman168.maskDescendant_none_iff', 'Hindman168.lieWordValue_nil', 'Hindman168.matrixDepth_zero', 'Hindman168.MatrixDepth.smul'}
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
    assert len(baseline["files"]) == 883 and len(new_modules) == 6
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 871 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 35
    assert sum(c["theorems"] for c in module_counts.values()) == 33
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
    assert len(registered) == len(set(registered)) == len(actual) == 4297
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4262 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 889
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


APPLICATION = ['PROGRESS. The previous goal proof round made authoritative progress. The current baseline independently checks all 883 retained source/config hashes before registration, the preceding 4262 exact kernel reports and actual terminal successful log hashes. The six new proof modules are registered only after warning-free native compilation. Retained proof sources, StrongStatement, original Lie group, specified lattice, pins and attributed sources are unchanged; only retained root/registry change. No remote updates.', 'FiniteVectorPolynomialMixedSubspaces proves mixed bilinear coefficient propagation V x F to N, and positive adjoint-power propagation when N is contained in F. The finite polynomial sum is split with its genuine zero term retained. Exact primitive append and constant evaluation laws expose the actual affine initial curve. These algebraic results assume no topological closedness.', 'NativeLieRationalMixedDefect proves every coefficient of the genuine dexp-defect polynomial and each positive defect power lies in the specified rational improved layer N. The actual field polynomial is the original zero power q followed by a finite positive-power tail. The tail coefficients lie in N. These are the existing actual finite inverse-differential polynomials, not a supplied BCH model.', 'NativeLieRationalAffineLayer splits the actual Picard polynomial into u + q*w plus the rational primitive of that genuine tail. Exact rational coefficient evaluation proves the error lies in N for every positive iterate and rational time. The zero nilpotency class is handled from the actual original Lie lower-central termination, which forces the original model vector to be zero. Therefore actual logarithm lifting and actual global Log(Exp(u)Exp(w)) have their error in N when V is bracket closed, N is contained in F contained in V, and actual native brackets send V x F to N. No closed Q-subspace integration is used.', 'NativeLieRationalInternalLayers defines F_j as the image of the actual INTERNAL rational Lie lower-central series of A=V, using the genuine inclusion into the original native Lie algebra. F_0=V, F_j is antitone and contained in V; the actual native adjoint differential sends V x F_j to F_(j+1). The genuine bracket-preserving inclusion maps each internal layer into the original ambient rational Lie lower-central layer. Its proved termination at the original group nilpotency class implies F_c=0. This is an image of the internal rational series, not merely V intersect an ambient real layer.', 'NativeLieRationalInternalBCH proves the actual rational-time lift and actual product logarithm errors lie in F_(j+1) for w in F_j and u in V. At j+1=c the actual error vanishes, giving exact Log(Exp(u)Exp(w))=u+w. It constructs these same internal layers for the actual original W_Gamma=span_Q Log Gamma and proves actual Log(gh)-(Log g+Log h) is in its first internal rational layer. Gamma remains the specified original subgroup; Log Gamma is not assumed additive.', 'NativeSubgroupRationalNormalizedSpan proves monotonicity of original rational log spans and adjoint invariance under an actual specified conjugation condition. If actual K normalizes actual Delta, integer powers of elements of K give genuine adjoint curve values in W_Delta; actual rational coefficient extraction gives native brackets of Log K with Log Delta in W_Delta. Q bilinearity extends this to [W_K,W_Delta] contained in W_Delta. This supplies the relative ideal property needed for later group/Lie-layer comparison. It does not assert the original Gamma normal in the ambient group.', 'The general positive-root subgroup theorem remains proved. This round improves actual rational BCH error control but does not prove the full native rational hull lies in positive roots of Gamma. The equality W(Gamma) intersect native center = W(Gamma intersect center), full specified-lattice rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie-layer comparison, faithful integration/Malcev and full Calibration/Alignment/ordered positive witnesses remain unproved. StrongConjecture and the full prize target remain unproved. Full proof/audit precede publication/submission. No unavoidable blocker.', 'Six new modules, thirty-three proved theorems and two definitions give thirty-five new exact reports. The actual full build and kernel check cover 871 own and nine attributed PNT+ modules plus root/registry, with 889 current source/config hashes. All retained axiom sets and all twelve retained axiom-free reports are unchanged; no new empty report. New oleans are current; all executable sources have no banned proof placeholders or declared axioms, no new option overrides, and fixed local paper/pins match.']

COMPONENTS = ['actual mixed rational polynomial coefficients and positive adjoint powers propagate into the improved specified layer with explicit zero-term and primitive laws', 'actual Picard and global BCH affine errors lie in specified rational layers by finite rational polynomial primitives, including genuine zero-nilpotency-class handling', 'actual BCH errors improve INTERNAL rational Lie lower-central layers, with exact addition in the last layer and specialization to the original W_Gamma', 'actual internal rational lower-central layers are defined using the original Lie-subalgebra inclusion, are antitone and terminate at the original group nilpotency class', 'actual original finite dexp-defect positive-power coefficients lie in the improved rational layer while the genuine zero-power field term is retained', 'actual subgroup conjugation normalization implies rational log-span adjoint invariance and the relative bracket ideal property without assuming ambient lattice normality']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Generic genuine center-quotient induction proves finite-order generators in any nilpotent group generate a finite subgroup. NOW actual central commutator collection, actual iterated finite lower-central generator sets and their power propagation, proved relative normality of consecutive Gamma/lower-central joins, actual finite relative torsion-generator quotients and their actual exponents eliminate ALL actual lower-central remainders. Any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one uniform positive power sending every original element into the SAME Gamma. The actual two-generator subgroup therefore gives general noncommuting multiplication closure of roots(Gamma) without assuming Gamma normal. Actual positive roots form the least root-closed containing subgroup and are idempotent; every actual finitely generated subgroup of those roots has a uniform positive power in Gamma. General nonnormal root multiplication is proved. NOW the actual native BCH error is controlled in the INTERNAL rational lower-central series F_j of any original bracket-closed V, in particular the actual specified W_Gamma. Finite rational dexp-defect and Picard coefficient lists keep the genuine zero field term and prove Log(Exp(u)Exp(w))-(u+w) lies in F_(j+1) when u is in V and w is in F_j. The actual Lie-subalgebra inclusion proves F_0=V, antitonicity, bracket improvement and F_c=0 at the original group nilpotency class c, so the final layer gives exact addition. Zero nilpotency class is handled from actual original model termination. No Q-subspace topological closedness is assumed. Actual normalization of Delta by K implies [W_K,W_Delta] is contained in W_Delta using integer adjoint curve coefficient extraction. These actual rational error and relative ideal controls do NOT establish equality with the original group lower-central spans or logarithm additivity of roots(Gamma). Remaining: full native rational hull-to-Gamma positive powers (reverse of the proved root-to-hull inclusion); identify W(Gamma) intersect native center with the actual specified center rational log span; full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse group/Lie lower-central comparison and algebraic layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 958
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 883,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 33,
        "new_selected_report_count": 35, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 6, "new_theorem_count": 33,
                    "new_selected_report_count": 35, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = (
        "\n2026-10-10 round-rational-bch-layers: PROGRESS. "
        "Six new modules, thirty-three proved theorems and two definitions; thirty-five new exact reports. "
        "All 883 retained source/config baseline hashes checked before registration; retained proof sources unchanged. "
        "Actual finite rational dexp-defect positive powers improve the mixed rational layer; the zero field term is retained. "
        "Actual Picard primitives give Log(Exp(u)Exp(w))-(u+w) in N when [V,F] is contained in N contained in F contained in V. "
        "The actual zero nilpotency class is handled without an added positive-class hypothesis. "
        "Actual internal rational Lie lower-central layers F_j of V, rather than real-layer intersections, "
        "are antitone, improve under brackets with V, and terminate at the original group class c. "
        "Actual rational BCH error improves F_j to F_(j+1), with exact addition when j+1=c. "
        "These layers and error theorems specialize to the specified original W_Gamma. "
        "Actual normalization of Delta by K gives [W_K,W_Delta] contained in W_Delta by integer adjoint coefficient extraction. "
        "Gamma is not assumed normal in the ambient group; Log Gamma and logs of its roots are not assumed additive. "
        "Full hull-to-Gamma powers, W-center kernel equality, full rational-form induction, rational subgroup cocompactness, "
        "quantitative bounds, reverse group/Lie comparison, faithful integration/Malcev, "
        "Calibration/Alignment, ordered positive witnesses and the full target remain unproved. "
        "All 871 own and nine attributed PNT+ modules plus root/registry scanned; 889 current source/config hashes. "
        "All retained axiom sets and twelve empty reports unchanged; new empty reports exactly: "
        + repr(sorted(NEW_AXIOM_FREE)) + ". "
        "Actual complete build: " + str(verified["build_jobs"]) + " jobs; "
        "4297 exact unique standard-axiom reports, both actual terminal exit 0. "
        "New sources warning-free and oleans current; original pins and fixed local paper match. "
        "No remote updates. No unavoidable blocker. Review: round-rational-bch-layers-review.json.\n\n"
    )
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 871, "pntplus_modules": 9, "scanned_module_count": 880,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4297, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 883, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 33 and review["new_selected_report_count"] == 35
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 964 and manifest["proved_components"][-6:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 880 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4297 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 33, "new_selected_declarations": 35,
        "all_source_modules_scanned": 880, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4297,
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
