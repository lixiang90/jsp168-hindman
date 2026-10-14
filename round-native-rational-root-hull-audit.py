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
PREFIX = "round-native-rational-root-hull"
OLD = 'round-rational-commutator-leading'
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
AXIOM_FREE = {'Hindman168.MatrixDepth.smul', 'Hindman168.boundedLieWordValues', 'Hindman168.maskDescendant_encoding_injective', 'Hindman168.lieWordValue_cons', 'Hindman168.matrixDepth_zero_iff_upper', 'Hindman168.lieWordValue', 'Hindman168.maskDescendant_none_iff', 'Hindman168.lowerCentralCommutatorGenerators', 'Hindman168.finiteVectorPolynomialSum', 'Hindman168.maskDescendant_some_of_noninvariant', 'Hindman168.lieWordValue_nil', 'Hindman168.matrixDepth_zero'}
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
    assert len(baseline["files"]) == 897 and len(new_modules) == 7
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 886 and len(pnt) == 9
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
    assert sum(c["theorems"] for c in module_counts.values()) == 24
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
    assert len(registered) == len(set(registered)) == len(actual) == 4349
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4323 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 904
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


APPLICATION = ['PROGRESS. The previous goal proof round made authoritative progress. The retained baseline was independently rechecked in this turn: all 897 current source/config hashes, preceding 4323 exact kernel reports, successful actual terminal log hashes, registry coverage and combined logs. All retained proof sources, original Lie group, specified subgroup/lattice Gamma, StrongStatement, dependency pins and attributed sources remain unchanged; only root/registry change. No remote updates.', 'NativeLieRationalPowerMembership proves actual integer exponential powers, including negative powers, and clears each genuine rational denominator: Exp(q v)^den(q)=Exp(v)^num(q). A genuinely positive-root-closed subgroup is thus closed under Exp of rational multiples of its own actual logarithms. This uses actual powers in the same original group and no added BCH or root-membership premise for Gamma.', 'NativeLieRationalIdealCosets proves the actual Log(Exp(u)Exp(w)^-1) lies in N whenever u-w lies in the specified rational ideal N of V. Genuine alternating native bracket identities and the already proved pair-ideal BCH error give this membership. Multiplying the actual inverse difference transfers subgroup exponential membership from u to w when all actual Exp(N) already lie in that subgroup. No quotient Exp/Log maps or ambient subgroup normality are assumed.', 'NativeLieRationalRootLayerSubmodule constructs the actual Q subspace {v in F_j : Exp(v) in K}, conditional on Exp(F_(j+1)) contained in the positive-root-closed subgroup K. Genuine native BCH puts the product logarithm minus u+w in F_(j+1); the proved ideal-coset transfer removes this error. Actual rational denominator clearing proves scalar closure. The next-layer condition is proved by the following terminating induction rather than treated as a global assumption.', 'NativeSubgroupRationalRootInduction descends from the actual zero internal layer F_(j+n)=0. At each step the original Gamma.lowerCentralSeries j logarithms belong to the constructed Q subspace because their exponentials are the same actual original subgroup elements. The proved equality W(Gamma_j)=F_j and the actual Q span universal property extend this to the full layer. Thus the full original rational hull is contained in EVERY positive-root-closed subgroup containing Gamma. No Gamma normality, finite generation, discreteness or lattice replacement is required.', 'NativeSubgroupRationalHullRoots applies that genuine induction to the already proved arbitrary nilpotent positive-root subgroup. The opposite inclusion was retained and independently checked. Consequently the FULL actual native rational hull equals roots(Gamma), and actual membership is iff some positive integer power lies in the SAME Gamma. The logarithmic rational span has the corresponding Exp membership iff. Actual finitely generated subgroups of this hull now have one common positive exponent sending every element into Gamma. No explicit quantitative denominator bound is claimed.', 'NativeSubgroupRationalCenterKernel combines FULL hull positive powers with genuine central denominator clearing. An actual v in W(Gamma) and the native real center exponentiates to a central positive root of Gamma; the already proved central-root logarithmic span theorem gives v in W(Gamma intersect center). The reverse inclusion uses actual center logarithms and span monotonicity. Thus W(Gamma) intersect native center = W(Gamma intersect center), and the corresponding hull center-intersection equality is proved. These algebraic equalities require no lattice or discreteness hypotheses.', 'NativeCenterQuotientRationalKernel constructs an ACTUAL Q-linear equivalence between the kernel of the actual quotient projection restricted to W(Gamma) and W(Gamma intersect center). Actual rank-nullity and the retained quotient log-span image equality give an exact Q dimension decomposition when W has finite Q dimension. For the original specified discrete cocompact lattice, the genuine center integer/rational basis proves the center summand dimension equals the real center dimension. The resulting center-quotient DIMENSION STEP is proved; its hypothesis for the quotient remains explicit. A full recursive rational-form/scalar-extension induction is not asserted complete.', 'Full native hull positive powers and actual W-center kernel equality are now proved. Full ambient rational-dimension induction, real-compatible basis/scalar-extension injectivity, arbitrary specified-lattice rational subgroup cocompactness, explicit quantitative bounds, whole-group/real-Lie layer equality and closedness, faithful integration/Malcev, Calibration/Alignment and ordered positive witnesses remain. StrongConjecture and the full prize target remain unproved. Publication/submission await full proof and audit. No unavoidable blocker.', 'Seven new modules, twenty-four proved theorems and two definitions give twenty-six new exact kernel reports. The actual successful full build and kernel cover all 886 own and nine attributed PNT+ modules plus root/registry; 904 source/config hashes. All twelve retained axiom-free reports and every retained axiom set are unchanged; no new empty reports. Only standard axioms, no proof placeholders or declared axioms, no new option overrides, warning-free new sources, current oleans, and exact original pins/fixed local paper are checked.']

COMPONENTS = ['actual original integer exponential powers and rational denominator clearing prove rational exponential membership in any genuine positive-root-closed subgroup', 'actual rational ideal difference gives original exponential coset membership transfer through genuine pair-ideal BCH', 'actual root-closed subgroup exponential membership within each internal rational layer is a genuine Q subspace after next-layer error removal', 'actual terminating downward Lie-layer induction proves the full specified-subgroup rational hull is contained in every containing positive-root-closed subgroup', 'FULL actual native rational hull equals positive roots of the SAME specified subgroup, with genuine positive-power membership iff and finitely generated uniform powers', 'actual specified-subgroup rational logarithmic CENTER KERNEL equals the Q log span of its actual original center intersection, with corresponding hull intersection equality', 'actual center-quotient rational kernel equivalence and rank-nullity decomposition give a proved specified-lattice rational dimension induction STEP']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Generic genuine center-quotient induction proves finite-order generators in any nilpotent group generate a finite subgroup. NOW actual central commutator collection, actual iterated finite lower-central generator sets and their power propagation, proved relative normality of consecutive Gamma/lower-central joins, actual finite relative torsion-generator quotients and their actual exponents eliminate ALL actual lower-central remainders. Any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one uniform positive power sending every original element into the SAME Gamma. The actual two-generator subgroup therefore gives general noncommuting multiplication closure of roots(Gamma) without assuming Gamma normal. Actual positive roots form the least root-closed containing subgroup and are idempotent; every actual finitely generated subgroup of those roots has a uniform positive power in Gamma. General nonnormal root multiplication is proved. NOW actual rational BCH affine errors lie in the internal next layer F_(j+1), and the actual original Lie inclusion proves F_c=0. Actual alternating pair spans and rational Picard primitives prove the genuine pair-ideal BCH error. Actual adjoint rational factorial expansion separates its constant and native bracket term. For w in F_j the actual original group commutator satisfies Log([Exp(v),Exp(w)])-[v,w] in F_(j+2), so its log lies in F_(j+1). The actual internal successor-generation criterion and genuine exponential-layer subgroups give W(Gamma.lowerCentralSeries j) contained in F_j. Actual generator brackets give the reverse containment modulo the next layer. Genuine normalization by Gamma makes W(Gamma_(j+1)) a stable rational ideal. Two actual terminating Lie-layer inductions remove the retained remainder. Thus W(Gamma.lowerCentralSeries j)=F_j for every j is NOW PROVED for the SAME specified original Gamma, without assuming ambient normality or finite generation of Gamma. This is equality of Q LOG SPANS, not whole subgroup equality or real closedness.  NOW actual integer/rational exponential powers and genuine rational ideal-coset stability are proved in the original group. For a root-closed actual subgroup K, next-layer exponential membership removes genuine BCH errors and constructs the Q subspace of F_j exponentiating into K. Actual downward induction starts at the terminating original F_c=0 and uses the PROVED W(Gamma_j)=F_j to supply every original group-layer generator. Therefore the FULL original native rational hull is the least positive-root-closed subgroup containing the SAME specified Gamma. Applying this to the genuine arbitrary nilpotent root subgroup proves nativeHull(Gamma)=roots(Gamma), without Gamma normality, finite generation or discreteness assumptions. Every actual hull element has some positive integer power in Gamma; every actual finitely generated subgroup of that hull has one uniform such power. Full root membership plus genuine central denominator clearing NOW PROVE W(Gamma) intersect native center = W(Gamma intersect original group center), and the corresponding actual hull intersection equality. The actual original center projection restricted to W has a constructed Q kernel equivalence with that center-intersection span. Actual rank-nullity gives the rational dimension decomposition; the actual specified center lattice has rational dimension equal to its real dimension. The center-quotient rational DIMENSION INDUCTION STEP is now proved, with the quotient dimension equality explicitly required as its induction hypothesis. Remaining: complete the ambient rational-dimension induction through strictly smaller actual center quotients, then obtain a real-compatible rational basis and full scalar-extension injectivity for the specified lattice; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; whole original group/real-Lie lower-central equality and layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 972
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 897,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 24,
        "new_selected_report_count": 26, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 7, "new_theorem_count": 24,
                    "new_selected_report_count": 26, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = (
        "\n2026-10-10 round-native-rational-root-hull: PROGRESS. "
        "Seven new modules, twenty-four proved theorems and two definitions; twenty-six exact new reports. "
        "All 897 retained baseline source/config hashes and previous terminal log/kernel evidence independently checked; retained proof sources unchanged. "
        "Actual integer/rational exponential powers and ideal-coset BCH stability construct genuine layer Q subspaces in root-closed subgroups. "
        "Terminating original internal-layer descent, using proved W(Gamma_j)=F_j, proves the actual full rational hull is least root-closed over the SAME Gamma. "
        "FULL nativeHull(Gamma)=roots(Gamma) and actual positive-power membership iff are NOW PROVED without subgroup normality, finite generation or discreteness assumptions. "
        "Actual finitely generated hull subgroups have a uniform positive power in Gamma; no explicit numerical bound is claimed. "
        "Full hull roots and genuine central denominator clearing prove W(Gamma) intersect native center = W(Gamma intersect center), and actual hull intersection equality. "
        "A constructed actual rational center-quotient kernel equivalence gives exact rank-nullity. "
        "For the SAME specified lattice, the center rational summand has its actual real dimension; the rational dimension INDUCTION STEP is proved. "
        "Full dimension recursion, real-compatible rational basis/scalar extension, rational subgroup cocompactness, quantitative bounds, "
        "whole group/real-Lie layer equality and closedness, faithful integration/Malcev, Calibration/Alignment, ordered positive witnesses and full target remain. "
        "All 886 own and nine attributed PNT+ modules plus root/registry scanned; 904 source/config hashes. "
        "All retained standard-axiom sets and twelve empty reports unchanged; new empty reports exactly: "
        + repr(sorted(NEW_AXIOM_FREE)) + ". "
        "Actual full build: " + str(verified["build_jobs"]) + " jobs; "
        "4349 exact unique standard-axiom reports, both actual terminal exit 0. "
        "New sources warning-free and oleans current; original pins and fixed local paper match. "
        "No remote updates. No unavoidable blocker. Review: round-native-rational-root-hull-review.json.\n\n"
    )
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 886, "pntplus_modules": 9, "scanned_module_count": 895,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4349, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 897, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 24 and review["new_selected_report_count"] == 26
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 979 and manifest["proved_components"][-7:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 7
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
    assert scan["scanned_module_count"] == 895 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4349 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 24, "new_selected_declarations": 26,
        "all_source_modules_scanned": 895, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4349,
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
