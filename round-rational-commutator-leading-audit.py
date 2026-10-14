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
PREFIX = "round-rational-commutator-leading"
OLD = "round-rational-bch-layers"
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
    assert len(baseline["files"]) == 889 and len(new_modules) == 8
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 879 and len(pnt) == 9
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
    assert len(registered) == len(set(registered)) == len(actual) == 4323
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4297 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 897
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


APPLICATION = ['PROGRESS. The previous round made authoritative proof progress. Its complete actual audit was freshly rechecked before current edits. All 889 retained baseline source/config hashes, preceding 4297 exact kernel reports and actual successful terminal log hashes were independently checked before registration. All retained proof sources, original Lie group, specified lattice Gamma, StrongStatement, pins and attributed sources are unchanged; only retained root/registry change. No remote updates.', 'RationalBilinearPairIdeal uses genuine real continuous bilinearity restricted to Q. If B is alternating, N is stable under B(V,N), u,w lie in V and B(u,w) lies in N, the actual P=span_Q{u,w} joined with N satisfies B(P,P) contained in N. Both directions use actual submodule span/comap laws and skew symmetry. N remains the actual specified subspace.', 'NativeLieRationalPairIdealBCH proves the native adjoint differential self/skew identities from the actual original adjoint generator. The preceding actual pair span P is proved native-bracket closed, and the previously proved rational Picard affine theorem then gives genuine Log(Exp(u)Exp(w))-(u+w) in N under that pair ideal condition. No quotient logarithm, rational BCH formula or closed Q-subspace is assumed.', 'NativeLieRationalAdjointInternal proves actual adjoint powers send F_j to F_(j+n), and Ad(Exp(v))w-w lies in F_(j+1). A genuine padded finite adjoint polynomial keeps the constant and linear terms even in original classes zero/one. Subtracting them gives an exact finite rational-factorial sum of powers starting at two. Thus Ad(Exp(v))w-w-[v,w] lies in F_(j+2). Actual adjoint exponentials preserve F_j. The layers are INTERNAL rational layers of the actual V.', 'NativeLieRationalCommutatorLeading retains actual conjugation Exp(v)Exp(w)Exp(v)^-1=Exp(Ad(Exp(v))w) and the actual inverse Exp(-w). The bracket of Ad(Exp(v))w with -w is the bracket of w with the actual difference Ad(Exp(v))w-w, so it is in F_(j+2). The genuine pair-ideal BCH error and adjoint remainder are added, proving Log([Exp(v),Exp(w)])-[v,w] in F_(j+2), and therefore the actual group commutator logarithm lies in F_(j+1). Signs correspond to the actual original group commutator convention; no model commutator is substituted.', 'NativeLieRationalInternalGeneration proves an exact successor-generation criterion: F_(j+1) is contained in N iff every actual native bracket of V with F_j is in N. The proof maps the actual internal Lie lower-central bracket span using the genuine original inclusion. Every F_j is proved native-bracket closed; its actual exponential image is consequently a genuine subgroup, with actual Log membership iff.', 'NativeSubgroupRationalGroupLayers proves the actual original Gamma.lowerCentralSeries j is contained in the exponential subgroup of its own F_j. Genuine subgroup commutator generation and the already proved actual commutator logarithm comparison drive the induction. Therefore every actual Gamma_j logarithm and its whole Q span lie in F_j. No ambient normality of Gamma, finite generation of Gamma, matrix substitution, or layer equality is assumed.', 'NativeLieRationalLayerDescent proves a stable N absorbs a genuine next-layer remainder. If F_j is contained in N joined with F_(j+1), bracket generation propagates the same assertion to all subsequent layers. A second induction retains the remainder while lowering it to F_(j+c)=0 at the original class c, proving F_j contained in N. The terminating original filtration, rather than an assumed absorption statement, removes the remainder.', 'NativeSubgroupRationalLayerEquality proves actual generator brackets are in W_(Gamma_(j+1)) joined with F_(j+2) using actual commutator leading terms. True Q bilinearity extends this to W_Gamma x W_(Gamma_j). The genuine self-normalizer theorem proves Gamma normalizes its own Gamma_(j+1); the preceding normalization theorem gives the actual ideal property of W_(Gamma_(j+1)) inside W_Gamma. Induction, exact successor generation and genuine terminating remainder absorption now prove W_(Gamma_j)=F_j for EVERY j of the specified original subgroup. This is equality of actual Q log SPANS, not an assertion Gamma_j=Exp(F_j) or real closedness of Gamma_j.', 'The full native rational hull-to-Gamma positive power theorem is still unproved. The new Q log-span comparison closes that particular missing rational-layer equality. Next, actual ideal-coset exponential stability and rational-power membership must be constructed, then used in a downward terminating induction for the actual root subgroup. W-center kernel equality, full scalar-extension/rational-form induction, arbitrary specified-lattice rational subgroup cocompactness, quantitative bounds, whole-group/real-Lie layer equality and closedness, faithful integration/Malcev, Calibration/Alignment and ordered positive witnesses remain unproved. StrongConjecture and the full prize target remain unproved. Publication/submission await complete proof and audit. No unavoidable blocker.', 'Eight new modules, twenty-five proved theorems and one definition give twenty-six new exact kernel reports. The actual full build and kernel cover all 879 own and nine attributed PNT+ modules plus root/registry; 897 current source/config hashes. All twelve retained empty reports and all retained axiom sets are unchanged; no new empty reports. Only standard axioms, no proof placeholders or declared axioms, no new option overrides, current oleans, and exact original pins/fixed local paper are independently checked.']

COMPONENTS = ['actual adjoint finite rational factorial formula separates constant and bracket terms, controlling its first and second internal rational-layer remainders', 'actual original commutator logarithm equals the native bracket modulo the next internal rational layer using genuine conjugation and pair-ideal BCH remainders', 'actual internal rational successor layers are generated by original brackets and their true exponential images are proved subgroups', 'actual stable rational subspaces absorb retained next-layer remainders by two inductions down the terminating original internal series', 'actual native pair-ideal BCH errors lie in the specified rational ideal through a constructed bracket-closed pair span', 'actual specified subgroup lower-central logarithms and their Q spans lie in the corresponding original internal rational Lie layers', 'actual specified subgroup lower-central Q log spans EQUAL every internal rational Lie layer by commutator leading terms, relative normalization and terminating remainder absorption', 'actual alternating bilinear brackets of a pair span joined with a stable rational subspace lie in that same specified subspace']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Generic genuine center-quotient induction proves finite-order generators in any nilpotent group generate a finite subgroup. NOW actual central commutator collection, actual iterated finite lower-central generator sets and their power propagation, proved relative normality of consecutive Gamma/lower-central joins, actual finite relative torsion-generator quotients and their actual exponents eliminate ALL actual lower-central remainders. Any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one uniform positive power sending every original element into the SAME Gamma. The actual two-generator subgroup therefore gives general noncommuting multiplication closure of roots(Gamma) without assuming Gamma normal. Actual positive roots form the least root-closed containing subgroup and are idempotent; every actual finitely generated subgroup of those roots has a uniform positive power in Gamma. General nonnormal root multiplication is proved. NOW actual rational BCH affine errors lie in the internal next layer F_(j+1), and the actual original Lie inclusion proves F_c=0. Actual alternating pair spans and rational Picard primitives prove the genuine pair-ideal BCH error. Actual adjoint rational factorial expansion separates its constant and native bracket term. For w in F_j the actual original group commutator satisfies Log([Exp(v),Exp(w)])-[v,w] in F_(j+2), so its log lies in F_(j+1). The actual internal successor-generation criterion and genuine exponential-layer subgroups give W(Gamma.lowerCentralSeries j) contained in F_j. Actual generator brackets give the reverse containment modulo the next layer. Genuine normalization by Gamma makes W(Gamma_(j+1)) a stable rational ideal. Two actual terminating Lie-layer inductions remove the retained remainder. Thus W(Gamma.lowerCentralSeries j)=F_j for every j is NOW PROVED for the SAME specified original Gamma, without assuming ambient normality or finite generation of Gamma. This is equality of Q LOG SPANS, not whole subgroup equality, real closedness or logarithm additivity of roots. Remaining: full native rational hull-to-Gamma positive powers; next construct actual ideal-coset exponential stability and rational-power root membership, then descend from the terminating F_c using the proved actual group-layer log spans. Identify W(Gamma) intersect native center with the actual specified center rational log span; full ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; whole original group/real-Lie lower-central equality and layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 964
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 889,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 25,
        "new_selected_report_count": 26, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 8, "new_theorem_count": 25,
                    "new_selected_report_count": 26, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = (
        "\n2026-10-10 round-rational-commutator-leading: PROGRESS. "
        "Eight new modules, twenty-five proved theorems and one definition; twenty-six exact new reports. "
        "All 889 retained source/config hashes independently checked before registration; retained proof sources unchanged. "
        "Actual alternating pair-ideal bilinearity and native rational Picard primitives give genuine pair-ideal BCH error. "
        "Actual adjoint rational factorial expansion separates the constant and first bracket term; its remainder is in F_(j+2). "
        "Actual original conjugation and inverse exponentials then give Log([Exp(v),Exp(w)])-[v,w] in F_(j+2) for w in F_j. "
        "Actual internal bracket successor generation and actual exponential layer subgroups give the forward group-layer Q log-span comparison. "
        "Actual original commutators give reverse generator inclusion modulo the next rational layer. "
        "Gamma normalizes its own actual lower-central subgroups, giving the genuine relative Q ideal property. "
        "Two terminating internal-layer inductions retain and lower each remainder to zero. "
        "Thus the actual original W(Gamma.lowerCentralSeries j)=F_j is NOW PROVED for every j, "
        "without ambient Gamma normality or Gamma finite-generation assumptions. "
        "This is Q LOG SPAN equality, not whole group-layer equality or real closedness. "
        "Full hull-to-Gamma positive powers, W-center kernel equality, rational-form induction, rational subgroup cocompactness, "
        "quantitative bounds, whole group/real-Lie layer equality and closedness, faithful integration/Malcev, "
        "Calibration/Alignment, ordered positive witnesses and the full target remain unproved. "
        "All 879 own and nine attributed PNT+ modules plus root/registry scanned; 897 source/config hashes. "
        "All retained standard-axiom sets and twelve empty reports unchanged; new empty reports exactly: "
        + repr(sorted(NEW_AXIOM_FREE)) + ". "
        "Actual full build: " + str(verified["build_jobs"]) + " jobs; "
        "4323 exact unique standard-axiom reports, both actual terminal exit 0. "
        "New sources warning-free and oleans current; original pins and fixed local paper match. "
        "No remote updates. No unavoidable blocker. Review: round-rational-commutator-leading-review.json.\n\n"
    )
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 879, "pntplus_modules": 9, "scanned_module_count": 888,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4323, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 889, "previous_current_state_rechecked_before_edits": True,
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
    assert len(manifest["proved_components"]) == 972 and manifest["proved_components"][-8:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 888 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4323 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 25, "new_selected_declarations": 26,
        "all_source_modules_scanned": 888, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4323,
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
