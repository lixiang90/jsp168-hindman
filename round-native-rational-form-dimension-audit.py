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
PREFIX = 'round-native-rational-form-dimension'
OLD = 'round-native-rational-root-hull'
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
    assert len(baseline["files"]) == 904 and len(new_modules) == 8
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 894 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 38
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
    assert len(jobs) == 1 and int(jobs[0]) >= baseline["build_job_count"] + len(new_modules)
    assert not re.search(rb"(?:error:|warning:)", blog), "build diagnostics"
    previous = reports(OLD + "-axioms.txt")
    old_result = obj(OLD + "-kernel-result.json")
    assert old_result["exit_code"] == 0 and old_result["terminal"] is True
    assert digest(OLD + "-axioms.txt") == old_result["log_sha256"]
    actual = reports(PREFIX + "-axioms.txt")
    registered = re.findall(r"^#print axioms (\S+)", lean_code(read("Verification.lean")), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 4387
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4349 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 912
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


APPLICATION = ['PROGRESS. The preceding goal proof round made authoritative progress. In this turn all 904 current retained source/config hashes, all 4349 exact unique preceding kernel reports, registration coverage, prior terminal build/kernel log hashes and the full combined logs were independently rechecked before root/registry registration. All retained proof sources, the original Lie group and model with corners, the actual specified subgroup/lattice Gamma, StrongStatement, original dependency pins and attributed sources remain unchanged. No official or remote updates.', 'NativeLatticeRationalDimension proves the FULL equality dim_Q W_Gamma = dim_R E for every original discrete cocompact specified lattice. Strong induction is quantified over all actual identity-model groups in fixed arbitrary universes; actual center quotients keep these universes and strictly decrease the real model dimension. The genuine quotient structures and discrete cocompact image lattice are already constructed and used. The subsingleton group case uses the actual injective exponential to prove the original model subsingleton. One genuine center-quotient step then applies the established identity-model theorem to the actual quotient of ANY original model with corners. No original recharting, matrix substitution, replacement lattice, supplied rational dimension equality or restricted original model is used.', 'RationalSubspaceRealBasis constructs a rational basis from a full rational subspace of the proved correct dimension. Its SAME original vectors span the real space by the genuine scalar-tower span theorem; the correct finite cardinality then proves real linear independence. These columns construct an actual real basis, and equality of the original columns is proved. The generic dimension and full-real-span premises are proved for the actual native lattice by retained full spanning and the new full dimension induction, rather than assumed in the native application.', 'RationalSubspaceScalarExtension constructs the genuine NATURAL map R tensor_Q W -> E, r tensor w maps to r times the original w. A scalar-extended rational basis and the real basis give an equivalence, and equality on the actual tensor basis identifies its linear map with this natural map. Hence natural scalar-extension bijectivity is proved, and its tensor values are checked. The result is not merely the existence of an unrelated dimension-count isomorphism.', 'NativeLatticeRationalForm applies these constructions to the SAME original W_Gamma = span_Q Log Gamma, with all finite-dimensional, dimension and real-span requirements discharged by genuine native results. It constructs compatible Q/R bases in the original real model, proves exact rational spanning and real linear independence, and constructs the actual natural scalar-extension equivalence with its original-vector tensor formula. It does not identify nonabelian Log Gamma with an additive integer lattice or change Gamma.', 'RationalSubspaceCoordinates proves the actual rational and real coordinate square commutes by genuine basis reconstruction and the actual rational/real scalar compatibility. Membership in W is then iff the genuine real coordinates are the cast of one rational coordinate vector, equivalently each real coordinate is rational. No rationality of the tested vector is assumed as a replacement for the membership proof.', 'RationalCoordinateSpanPreimage proves that the real span of any actual rational coordinate subspace creates no new rational coordinate vectors. Choose an actual Hamel coordinate of 1 with nonzero rational coefficient, apply the retained genuine real-rational component membership theorem, and invert this nonzero rational coefficient inside the original rational subspace. This proves the original preimage equality for arbitrary coordinate index types, without requiring finite index or assuming an intersection theorem.', 'RationalSubspaceSpanIntersection transports the genuine coordinate-span preimage theorem through the actual compatible bases and the commuting inclusion square. For every actual Q subspace U of W, a vector of W lies in real span U iff it lies in U; consequently real span U intersect W equals the original ambient image of U. The coercion equality is definitional and checked by Lean. No scalar-extension injectivity or real/rational intersection conclusion is an extra native hypothesis.', 'NativeLatticeRationalCoordinates gives the original specified lattice coordinate membership criterion and combines it with the retained FULL positive-power characterization: Exp(v) has a positive power in the SAME Gamma iff all actual native real coordinates of v are rational. For every original ambient Q subspace U contained in W_Gamma, real span U intersect W_Gamma = U. Native rational subspace is defined using exactly the original W_Gamma intersection, and the real span of each such U satisfies that definition. This establishes rational-form coordinates and intersections, not yet arbitrary rational subgroup cocompactness.', 'The full original native rational dimension induction, compatible original Q/R bases and NATURAL scalar-extension bijectivity are NOW proved. Arbitrary specified-lattice rational subgroup cocompactness, explicit quantitative degree/denominator bounds, whole original group/real-Lie lower-central equality and layer closedness, faithful integration/Malcev, full Calibration/Alignment and ordered positive arithmetic witnesses remain. StrongConjecture and the complete prize target remain unproved. Publication and submission await full proof and audit. No unavoidable blocker.', 'Eight new modules, thirty proved theorems and eight definitions give thirty-eight new exact kernel reports. Actual full build and kernel checks cover all 894 own and nine attributed PNT+ modules plus root/registry, with 912 current source/config hashes. Every retained axiom set and all twelve retained axiom-free reports are unchanged; no new empty reports. Only standard axioms, no proof placeholders or declared axioms, no new option overrides, warning-free new sources, current oleans and exact retained pins/fixed local paper are checked.']

COMPONENTS = ['FULL original specified-lattice rational dimension equality is proved by terminating actual center-quotient induction, retaining arbitrary original model with corners and actual Gamma', 'an actual full rational subspace of the correct proved dimension has a Q basis whose SAME original vectors are an R basis, with real linear independence proved', 'the actual NATURAL scalar-extension map R tensor_Q W -> original E is bijective and agrees with the constructed tensor-basis equivalence', 'actual original specified-lattice compatible Q/R bases and natural scalar-extension equivalence are constructed with all native requirements proved', 'actual rational and real basis coordinates commute and genuine original rational-subspace membership is iff all real coordinates are rational', 'real span of any actual rational coordinate subspace creates no new rational vectors, proved via a genuine nonzero Hamel coordinate of one', 'actual real span of every Q subspace inside the full rational form intersects that form in exactly the original Q subspace', 'original specified-lattice rational coordinates characterize positive powers in the SAME Gamma; actual ambient rational spans have exact W_Gamma intersections and satisfy the genuine rational-subspace definition']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Generic genuine center-quotient induction proves finite-order generators in any nilpotent group generate a finite subgroup. NOW actual central commutator collection, actual iterated finite lower-central generator sets and their power propagation, proved relative normality of consecutive Gamma/lower-central joins, actual finite relative torsion-generator quotients and their actual exponents eliminate ALL actual lower-central remainders. Any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one uniform positive power sending every original element into the SAME Gamma. The actual two-generator subgroup therefore gives general noncommuting multiplication closure of roots(Gamma) without assuming Gamma normal. Actual positive roots form the least root-closed containing subgroup and are idempotent; every actual finitely generated subgroup of those roots has a uniform positive power in Gamma. General nonnormal root multiplication is proved. NOW actual rational BCH affine errors lie in the internal next layer F_(j+1), and the actual original Lie inclusion proves F_c=0. Actual alternating pair spans and rational Picard primitives prove the genuine pair-ideal BCH error. Actual adjoint rational factorial expansion separates its constant and native bracket term. For w in F_j the actual original group commutator satisfies Log([Exp(v),Exp(w)])-[v,w] in F_(j+2), so its log lies in F_(j+1). The actual internal successor-generation criterion and genuine exponential-layer subgroups give W(Gamma.lowerCentralSeries j) contained in F_j. Actual generator brackets give the reverse containment modulo the next layer. Genuine normalization by Gamma makes W(Gamma_(j+1)) a stable rational ideal. Two actual terminating Lie-layer inductions remove the retained remainder. Thus W(Gamma.lowerCentralSeries j)=F_j for every j is NOW PROVED for the SAME specified original Gamma, without assuming ambient normality or finite generation of Gamma. This is equality of Q LOG SPANS, not whole subgroup equality or real closedness.  NOW actual integer/rational exponential powers and genuine rational ideal-coset stability are proved in the original group. For a root-closed actual subgroup K, next-layer exponential membership removes genuine BCH errors and constructs the Q subspace of F_j exponentiating into K. Actual downward induction starts at the terminating original F_c=0 and uses the PROVED W(Gamma_j)=F_j to supply every original group-layer generator. Therefore the FULL original native rational hull is the least positive-root-closed subgroup containing the SAME specified Gamma. Applying this to the genuine arbitrary nilpotent root subgroup proves nativeHull(Gamma)=roots(Gamma), without Gamma normality, finite generation or discreteness assumptions. Every actual hull element has some positive integer power in Gamma; every actual finitely generated subgroup of that hull has one uniform such power. Full root membership plus genuine central denominator clearing NOW PROVE W(Gamma) intersect native center = W(Gamma intersect original group center), and the corresponding actual hull intersection equality. The actual original center projection restricted to W has a constructed Q kernel equivalence with that center-intersection span. Actual rank-nullity gives the rational dimension decomposition; the actual specified center lattice has rational dimension equal to its real dimension. The center-quotient rational DIMENSION INDUCTION STEP is proved, and NOW its recursive hypothesis is discharged by FULL strong induction through the actual strictly lower-dimensional center quotients. The genuine actual quotient group, model and image lattice are used at each step. One final genuine center-quotient step transfers the identity-model induction to ANY arbitrary ORIGINAL model with corners without replacing its chart, group or specified Gamma. Therefore dim_Q W_Gamma = dim_R E is NOW PROVED for every actual discrete cocompact specified lattice. A genuine Q basis of W_Gamma has SAME original columns that form an R basis of the original E; real independence follows from full real spanning and the proved dimension. The NATURAL scalar-extension map R tensor_Q W_Gamma -> E, r tensor w maps to r*w, is NOW PROVED bijective, identified with the actual basis equivalence by equality on genuine tensor basis columns. Actual Q/R coordinates commute, and membership in W_Gamma is exactly rationality of each actual real coordinate. Full positive-root membership shows that this is equivalent to some positive power of Exp(v) lying in the SAME Gamma. Genuine rational-coordinate Hamel components prove real span of an arbitrary Q coordinate subspace creates no new rational vectors; transporting this through the actual compatible bases proves (real span U) intersect W_Gamma = U for EVERY actual Q subspace U contained in W_Gamma. Native rational subspace is defined relative to precisely this original W_Gamma; such real spans are proved rational. Nonabelian Log Gamma is never treated as an additive integer lattice. Remaining: arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; whole original group/real-Lie lower-central equality and layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 979
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 904,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 30,
        "new_selected_report_count": 38, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 8, "new_theorem_count": 30,
                    "new_selected_report_count": 38, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = (
        '\n2026-10-10 round-native-rational-form-dimension: PROGRESS. Eight new modules, thirty proved theorems and eight definitions; thirty-eight exact new reports. All 904 retained baseline source/config hashes and previous terminal log/kernel evidence independently checked; retained proof sources unchanged. FULL actual rational dimension equality is now proved by strong induction through genuine strictly lower-dimensional center quotients with actual image lattices. The final genuine quotient step covers every arbitrary original model with corners, retaining the original group and SAME specified Gamma. Actual Q/R bases have the SAME original columns, with real linear independence proved from real spanning and dimension. The NATURAL map R tensor_Q W_Gamma -> original E, r tensor w maps to r*w, is proved bijective and identified with the actual tensor-basis equivalence. Actual coordinates characterize W_Gamma membership and positive powers in the SAME Gamma. Actual rational-coordinate preimages and compatible basis transport prove real span U intersect W_Gamma = U for every Q subspace U contained in W_Gamma. The corresponding original specified-lattice rational-subspace definition is satisfied; no nonabelian Log Gamma additive-lattice substitution. Arbitrary rational subgroup cocompactness, quantitative bounds, whole group/real-Lie layer equality and closedness, faithful integration/Malcev, Calibration/Alignment, ordered positive witnesses and full target remain. All 894 own and nine attributed PNT+ modules plus root/registry scanned; 912 source/config hashes. All retained standard-axiom sets and twelve empty reports unchanged; no new empty reports. '
        + "Actual full build: " + str(verified["build_jobs"]) + " jobs; "
        "4387 exact unique standard-axiom reports, both actual terminal exit 0. "
        "New sources warning-free and oleans current; original pins and fixed local paper match. "
        "No remote updates. No unavoidable blocker. Review: round-native-rational-form-dimension-review.json.\n\n"
    )
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 894, "pntplus_modules": 9, "scanned_module_count": 903,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4387, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 904, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 30 and review["new_selected_report_count"] == 38
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 987 and manifest["proved_components"][-8:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 903 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4387 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 30, "new_selected_declarations": 38,
        "all_source_modules_scanned": 903, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4387,
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
