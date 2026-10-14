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
PREFIX = "round-noncommuting-power-collection"
OLD = "round-nilpotent-torsion"
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
NEW_AXIOM_FREE = {'Hindman168.lowerCentralCommutatorGenerators'}
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
    assert len(baseline["files"]) == 870 and len(new_modules) == 13
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 865 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 52
    assert sum(c["theorems"] for c in module_counts.values()) == 47
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
    assert len(registered) == len(set(registered)) == len(actual) == 4262
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4210 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 883
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


APPLICATION = ['PROGRESS. Previous proof turn made authoritative progress. The already recorded pre-edit torsion audit was freshly rechecked before the first five new sources; current continuation independently verified all 870 retained source/config hashes and the previous 4210 exact kernel reports and successful terminal log hashes. The old complete audit expects 852 sources and cannot be rerun unchanged after these new sources appear; the new audit checks all 865 sources. No retained proof source, original Lie group, specified lattice, StrongStatement, pins or attributed source changes. No remote updates.', 'CentralCommutatorPowers proves exact natural powers in each variable for the genuine specified central commutator. CentralProductPowers proves (ab)^k = [a,b]^(-choose(k,2)) a^k b^k with the actual group multiplication and proves the exact double-denominator binomial identity. CentralRootMultiplication gives (ab)^(2mn) in the actual Gamma from a^m,b^n in Gamma and an actual central commutator. Gamma normality is not assumed.', 'ClassTwoPositiveRoots proves genuine commutators central from termination of the actual second lower-central layer, or from actual nilpotency class at most two. Thus the actual root set of every specified subgroup is a subgroup in this induction base. The general original group is not replaced by a class-two group.', 'LowerCentralPowerCollection uses the actual original quotients by the actual j+2 lower-central layer. Actual layer j+1 maps to the quotient center; a in layer j gives a central actual commutator in that quotient. It proves the genuine power identity in the quotient and the product power in Gamma joined with the actual remaining layer. This remainder is explicitly retained.', 'CentralCommutatorBilinear constructs real group homomorphisms from the actual specified subgroups by proving central commutator multiplication in each variable. CentralCommutatorGeneration proves the actual commutator of generated subgroups is generated by the actual generator pairs, using genuine subgroup closure and homomorphism inverse images. Finite generator pairs are finite. Adjoining an actual central subgroup creates no new commutators.', 'LowerCentralFiniteGenerators constructs actual iterated generator commutators for an arbitrary original group generated by s. It proves L_j = closure(S_j) joined with L_(j+1) at EVERY j, by actual quotient map/comap equalities and a proved central-image step. Finite original s makes every S_j finite, giving finite generation of actual central factor images. A terminating actual series gives finite generation of each whole L_j; actual finite-generation nilpotent groups satisfy this. No whole-layer finite generation is assumed in the factor induction.', 'LowerCentralGeneratorPowers retains an original a^m in Gamma joined with L_(j+1), decomposes it by the genuine normal remainder layer, and uses the genuine central image of that remainder in G/L_(j+2). The commutator power lands in Gamma joined with L_(j+2), not falsely in Gamma. If every original generator b has b^N in Gamma, every actual iterated generator at layer j has its N^(j+1) power in Gamma joined with L_(j+1).', 'FiniteRelativePowerQuotient concerns H normal INSIDE actual K. If K = closure(s) joined with H for finite s whose elements have positive powers in H, images of the genuine subtype generators generate the entire actual K/(H intersect K), and the previously proved finite nilpotent torsion-generator theorem gives finiteness. Actual quotient exponent then sends all of K into the SAME actual H with one positive natural power. There is no added finite quotient or exponent assumption.', 'LowerCentralRelativeNormal proves L_j maps centrally in the actual G/L_(j+1) for all j including zero. Genuine map and commutator equalities prove [Gamma joined with L_j, Gamma joined with L_j] lies in Gamma joined with L_(j+1). It proves the next actual join normal inside its predecessor. This DOES NOT assert Gamma normal in G.', 'NilpotentPowerGenerators applies those proved relative normal quotients to the actual finite generator commutators and their proved powers. Actual finite quotient exponents are composed down the entire terminating original lower-central series. For a finite generating set with one common positive power in arbitrary Gamma, one positive natural power of EVERY original group element lands in Gamma itself. No remainder is left, no dimension or nilpotency-class restriction is added, and no explicit quantitative exponent is claimed.', 'NilpotentArbitraryPositiveRoots restricts to the actual subgroup generated by a and b, retains the actual Gamma intersection with that subgroup and derives a common positive generator power from the original witnesses m,n. The proved whole-series uniform result proves actual noncommuting positive-root multiplication for ANY original nilpotent group and ANY specified subgroup. The root set is a genuine subgroup, root-closed, least among root-closed containing subgroups and idempotent. Finite root sets have a common positive power in any group; applying this to the actual generators of K proves a uniform positive power on every actual finitely generated K contained in roots(Gamma), without assuming Gamma normal.', 'The new general nonnormal root subgroup is a necessary algebraic input for the original specified lattice. Roots(Gamma) were already proved contained in the native rational exponential hull, but the reverse inclusion is still missing. The equality W(Gamma) intersect V = W(Gamma intersect center), full original scalar-extension/rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, Malcev and full Calibration/Alignment/positive ordered witnesses remain unproved. StrongConjecture and the full prize target remain unproved. Full proof/audit precede publication/submission. No unavoidable blocker.', 'Thirteen new modules, forty-seven proved theorems and five definitions give fifty-two new exact reports. The actual full build and kernel check cover all 865 own and nine attributed PNT+ sources plus root/registry. New current oleans, retained standard-axiom sets, exact empty-report sets, all-source trust scan, fixed local paper/pins and source/config hashes are checked. No new option overrides, declared axioms, native_decide, proof placeholders or dependency edits.']

COMPONENTS = ['actual central commutator multiplication in both variables yields group homomorphisms on the specified original subgroups', 'actual central commutators of generated subgroups are generated by actual generator pairs, with finite pair sets and invariance under adjoining central subgroups', 'actual central commutator natural powers in either and both variables are exact without a specified-subgroup normality assumption', 'actual product power collection with the inverse central binomial correction and the double-denominator coefficient identity', 'actual subgroup power membership of a product at degree twice the denominator product when the genuine commutator is central', 'actual class-two terminating lower-central base gives a positive-root subgroup for every original specified nonnormal subgroup', 'actual finite relative nilpotent power-generator quotients and their uniform positive exponents, with proved generation of the whole genuine quotient', 'actual iterated finite commutator generators generate every original lower-central factor modulo its next layer, and whole terminating layers are finitely generated', 'actual common positive generator powers propagate through each iterated commutator generator modulo the next original layer', 'actual successive lower-central quotient power collection retaining Gamma joined with the original remainder layer', 'actual next Gamma/lower-central join is normal inside the preceding actual join, without assuming Gamma normal in the original group', 'actual arbitrary-subgroup positive roots in any original nilpotent group are closed under noncommuting multiplication, root-closed and idempotent, with uniform positive powers on every finitely generated subgroup inside them', 'actual finite relative quotient exponents composed down the entire terminating original lower-central series give one positive power sending every original group element into the same arbitrary specified subgroup']

NEW_PROGRESS = 'Retained original native Exp/Log diffeomorphism, rational finite BCH/Picard construction, W bracket closure, full real log span and actual specified lattice Gamma finite generation remain proved. The actual center lattice has discrete full integer/rational/real log spans and compact additive quotient; its rational exponential hull is exactly the actual central positive roots of Gamma. The original center quotient has a constructed genuine smooth Hausdorff simply connected LieGroup, discrete cocompact image lattice and strictly lower real model dimension. Its actual differential is pi with kernel V; pi preserves genuine brackets and intertwines actual native Exp/Log, mapping original W=span_Q Log Gamma exactly onto the actual projected subgroup rational log span. Generic genuine center-quotient induction proves finite-order generators in any nilpotent group generate a finite subgroup. NOW actual central commutator collection, actual iterated finite lower-central generator sets and their power propagation, proved relative normality of consecutive Gamma/lower-central joins, actual finite relative torsion-generator quotients and their actual exponents eliminate ALL actual lower-central remainders. Any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one uniform positive power sending every original element into the SAME Gamma. The actual two-generator subgroup therefore gives general noncommuting multiplication closure of roots(Gamma) without assuming Gamma normal. Actual positive roots form the least root-closed containing subgroup and are idempotent; every actual finitely generated subgroup of those roots has a uniform positive power in Gamma. General nonnormal root multiplication is proved. Remaining: full native rational hull-to-Gamma positive powers (the reverse of the already proved root-to-hull inclusion); identify W(Gamma) intersect V with the actual specified center rational log span; finish full original ambient scalar-extension injectivity and specified-lattice rational-form induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse group/Lie lower-central comparison and algebraic layer closedness; faithful integration/Malcev. Full Calibration/Alignment, ordered positive arithmetic witnesses, StrongConjecture and the full prize target remain unproved. Publication and submission await full proof/audit. No unavoidable blocker.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 945
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 870,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 47,
        "new_selected_report_count": 52, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 13, "new_theorem_count": 47,
                    "new_selected_report_count": 52, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = (
        "\n2026-10-10 round-noncommuting-power-collection: PROGRESS. "
        "Thirteen new modules, forty-seven proved theorems and five definitions; fifty-two exact new reports. "
        "All 870 retained baseline hashes verified before registration; only retained root/registry change. "
        "Genuine central commutator powers and product collection give a nonnormal class-two base. "
        "Actual finite generator commutators generate every successive lower-central factor modulo the next original layer. "
        "Finite generation of actual terminating nilpotent layers is proved. "
        "Generator power conditions propagate to actual commutator generators modulo their next layer. "
        "Gamma joined with each next lower-central layer is proved normal INSIDE the preceding join; Gamma itself remains arbitrary. "
        "Finite torsion generator images generate each actual relative quotient, proving it finite. "
        "Their actual finite quotient exponents are composed along the entire terminating series. "
        "Thus any nilpotent group generated by a finite set with common positive powers in arbitrary Gamma has one positive power "
        "sending every element to the SAME original Gamma. "
        "Application to the actual two-generator subgroup proves general noncommuting positive-root multiplication, "
        "a genuine root-closed least subgroup and idempotence, and a uniform denominator on any actual finitely generated subgroup of those roots. "
        "General nonnormal root multiplication is NOW proved. Full rational hull-to-Gamma powers and W-center kernel equality are NOT proved. "
        "Full rational-form induction, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, "
        "Malcev, Calibration/Alignment, ordered positive witnesses and the full target remain unproved. "
        "All retained axiom sets and eleven retained empty reports unchanged; new empty reports exactly: "
        + repr(sorted(NEW_AXIOM_FREE)) + ". "
        "All 865 own and nine attributed PNT+ modules plus root/registry scanned; 883 source/config hashes. "
        "Actual full build and exact kernel totals: " + str(verified["build_jobs"]) +
        " jobs, 4262 exact unique allowed-standard-axiom reports, both terminal exit 0. "
        "New sources warning-free and oleans current. Actual pins and fixed local paper match; no remote updates. "
        "No unavoidable blocker. Review: round-noncommuting-power-collection-review.json.\n\n"
    )
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 865, "pntplus_modules": 9, "scanned_module_count": 874,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4262, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 870, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 47 and review["new_selected_report_count"] == 52
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 958 and manifest["proved_components"][-13:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 13
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
    assert scan["scanned_module_count"] == 874 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4262 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 47, "new_selected_declarations": 52,
        "all_source_modules_scanned": 874, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4262,
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
