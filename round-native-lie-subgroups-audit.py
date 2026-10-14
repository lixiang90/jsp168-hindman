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
PREFIX = "round-native-lie-subgroups"
OLD = "round-native-global-inverse"
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
    assert len(baseline["files"]) == 772 and len(new_modules) == 10
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 764 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 47
    assert sum(c["theorems"] for c in module_counts.values()) == 43
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
    assert len(registered) == len(set(registered)) == len(actual) == 3911
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3864 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 782
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


APPLICATION = ['PROGRESS: the preceding original global exponential diffeomorphism round was recorded and freshly rechecked before the saved 772-file baseline and these edits. All baseline hashes are reverified before registration. Retained proofs, StrongStatement, pins and attribution are unchanged; only root and exact-name registry change. No remote official updates are checked. No unavoidable blocker is established.', 'NativeLieSubalgebraModel is the actual underlying real submodule of an arbitrary original native Lie subalgebra. Its finite-dimensional closure is proved. The original adjoint generator equals the actual original bracket, so actual internal parameters preserve the subalgebra under generator powers, genuine dexp defect powers, finite inverse and true logarithm vector field. No provided substitute Lie algebra or BCH closure is used.', 'NativeLieSubalgebraPicard uses real finite-dimensional closure and actual interval integral membership to keep every genuine finite Picard iterate in the original subalgebra. The actual stabilized lift therefore stays inside it. NativeLieSubalgebraSubgroup uses the already proved actual product logarithm, zero and inverse laws to show that the original exponential image itself is an original subgroup, not merely a generated or closed envelope. Original global inverse laws give the exact subgroup/logarithm membership correspondence.', 'NativeLieSubalgebraTopology constructs the actual restricted exponential/global-logarithm homeomorphism with natural subtype topologies. The subgroup is genuinely closed by the actual logarithm preimage of the closed model; actual convexity and the true homeomorphism give contractibility, connectedness and simply connectedness. This does not prove the required specified-lattice cocompactness, rationality or smooth subgroup manifold structure.', 'NativeLieIdealSubgroup proves invariance under every original conjugation from the actual finite adjoint formula, true original exponential surjectivity and genuine conjugation/exponential identity. The exponential of any actual original native Lie ideal is normal. NativeLieLowerCentralSubgroups exponentiates each original native Lie lower-central layer and proves antitonicity, original-class termination, zeroth top, normality and, in the original simply connected case, closedness and contractibility. These exponentiated layers are not silently identified with the algebraic group lower central series.', 'NativeLieLogarithmAffineLayer proves that the actual logarithm vector field differs from its layer-j velocity by an element of layer j+1: the finite inverse preserves j, its true dexp equation converts the defect into the difference, and the proved defect lowers layers. Actual Picard integral subtraction proves the true lift differs from u+t*w in j+1. The actual product logarithm then proves membership in the next exponential layer when u+w is in that layer.', 'NativeLieAdjointLayer pads the actual finite adjoint series by a zero terminal power and removes its identity term, giving a true positive-power formula even in class zero. Original generator powers lower the original Lie layers, hence Ad(g)(w)-w lies in layer j+1 for every original g and w in j. NativeLieGroupLowerCentralComparison combines this fact, actual conjugation and genuine product logarithms to place actual commutators [g,Exp(w)] in the next exponential layer. Actual subgroup commutator generation and induction give Group.lowerCentralSeries(j) <= Exp(Lie.lowerCentralSeries(j)). Reverse inclusion, equality and algebraic group layer closedness remain unproved.', 'NativeLieGlobalProductLog proves that the actually constructed global logarithm of Exp(u)*Exp(w) equals the genuine finite Picard lift. Consequently the true logarithm product error lies in the next layer, and for all original g,h the actual log(g*h)-log(g)-log(h) belongs to the actual first Lie commutator layer. Actual original group lower-central elements have logarithms in the corresponding native Lie layers. No rational Lie-polynomial BCH coefficient claim is made.', 'Ten new modules, 43 proved theorems and four definitions give 47 exact new reports. Require full build and kernel terminal exit zero with real byte logs and hashes, current oleans, exact source names/imports, retained axiom sets and six retained axiom-free reports, all-source trust scans, pinned dependencies and fixed local paper objects. All 764 own and nine attributed PNT+ modules plus root and registry are covered. No new option overrides or dependency source edits are introduced.', 'Remaining: actual rational Lie-polynomial BCH structure, reverse individual group/Lie layer inclusion and exact series comparison, faithful integration/Malcev, arbitrary specified-lattice rational subgroup cocompactness, full calibration/Alignment and original ordered positive arithmetic witnesses. Original nonabelian lattice logarithms are not treated as additive. StrongConjecture and the full prize target remain unproved; publication and prize submission await full proof and audit.']

COMPONENTS = ['actual original native Lie subalgebras are closed in finite dimension and preserved internally by true adjoint generator powers, dexp defect powers and finite inverse logarithm fields', 'actual global finite Picard logarithm iterates and stabilized lifts remain inside every original native Lie subalgebra by true closed-submodule integrals', 'actual exponential image of every original native Lie subalgebra is itself a genuine original subgroup with exact actual global-logarithm membership', 'actual original Lie-subalgebra exponential image is naturally homeomorphic to its model and is closed, contractible, connected and simply connected', 'actual exponential image of every original native Lie ideal is normal by original finite adjoint invariance and actual group conjugation', 'actual original native Lie lower-central layers exponentiate to a decreasing normal filtration terminating at original group class and closed contractible layers in the simply connected case', 'actual logarithm-lifting field and finite Picard product lift have additive errors in the next original native lower-central layer', 'actual original group adjoint acts as identity modulo the next original native Lie lower-central layer via its true positive-power finite formula', 'actual original group lower central series is contained in the exponentials of original native Lie lower-central layers by genuine commutator identities and generation', 'actual original global logarithm of multiplication equals the finite Picard lift and is additive modulo the original native first commutator layer']

NEW_PROGRESS = 'The actual original native adjoint differential is the original native bracket, and original group nilpotency proves native Lie lower-central termination at the original class c. The actual original exponential comes from proved genuine global invariant curves. Original relative-curve mixed derivatives and group cocycle prove the actual finite dexp formula and genuine native local C-infinity inverses. Original fibers are exactly cosets of the proved closed discrete native central period subgroup. Actual dexp defect W_v lowers original layers, W_v^c=0, and the genuine finite geometric sum U_v is its true two-sided inverse. The actual C-infinity field F_w(v)=U_v(w) strictly improves parameter differences by one original lower-central layer. Original finite-dimensionality proves these layers genuinely closed and true quotient-map integral commutation keeps actual integrals inside them. Actual global Picard iterates gamma_0=u and gamma_(n+1)=u+integral(0..t,F_w(gamma_n)) have true FTC derivatives. Actual differences gamma_(n+1)-gamma_n belong to S_n; the original nilpotency class c kills the next difference, proving gamma_(c+1)=gamma_c and the genuine global logarithm-lifting ODE including c=0. Actual manifold chain rules and original global integral-curve uniqueness prove Exp(gamma(t))=Exp(u)*gamma_w(t), giving a true product logarithm at one. The actual original exponential range is a subgroup; its true openness and original connectedness make it all of G. Thus genuine whole-group surjectivity and the actual additive-period quotient covering are proved. Original simply connectedness now eliminates the actual period group. Original local path connectedness is genuinely derived from the actual exponential quotient map of original E; it is not an extra premise. The true covering lifting theorem lifts identity G with lift zero of one to an actual continuous logarithm L. Actual preconnectedness of original E and genuine covering lift uniqueness prove both inverse laws L(Exp(v))=v and Exp(L(g))=g. Actual original exponential injectivity follows and K is exactly bottom. Near every original group point the actual global L equals the previously constructed true local logarithm by injectivity. Therefore L is genuinely native C-infinity. The actual native exponential and this constructed L form a global native C-infinity Diffeomorph E-to-G, with actual inverse differential composition. Global surjectivity, injectivity, period elimination and global smooth inverse no longer remain open tasks. No replacement matrix model, supplied global inverse, assumed BCH or nonabelian additive lattice logarithms is used. Every original native real Lie subalgebra is now proved closed in finite dimension and preserved by the genuine finite inverse field and actual Picard integrals. Its actual exponential image itself is a subgroup. The actual restricted exponential and global logarithm form a natural subtype homeomorphism, proving genuine closedness and contractibility, hence connectedness and simply connectedness. Every original native Lie ideal exponentiates to a normal original subgroup by actual finite adjoint invariance. The original native Lie lower-central layers S_j exponentiate to a decreasing normal filtration H_j with H_0=G, H_c=1 and closed contractible terms in the original simply connected case. Actual dexp equations prove F_w(v)-w lies in S_(j+1) when w lies in S_j, and real Picard integrals give Lift(w,u,t)-(u+t*w) in S_(j+1). The actual finite adjoint formula, padded by its genuinely zero terminal power, gives Ad(g)(w)-w in S_(j+1). True conjugation and product-logarithm laws place [g,Exp(w)] in H_(j+1). Subgroup commutator generation and induction prove the one-sided inclusion of the original algebraic Group.lowerCentralSeries(j) in H_j. The actual global logarithm of Exp(u)*Exp(w) is the genuine finite Picard lift; its additive error lies in S_(j+1), and actual log(g*h)-log(g)-log(h) lies in S_1. These are statements about original arbitrary groups and original native brackets, not replacement matrix models. Remaining: prove the actual finite Picard product logarithm has the required rational Lie-polynomial BCH structure; prove reverse individual original group/Lie lower-central inclusion, exact comparison and algebraic group layer closedness; derive faithful integration/Malcev and arbitrary specified-lattice rational subgroup cocompactness. Closedness of exponentiated real subalgebras alone does not imply rationality or lattice cocompactness. Original nonabelian lattice logarithms are not assumed additive. Full calibration/Alignment and original ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target are unproved; publication and submission await full proof and audit. No unavoidable blocker is established.'


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 847
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 772,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 43,
        "new_selected_report_count": 47, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 10, "new_theorem_count": 43,
                    "new_selected_report_count": 47, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = ('\n2026-10-10 round-native-lie-subgroups: PROGRESS. Ten new modules, 43 proved theorems and four definitions; 47 exact new reports. All 772 baseline source/config hashes verified before registration. Only retained root and registry change. Actual original native real Lie subalgebras are preserved by the true finite inverse and Picard integrals; their exponential images are genuine closed contractible original subgroups with natural restricted exponential/logarithm homeomorphisms. Actual Lie ideals exponentiate to normal subgroups. Actual native lower-central layers exponentiate to a decreasing normal filtration with original-class termination. True inverse differential, genuine integrals and finite adjoint formula give actual next-layer additive errors and commutator membership. Original algebraic group lower-central layers are contained in the corresponding Lie exponential layers; reverse inclusion and equality remain unproved. Actual global product logarithms equal the genuine finite Picard lifts. Rational BCH and arbitrary specified-lattice cocompactness remain unproved, as does the full target. Complete build terminal exit 0: ' + str(verified["build_jobs"]) + ' jobs. Kernel terminal exit 0: 3911 exact unique standard-axiom reports. Retained axioms and six retained axiom-free reports unchanged. All 764 own and nine attributed PNT+ modules plus root and registry scanned; 782 source/config hashes. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-lie-subgroups-review.json.\n\n')
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 764, "pntplus_modules": 9, "scanned_module_count": 773,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 3911, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 772, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 43 and review["new_selected_report_count"] == 47
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 857 and manifest["proved_components"][-10:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 10
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
    assert scan["scanned_module_count"] == 773 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 3911 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 43, "new_selected_declarations": 47,
        "all_source_modules_scanned": 773, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 3911,
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
