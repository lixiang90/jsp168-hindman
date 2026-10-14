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
PREFIX = "round-native-lattice-rational"
OLD = "round-native-rational-picard"
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
    assert len(baseline["files"]) == 793 and len(new_modules) == 11
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 786 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 41
    assert sum(c["theorems"] for c in module_counts.values()) == 36
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
    assert len(registered) == len(set(registered)) == len(actual) == 4010
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 3969 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 804
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


APPLICATION = ['PROGRESS: the preceding rational Picard round was recorded and freshly rechecked before the saved 793-file baseline and these edits. All 793 baseline hashes are independently reverified before registration. Only the root and exact-name registry change among retained sources; retained proofs, StrongStatement, dependency pins and attributed sources remain unchanged. No remote updates are checked and no unavoidable blocker is established.', 'RationalVectorPolynomialCoefficients proves exact uniqueness of finite Q-vector polynomial coefficients from their values at all natural numbers, using actual algebraic duals and scalar polynomial uniqueness. The actual Q-module quotient of an arbitrary rational subspace extracts coefficient membership from natural-time membership. Real natural monomials are converted to genuine rational scalars by scalar compatibility. No rational-subspace closedness, norm or finite rational dimension is assumed.', 'NativeLieAdjointNatPolynomial rewrites the genuine original adjoint curve applied to an original vector as a finite polynomial with rational reciprocal-factorial coefficients. The actual original group nilpotency class makes its terminal and next powers zero, so two genuinely zero terms pad the formula and permit extraction of the linear coefficient even at class zero or one. Natural-time curve membership therefore implies membership of the actual original adjoint generator applied to that vector.', 'NativeSubgroupLogarithmSpan defines W as span_Q of the actual original global logarithms of the arbitrary specified original subgroup Gamma. The original exponential conjugation identity and actual two-sided logarithm inverse laws give Ad(g)(Log(h))=Log(g*h*g^-1). Original subgroup closure and actual Q-linear span induction prove Ad(g) preserves W for every g in Gamma. Log(Gamma) itself is not asserted additive.', 'NativeSubgroupBracketSpan uses the actual natural-time equality exp(n*Log(g))=g^n for g in Gamma. Thus all natural-time original adjoint values of Log(h) belong to W, and coefficient extraction gives B_Log(g)(Log(h)) in W. Actual bilinearity in both arguments extends this to all of W. The retained original adjoint-differential/native-bracket identity proves actual native bracket closure of W without a supplied rational structure or bracket-closure premise. The retained genuine rational Picard/BCH theorem gives closure under the actual noncommuting product logarithm.', "NativeSubgroupRationalHull exponentiates this derived bracket-closed W into a genuine original subgroup, gives exact original global-logarithm membership and proves it contains Gamma. Actual span minimality proves containment in every exponential rational Lie structure containing Gamma's actual logarithms. Every hull element's actual adjoint preserves W by the true finite original factorial formula. No claim is made that this hull is closed, discrete or cocompact.", 'RationalBilinearRealSpan proves actual real bilinear preservation of the real span of an actual preserved Q-subspace by two genuine linear-span arguments. NativeSubgroupRealLieSpan therefore constructs an actual original native real Lie subalgebra S from W. Its underlying original real model equals span_R(Log(Gamma)), not a different generated algebra. The true original exponential subgroup contains Gamma and is closed and contractible by the retained finite-dimensional exponential/logarithm homeomorphism.', 'NilpotentLieSubalgebraSpanning proves explicitly that S plus the actual commutator layer equals the whole Lie algebra only when S itself equals the whole algebra. The proof decomposes actual original vectors into S and a lower-central layer, expands actual brackets, and descends through the true terminating lower-central series. No maximal-subalgebra or Malcev conclusion is assumed.', 'NativeLieLogarithmCharacter constructs an actual continuous real function f(Log(g)) from an original real linear functional. Its actual additive character law follows from the true original product-logarithm error in the native commutator layer. Nonzero functionals yield surjective actual characters via the genuine original exponential/logarithm inverse. NativeLieCharacterCompactQuotient descends this actual function to the original coset quotient G/Gamma using original left-coset relations, without requiring Gamma normal. Compactness of that actual quotient and noncompactness of R force the functional to vanish.', "NativeLatticeRealSpanning applies actual real algebraic dual separation to a hypothetical proper original native Lie subalgebra containing all Log(Gamma). Its sum with the actual commutator layer is proper by the proved nilpotent spanning lemma. The separating nonzero functional gives a continuous surjective real character on the actual compact original quotient, a contradiction. Therefore every actual cocompact subgroup's logarithms span the entire original real model, and the actual W=span_Q(Log(Gamma)) has full real span. CompactSpace(G/Gamma) is the original specified quotient compactness premise, not a newly assumed compactness conclusion. Gamma discreteness is not needed for this real-spanning theorem.", 'Eleven new modules, 36 theorems and five definitions give 41 exact new reports. Require actual terminal exit-zero complete build/kernel records, byte logs and hashes, exact names/imports, current oleans and all-source trust scans. All 786 own and nine attributed PNT+ modules plus root and registry are covered. All seven retained axiom-free reports and retained axiom sets remain unchanged; actual new reports must use only standard allowed axioms. No option overrides are introduced.', 'Remaining: prove finite Q dimension and the full rational form of the actual specified discrete cocompact lattice, quantitative degree/denominator bounds, reverse original group/Lie lower-central inclusion and exact comparison/closedness, faithful integration/Malcev, and actual specified-lattice rational subgroup cocompactness. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await complete proof and audit.']

COMPONENTS = ['actual finite Q-vector polynomial coefficients are uniquely determined by all natural-time values and quotient coefficient membership needs no rational-subspace closedness', 'actual original adjoint curve rational factorial polynomial and genuine zero padding recover generator membership from natural-time membership for every original nilpotency class', 'actual Q-linear span of logarithms of an arbitrary specified original subgroup is invariant under its genuine original adjoint action by actual conjugation and global inverse laws', 'actual Q-linear span of logarithms of an arbitrary specified original subgroup is closed under the original native Lie bracket by integer conjugations and coefficient extraction', 'actual specified-subgroup logarithmic Q-span preserves genuine original noncommuting product logarithms by the proved rational Picard BCH construction', 'actual specified-subgroup rational exponential hull is a genuine original subgroup with exact logarithm membership, contains the specified subgroup, is minimal among containing rational Lie structures and preserves the actual Q-span under adjoint action', 'actual real span of a bilinear-preserved rational subspace is bilinear-preserved without topological closure assumptions', 'actual real span of specified-subgroup logarithms is an original native Lie subalgebra whose genuine exponential subgroup is closed, contractible and contains the original subgroup', 'actual nilpotent Lie subalgebra spanning the original abelianization equals the whole algebra by explicit terminating lower-central descent', 'actual original real logarithmic characters killing the native commutator layer are continuous, additive and surjective when nonzero and descend to original nonnormal coset quotients', 'actual cocompact original subgroup logarithms span the entire original real Lie model by genuine quotient compactness, native nilpotent spanning and real dual separation']

NEW_PROGRESS = "The actual original native adjoint differential is the original native bracket, and original group nilpotency proves native Lie lower-central termination at the original class c. The actual original exponential comes from proved genuine global invariant curves. Original relative-curve mixed derivatives and group cocycle prove the actual finite dexp formula and genuine native local C-infinity inverses. Original fibers are exactly cosets of the proved closed discrete native central period subgroup. Actual dexp defect W_v lowers original layers, W_v^c=0, and the genuine finite geometric sum U_v is its true two-sided inverse. The actual C-infinity field F_w(v)=U_v(w) strictly improves parameter differences by one original lower-central layer. Original finite-dimensionality proves these layers genuinely closed and true quotient-map integral commutation keeps actual integrals inside them. Actual global Picard iterates gamma_0=u and gamma_(n+1)=u+integral(0..t,F_w(gamma_n)) have true FTC derivatives. Actual differences gamma_(n+1)-gamma_n belong to S_n; the original nilpotency class c kills the next difference, proving gamma_(c+1)=gamma_c and the genuine global logarithm-lifting ODE including c=0. Actual manifold chain rules and original global integral-curve uniqueness prove Exp(gamma(t))=Exp(u)*gamma_w(t), giving a true product logarithm at one. The actual original exponential range is a subgroup; its true openness and original connectedness make it all of G. Thus genuine whole-group surjectivity and the actual additive-period quotient covering are proved. Original simply connectedness now eliminates the actual period group. Original local path connectedness is genuinely derived from the actual exponential quotient map of original E; it is not an extra premise. The true covering lifting theorem lifts identity G with lift zero of one to an actual continuous logarithm L. Actual preconnectedness of original E and genuine covering lift uniqueness prove both inverse laws L(Exp(v))=v and Exp(L(g))=g. Actual original exponential injectivity follows and K is exactly bottom. Near every original group point the actual global L equals the previously constructed true local logarithm by injectivity. Therefore L is genuinely native C-infinity. The actual native exponential and this constructed L form a global native C-infinity Diffeomorph E-to-G, with actual inverse differential composition. Global surjectivity, injectivity, period elimination and global smooth inverse no longer remain open tasks. No replacement matrix model, supplied global inverse, assumed BCH or nonabelian additive lattice logarithms is used. Every original native real Lie subalgebra is now proved closed in finite dimension and preserved by the genuine finite inverse field and actual Picard integrals. Its actual exponential image itself is a subgroup. The actual restricted exponential and global logarithm form a natural subtype homeomorphism, proving genuine closedness and contractibility, hence connectedness and simply connectedness. Every original native Lie ideal exponentiates to a normal original subgroup by actual finite adjoint invariance. The original native Lie lower-central layers S_j exponentiate to a decreasing normal filtration H_j with H_0=G, H_c=1 and closed contractible terms in the original simply connected case. Actual dexp equations prove F_w(v)-w lies in S_(j+1) when w lies in S_j, and real Picard integrals give Lift(w,u,t)-(u+t*w) in S_(j+1). The actual finite adjoint formula, padded by its genuinely zero terminal power, gives Ad(g)(w)-w in S_(j+1). True conjugation and product-logarithm laws place [g,Exp(w)] in H_(j+1). Subgroup commutator generation and induction prove the one-sided inclusion of the original algebraic Group.lowerCentralSeries(j) in H_j. The actual global logarithm of Exp(u)*Exp(w) is the genuine finite Picard lift; its additive error lies in S_(j+1), and actual log(g*h)-log(g)-log(h) lies in S_1. These are statements about original arbitrary groups and original native brackets, not replacement matrix models. The genuine finite Picard product logarithm now has an explicit finite recursive rational original-bracket polynomial representation. Actual finite coefficient lists evaluate as real vector polynomials; pairwise original bilinear expansion and rational scaling preserve exact evaluations. The actual Bochner primitive of a monomial is given by division by its positive new degree in Q. Thus rational-time membership is proved by exact arithmetic, without treating an arbitrary Q-linear subspace as topologically closed. Actual original dexp defect powers and the actual finite geometric inverse field have explicit rational polynomial lists, using the actual adjoint differential already identified with the original native bracket. The actual Picard integral iterates exactly equal the real evaluations of their recursively constructed finite coefficient lists. Their coefficients stay in every original bracket-closed Q-linear structure V containing u,w; all true Picard iterates and the stabilized lift belong to V at rational times. The actual global logarithm of Exp(u)*Exp(w) therefore belongs to V, and Exp(V) itself is a genuine subgroup with exact actual logarithm membership. Actual original finite factorial adjoint formulas prove that conjugation by group elements with logarithms in V preserves V. An explicit finite polynomial list represents the actual original global logarithm of Exp(u)*Exp(t*w) for every real t, with the genuine product logarithm at one. All operations use original vectors, original brackets and rational scalars, not replacement matrices or supplied BCH laws. The arbitrary specified original subgroup Gamma now supplies a derived rational Lie structure W=span_Q(Log(Gamma)). Actual original conjugation proves its adjoint invariance under Gamma. Genuine natural-time adjoint values are conjugations by Gamma powers; algebraic rational vector polynomial coefficient extraction, with true nilpotent zero padding at all classes, recovers actual original generator membership. Actual bilinearity and the proved native bracket identity establish bracket closure of W without supplying it. The actual rational BCH result therefore preserves W and Exp(W) is a genuine rational hull subgroup containing Gamma, with exact original logarithm membership and rational Lie minimality. Every hull element's actual adjoint preserves W. Actual real linear span induction proves span_R(W)=span_R(Log(Gamma)) is an original native Lie subalgebra; its genuine original exponential subgroup contains Gamma and is closed and contractible. Explicit terminating lower-central descent proves that a proper nilpotent Lie subalgebra remains proper after adding the actual commutator layer. Real dual separation gives an actual nonzero linear functional vanishing on that sum. Actual product-logarithm errors prove its original continuous logarithmic character law, and genuine original exponential/logarithm inverses give surjectivity to R. This actual character descends to the original possibly nonnormal coset quotient. If the original specified quotient G/Gamma is compact, noncompactness of R contradicts surjectivity. Thus the actual specified cocompact subgroup's logarithms have full real span. No replacement group, supplied bracket closure, assumed character, rational-subspace closedness or additive nonabelian Log(Gamma) is used. Remaining: finite Q dimension and the full rational form of the actual specified discrete cocompact lattice; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev and actual specified-lattice rational subgroup cocompactness. The actual real spanning conclusion does not by itself prove finite Q dimension, discreteness or rational subgroup cocompactness. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker is established."


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 868
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 793,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 36,
        "new_selected_report_count": 41, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 11, "new_theorem_count": 36,
                    "new_selected_report_count": 41, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-native-lattice-rational: PROGRESS. Eleven new modules, 36 proved theorems and five definitions; 41 exact new reports. All 793 baseline hashes verified before registration; only retained root and registry change. Actual natural-time original adjoint values from specified subgroup powers and genuine rational polynomial coefficient extraction prove native bracket closure of W=span_Q(Log(Gamma)). Actual rational BCH gives its genuine exponential hull subgroup. Its real span is an original native Lie subalgebra with a closed contractible genuine exponential subgroup containing Gamma. Explicit nilpotent lower-central descent, real dual separation and actual continuous characters on the original compact coset quotient prove span_R(Log(Gamma))=E. Finite Q dimension, full specified-lattice rational form/cocompactness, quantitative bounds, reverse original group/Lie layer comparison, Malcev and full target remain unproved. Retained axiom sets and seven retained axiom-free reports remain unchanged. All 786 own and nine attributed PNT+ modules plus root and registry scanned; 804 source/config hashes. Actual complete build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4010 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and pins match; no remote updates. No unavoidable blocker. Review: round-native-lattice-rational-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 786, "pntplus_modules": 9, "scanned_module_count": 795,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4010, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 793, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 36 and review["new_selected_report_count"] == 41
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 879 and manifest["proved_components"][-11:] == COMPONENTS
    assert manifest["last_round"]["new_module_count"] == len(registration["new_modules"]) == 11
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
    assert scan["scanned_module_count"] == 795 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4010 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 36, "new_selected_declarations": 41,
        "all_source_modules_scanned": 795, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4010,
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
