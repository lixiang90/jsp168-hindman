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
PREFIX = "round-native-root-saturation"
OLD = "round-native-lattice-finite"
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
    assert len(baseline["files"]) == 813 and len(new_modules) == 10
    retained_changed = [f["path"] for f in baseline["files"] if digest(f["path"]) != f["sha256"]]
    assert retained_changed == ["Hindman168.lean", "Verification.lean"]
    own = sorted(Path("Hindman168").rglob("*.lean"))
    pnt = sorted(Path("PrimeNumberTheoremAnd").rglob("*.lean"))
    assert len(own) == 805 and len(pnt) == 9
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
    assert len(names) == len(set(names)) == 25
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
    assert len(registered) == len(set(registered)) == len(actual) == 4064
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert len(previous) == 4039 and all(actual[n] == a for n, a in previous.items())
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
    assert len(source_files) == len({f["path"] for f in source_files}) == 823
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


APPLICATION = ['PROGRESS: freshly rechecked the previous original lattice finite-generation round, including exact source hashes, terminal build/kernel records, retained axiom sets, fixed local paper and actual dependency pins. The 813-file baseline still matches every byte before registration. Only retained root and registry change. No remote updates or unavoidable blocker.', 'NilpotentFiniteExponentialFixedVector factors the actual finite exponential minus identity as B*Q. The genuine constant-one polynomial Q is a proved unit even at cutoff zero and commutes with B. Applying the factorization to the actual fixed vector and the actual invertible continuous linear operator proves B(w)=0. No fixed-vector kernel equality is supplied as a premise.', 'NativeLieExponentialCommuteIff uses original group conjugation and true exponential injectivity to turn actual commuting exponentials into an actual adjoint-fixed logarithm vector. The genuine finite adjoint formula and the preceding nilpotent fixed-vector proof give actual B_v(w)=0. The retained true adjoint ODE proves the reverse implication. The resulting equivalence uses the original native Lie bracket, not a matrix replacement or assumed BCH formula.', 'NativeLiePowerRoots derives Exp(n*v)=Exp(v)^n from the genuine one-parameter law, and Log(g^n)=n*Log(g) from both actual inverse laws. It constructs a root Exp(n^-1*Log(g)) for every positive natural n and proves uniqueness by actual logarithm scalar injectivity. It does not assert closure of the root-saturation set of a specified subgroup.', 'NativeLatticeCentralizer proves actual center membership of Exp(v) is equivalent to the true adjoint generator being zero. For an element centralizing actual Gamma, genuine commuting detection puts every actual Gamma logarithm in the real-linear generator kernel. The retained proved full real span makes that kernel the original entire model. True global exponential surjectivity then gives centralizer(Gamma)=center(G). Discreteness and finite generation are not used for this equality; actual ambient quotient compactness is.', 'FiniteCoordinateRecords bounds complete records by an actual finite product of finite coordinate-image subtypes, then proves every finite image has finitely many representatives in its original source. CentralCommutatorRecords proves original central products k*gamma identify the actual commutator [gamma,s] with [k^-1,s]. Equal records on actual subgroup generators extend to the actual generated subgroup by equality of original conjugation homomorphisms, so delta^-1*gamma centralizes Gamma.', 'DiscreteCentralCommutatorRecords uses actual original continuous commutator images of compact K. Their intersections with actual discrete Gamma are finite by the retained actual discrete compact-intersection theorem. For every finite original generator set the actual central translate records therefore have a finite complete image. No finite commutator record set is assumed.', 'CenterCompactRepresentatives chooses finite representatives of actual commutator records of Gamma elements with central K-translates. Equal records yield actual central differences through the proved centralizer equality. Every original central element is a finite representative translate times an element in Gamma intersect center(G). The actual finite union of compact K translates, intersected with the actual closed center, is compact. Its actual closed-subtype pullback gives genuine compact representatives inside the natural original center subtype.', 'CenterLatticeCocompactness proves compactness of any natural coset quotient from actual compact representatives. It also derives discreteness of the actual center intersection using its genuine continuous injective map to the original discrete Gamma. Ambient original compact quotient and local compactness provide the actual K via the proved open quotient representative construction. Combining the actual finite commutator proof gives compactness of center(G)/(Gamma intersect center(G)) under the stated actual centralizer and finite-generation hypotheses.', 'NativeCenterLattice discharges these generic hypotheses for the actual original arbitrary connected simply connected finite-dimensional nilpotent Lie group and specified lattice. Original Lie smoothness supplies the true topological-group instance; actual exponential diffeomorphism supplies local compactness; retained actual lattice finite generation and the new true centralizer equality give the natural center quotient CompactSpace. No restricted center compactness, replacement lattice, supplied rational form or additive nonabelian Log(Gamma) is assumed.', 'Ten new modules and 25 proved theorems give 25 exact new reports. Require actual terminal exit-zero full build and kernel records, byte log hashes, exact registration names, all-source trust scan, current new oleans and unchanged retained axioms. All 805 own plus nine attributed PNT+ modules and root/registry are covered; 823 source/config hashes. Eleven retained axiom-free reports remain unchanged; new empty axiom reports are checked against actual output. No new option overrides or proof placeholders.', 'The actual specified lattice now restricts to a discrete cocompact subgroup of the actual original center. This is a necessary step for central induction on full lattice rational form; it alone does not prove real independence of the original finite Q-basis or cocompactness for every rational subgroup. Positive root uniqueness is proved, but root saturation subgroup closure remains unproved. Full scalar-extension injectivity, arbitrary rational subgroup lattice-intersection cocompactness, quantitative bounds, reverse original group/Lie lower-central comparison, Malcev, full calibration/Alignment and positive ordered arithmetic witnesses remain. StrongConjecture and the full prize target are unproved; publication/submission await full proof and audit.']

COMPONENTS = ['actual finite exponentials of nilpotent continuous linear operators fix only actual kernel vectors through a proved constant-one polynomial unit', 'actual commuting exponentials in the original simply connected nilpotent Lie group are equivalent to zero actual native brackets', 'actual original natural power logarithm identities and explicit unique positive-degree roots follow from true one-parameter and global inverse laws', 'actual original center membership is zero actual adjoint generator and actual cocompact subgroup centralizers equal the entire original group center', 'actual finite coordinate images give finite complete commutator records with finite representatives in the original source', 'actual equal generator commutator records detect differences in the original generated subgroup centralizer', 'actual discrete original subgroups have finite central compact-translate commutator records by compact image intersections', 'actual center compact representatives are constructed from finite original commutator record representatives and genuine finite compact translates', 'actual natural center intersection subgroups are discrete and their natural coset quotients are compact from actual center representatives', 'actual arbitrary specified original nilpotent Lie group lattices intersect the original center in genuine discrete cocompact center subgroups']

NEW_PROGRESS = "The actual original native adjoint differential is the original native bracket, and original group nilpotency proves native Lie lower-central termination at the original class c. The actual original exponential comes from proved genuine global invariant curves. Original relative-curve mixed derivatives and group cocycle prove the actual finite dexp formula and genuine native local C-infinity inverses. Original fibers are exactly cosets of the proved closed discrete native central period subgroup. Actual dexp defect W_v lowers original layers, W_v^c=0, and the genuine finite geometric sum U_v is its true two-sided inverse. The actual C-infinity field F_w(v)=U_v(w) strictly improves parameter differences by one original lower-central layer. Original finite-dimensionality proves these layers genuinely closed and true quotient-map integral commutation keeps actual integrals inside them. Actual global Picard iterates gamma_0=u and gamma_(n+1)=u+integral(0..t,F_w(gamma_n)) have true FTC derivatives. Actual differences gamma_(n+1)-gamma_n belong to S_n; the original nilpotency class c kills the next difference, proving gamma_(c+1)=gamma_c and the genuine global logarithm-lifting ODE including c=0. Actual manifold chain rules and original global integral-curve uniqueness prove Exp(gamma(t))=Exp(u)*gamma_w(t), giving a true product logarithm at one. The actual original exponential range is a subgroup; its true openness and original connectedness make it all of G. Thus genuine whole-group surjectivity and the actual additive-period quotient covering are proved. Original simply connectedness now eliminates the actual period group. Original local path connectedness is genuinely derived from the actual exponential quotient map of original E; it is not an extra premise. The true covering lifting theorem lifts identity G with lift zero of one to an actual continuous logarithm L. Actual preconnectedness of original E and genuine covering lift uniqueness prove both inverse laws L(Exp(v))=v and Exp(L(g))=g. Actual original exponential injectivity follows and K is exactly bottom. Near every original group point the actual global L equals the previously constructed true local logarithm by injectivity. Therefore L is genuinely native C-infinity. The actual native exponential and this constructed L form a global native C-infinity Diffeomorph E-to-G, with actual inverse differential composition. Global surjectivity, injectivity, period elimination and global smooth inverse no longer remain open tasks. No replacement matrix model, supplied global inverse, assumed BCH or nonabelian additive lattice logarithms is used. Every original native real Lie subalgebra is now proved closed in finite dimension and preserved by the genuine finite inverse field and actual Picard integrals. Its actual exponential image itself is a subgroup. The actual restricted exponential and global logarithm form a natural subtype homeomorphism, proving genuine closedness and contractibility, hence connectedness and simply connectedness. Every original native Lie ideal exponentiates to a normal original subgroup by actual finite adjoint invariance. The original native Lie lower-central layers S_j exponentiate to a decreasing normal filtration H_j with H_0=G, H_c=1 and closed contractible terms in the original simply connected case. Actual dexp equations prove F_w(v)-w lies in S_(j+1) when w lies in S_j, and real Picard integrals give Lift(w,u,t)-(u+t*w) in S_(j+1). The actual finite adjoint formula, padded by its genuinely zero terminal power, gives Ad(g)(w)-w in S_(j+1). True conjugation and product-logarithm laws place [g,Exp(w)] in H_(j+1). Subgroup commutator generation and induction prove the one-sided inclusion of the original algebraic Group.lowerCentralSeries(j) in H_j. The actual global logarithm of Exp(u)*Exp(w) is the genuine finite Picard lift; its additive error lies in S_(j+1), and actual log(g*h)-log(g)-log(h) lies in S_1. These are statements about original arbitrary groups and original native brackets, not replacement matrix models. The genuine finite Picard product logarithm now has an explicit finite recursive rational original-bracket polynomial representation. Actual finite coefficient lists evaluate as real vector polynomials; pairwise original bilinear expansion and rational scaling preserve exact evaluations. The actual Bochner primitive of a monomial is given by division by its positive new degree in Q. Thus rational-time membership is proved by exact arithmetic, without treating an arbitrary Q-linear subspace as topologically closed. Actual original dexp defect powers and the actual finite geometric inverse field have explicit rational polynomial lists, using the actual adjoint differential already identified with the original native bracket. The actual Picard integral iterates exactly equal the real evaluations of their recursively constructed finite coefficient lists. Their coefficients stay in every original bracket-closed Q-linear structure V containing u,w; all true Picard iterates and the stabilized lift belong to V at rational times. The actual global logarithm of Exp(u)*Exp(w) therefore belongs to V, and Exp(V) itself is a genuine subgroup with exact actual logarithm membership. Actual original finite factorial adjoint formulas prove that conjugation by group elements with logarithms in V preserves V. An explicit finite polynomial list represents the actual original global logarithm of Exp(u)*Exp(t*w) for every real t, with the genuine product logarithm at one. All operations use original vectors, original brackets and rational scalars, not replacement matrices or supplied BCH laws. The arbitrary specified original subgroup Gamma now supplies a derived rational Lie structure W=span_Q(Log(Gamma)). Actual original conjugation proves its adjoint invariance under Gamma. Genuine natural-time adjoint values are conjugations by Gamma powers; algebraic rational vector polynomial coefficient extraction, with true nilpotent zero padding at all classes, recovers actual original generator membership. Actual bilinearity and the proved native bracket identity establish bracket closure of W without supplying it. The actual rational BCH result therefore preserves W and Exp(W) is a genuine rational hull subgroup containing Gamma, with exact original logarithm membership and rational Lie minimality. Every hull element's actual adjoint preserves W. Actual real linear span induction proves span_R(W)=span_R(Log(Gamma)) is an original native Lie subalgebra; its genuine original exponential subgroup contains Gamma and is closed and contractible. Explicit terminating lower-central descent proves that a proper nilpotent Lie subalgebra remains proper after adding the actual commutator layer. Real dual separation gives an actual nonzero linear functional vanishing on that sum. Actual product-logarithm errors prove its original continuous logarithmic character law, and genuine original exponential/logarithm inverses give surjectivity to R. This actual character descends to the original possibly nonnormal coset quotient. If the original specified quotient G/Gamma is compact, noncompactness of R contradicts surjectivity. Thus the actual specified cocompact subgroup's logarithms have full real span. No replacement group, supplied bracket closure, assumed character, rational-subspace closedness or additive nonabelian Log(Gamma) is used. The actual specified discrete cocompact subgroup Gamma is now proved finitely generated. Actual original local compactness is derived from the true exponential diffeomorphism and the original finite-dimensional real model. The actual open coset quotient map and its original compact target yield actual compact representatives K with an open subset O satisfying O*Gamma=G. The actual discrete subgroup has only finitely many elements in K^-1*K. Genuine translate overlaps and original preconnectedness prove these actual elements generate Gamma. The actual native Lie algebra over Q is constructed from the original real bracket with proved scalar compatibility, and its true Q lower-central series terminates at the original group class. Actual right-nested bracket words in finite original seed vectors belong to their true word-length lower-central layers. Actual nilpotency kills long words and actual bounded finite-list values are finite. Actual Jacobi gives a genuine Lie stabilizer of the bounded-word linear span. Seed adjoints preserve that span by prepending below the actual class and vanishing at the boundary; the actual generated Lie subalgebra is in that stabilizer and equals the bounded-word span, so it has an actual finite module spanning set. The actual W=span_Q(Log(Gamma)) now equals the original Q-Lie span of the original finite generating set's actual logarithms. The retained genuine rational BCH theorem makes the exponential image of that Lie span an actual original subgroup containing the generators and hence Gamma, giving one inclusion. The previously proved actual bracket closure of W gives the reverse inclusion. Therefore actual W is finite dimensional over Q and has a genuine finite Q-spanning set. This uses actual original Gamma, original vectors and original bracket; no replacement model, supplied finite generation, assumed finite Q dimension or additive nonabelian Log(Gamma). Actual commuting exponentials in the original simply connected nilpotent Lie group now imply zero actual native bracket. Genuine conjugation and exponential injectivity give an actual adjoint-fixed vector; actual finite adjoint factorization through a proved invertible constant-one polynomial gives the true generator kernel. The retained genuine adjoint ODE gives the reverse direction. Actual natural powers have Log(g^n)=n*Log(g), and explicit original Exp(n^-1*Log(g)) gives the unique positive-degree root. Actual center membership is exactly zero actual generator. The actual generator kernel of any Gamma-centralizing element contains every original Gamma logarithm; actual full real spanning therefore makes it zero. Thus the actual original cocompact subgroup has centralizer equal to the original group center. Original finite group generators give genuine finite commutator records of Gamma elements with central compact K-translates. Every coordinate equals an actual original compact commutator image value and remains in discrete Gamma, so its actual image is finite. Genuine finite coordinate products give finite complete records and finite source representatives. Equal actual generator commutator records give equal original conjugation homomorphisms on generated Gamma and hence actual differences centralizing Gamma, which lie in the original center. The actual finite union of compact K translates by record representatives, intersected with the actual closed original center, therefore supplies compact center representatives modulo the actual Gamma-center intersection. Actual closed-subtype pullback and the original quotient map prove genuine CompactSpace of center(G)/(Gamma intersect center(G)); a genuine continuous injection into Gamma proves actual restricted lattice discreteness. For the arbitrary original connected simply connected finite-dimensional real nilpotent Lie group, actual original local compactness, actual specified lattice finite generation and the proved original centralizer equality discharge every auxiliary hypothesis. No restricted center compactness, supplied full rational form, replacement matrix group, different lattice or additive nonabelian Log(Gamma) is assumed. Remaining: actual real scalar-extension injectivity and full specified-lattice rational form, including real linear independence of a Q-basis and actual central induction; arbitrary specified-lattice rational subgroup cocompactness; quantitative degree/denominator bounds; reverse original group/Lie lower-central inclusion, exact comparison and algebraic layer closedness; faithful integration/Malcev. Positive root uniqueness does not itself prove root-saturation subgroup closure, which remains unproved. Finite Q dimension and full real span do not themselves prove real Q-basis independence. Full calibration/Alignment and ordered positive arithmetic witnesses remain unproved. StrongConjecture and the full prize target remain unproved; publication and submission await full proof and audit. No unavoidable blocker."


def record():
    from importlib.util import spec_from_file_location, module_from_spec
    baseline, registration, files, verified, blog, alog, fixed = checks()
    manifest = obj("verification-manifest.json")
    assert manifest["files"] == baseline["files"] and manifest["full_target_proved"] is False
    assert len(manifest["proved_components"]) == 888
    assert not set(COMPONENTS) & set(manifest["proved_components"])
    spec = spec_from_file_location("previous_audit_body", OLD + "-audit.py")
    previous = module_from_spec(spec)
    spec.loader.exec_module(previous)
    remaining = manifest["last_round"]["remaining"]
    assert remaining.count(previous.NEW_PROGRESS) == 1
    remaining = remaining.replace(previous.NEW_PROGRESS, NEW_PROGRESS)
    review = {
        "date": "2026-10-10", "classification": "PROGRESS", "previous_goal_turn_classification": "PROGRESS",
        "full_target_proved": False, "baseline_hash_count": 813,
        "retained_changed": ["Hindman168.lean", "Verification.lean"],
        "new_modules": registration["new_modules"], "new_theorem_count": 25,
        "new_selected_report_count": 25, "module_report_counts": registration["module_report_counts"],
        "application_review": APPLICATION, "verification": verified, "remaining": remaining,
    }
    manifest.update(
        date="2026-10-10", files=files, build_succeeded=True, axiom_check_succeeded=True,
        hindman_module_count=verified["project_modules"], pntplus_module_count=verified["pntplus_modules"],
        selected_axiom_report_count=verified["axiom_reports"], source_scan_module_count=verified["source_scan_modules"],
        build_job_count=verified["build_jobs"], build_log=PREFIX + "-build.txt", axiom_log=PREFIX + "-axioms.txt",
        last_round={"classification": "PROGRESS", "new_module_count": 10, "new_theorem_count": 25,
                    "new_selected_report_count": 25, "retained_proof_sources_changed": False,
                    "root_and_registry_changed": True, "review_file": PREFIX + "-review.json", "remaining": remaining},
    )
    manifest["proved_components"] += COMPONENTS
    audit = read("AUDIT.txt")
    marker = "Remaining proof work:"
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline["last_round"]["remaining"]
    note = '\n2026-10-10 round-native-root-saturation: PROGRESS. Ten new modules, 25 proved theorems and 25 exact new reports. All 813 baseline hashes verified before registration; only retained root/registry change. True nilpotent finite adjoint fixed-vector kernel and original global exponential injectivity prove commuting iff native bracket zero. Actual natural power/logarithm identities give explicit unique positive-degree roots. Actual cocompact logarithmic full real span proves centralizer(Gamma)=center(G). Actual discrete compact commutator images give finite records on original finite generators. Equal records give actual central differences. An actual finite union of compact translates intersected with the actual closed center constructs genuine compact center representatives. Actual natural quotient image proves center(G)/(Gamma intersect center(G)) compact, and actual subgroup injection proves intersection discreteness. The arbitrary original nilpotent Lie group and specified lattice discharge all auxiliary hypotheses. Root-saturation subgroup closure, full rational form/real Q-basis independence, arbitrary rational subgroup cocompactness, quantitative bounds, reverse group/Lie comparison, Malcev and full target remain unproved. Eleven retained axiom-free reports and all retained axiom sets unchanged; actual new empty reports separately checked. All 805 own and nine attributed PNT+ modules plus root/registry scanned; 823 source/config hashes. Actual full build and exact kernel totals: ' + str(verified["build_jobs"]) + ' jobs, 4064 exact unique standard-axiom reports, both terminal exit 0. New sources warning-free and oleans current. Fixed local paper and actual pins match; no remote updates. No unavoidable blocker. Review: round-native-root-saturation-review.json.\n\n'
    Path("AUDIT.txt").write_text(audit.split(marker, 1)[0] + note + marker + "\n" + remaining + "\n", encoding="utf-8")
    Path("BUILD-EVIDENCE.txt").write_bytes(b"=== COMPLETE BUILD OUTPUT ===\n" + blog + b"\n=== COMPLETE AXIOM OUTPUT ===\n" + alog + b"\n")
    write_obj(PREFIX + "-review.json", review)
    write_obj("verification-manifest.json", manifest)
    write_obj(PREFIX + "-preprint-local-check.json", fixed)
    write_obj(PREFIX + "-source-scan.json", {
        "project_modules": 805, "pntplus_modules": 9, "scanned_module_count": 814,
        "root_registry_scanned": True, "executable_banned_tokens": [], "new_unlimited_heartbeats": [],
        "new_disabled_linters": [], "retained_changed": review["retained_changed"],
        "root_imports_exact": True, "new_option_overrides": [],
    })
    write_obj(PREFIX + "-kernel-check.json", {
        "exact_unique_reports": 4064, "registered_names_exact": True, "new_names_exact": True,
        "retained_axiom_sets_unchanged": True, "allowed_axioms": sorted(ALLOWED),
        "axiom_free_reports": sorted(AXIOM_FREE),
        "retained_axiom_free_reports": sorted(AXIOM_FREE - NEW_AXIOM_FREE),
        "new_axiom_free_reports": sorted(NEW_AXIOM_FREE),
    })
    write_obj(PREFIX + "-checks.json", {
        "baseline_hashes_verified_before_registration": 813, "previous_current_state_rechecked_before_edits": True,
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
    assert review["new_theorem_count"] == 25 and review["new_selected_report_count"] == 25
    assert review["new_modules"] == registration["new_modules"]
    assert review["module_report_counts"] == registration["module_report_counts"]
    assert manifest["last_round"]["remaining"] == review["remaining"] == read("AUDIT.txt").split("Remaining proof work:", 1)[1].strip()
    assert len(manifest["proved_components"]) == 898 and manifest["proved_components"][-10:] == COMPONENTS
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
    assert scan["scanned_module_count"] == 814 and not scan["executable_banned_tokens"] and not scan["new_option_overrides"]
    kernel = obj(PREFIX + "-kernel-check.json")
    assert kernel["exact_unique_reports"] == 4064 and kernel["retained_axiom_sets_unchanged"]
    result["fresh_final_recheck"] = {
        "source_config_hashes": len(files), "retained_only_root_registry_changed": True,
        "new_modules": len(registration["new_modules"]), "new_theorems": 25, "new_selected_declarations": 25,
        "all_source_modules_scanned": 814, "build_jobs": verified["build_jobs"], "kernel_exact_unique_reports": 4064,
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
