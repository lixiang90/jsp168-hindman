"""Register and audit the actual product quotient and representation increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-joint-localization'
OLD = 'round-localized-intersection-density'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/JointMixedDualSpan.lean', 'Hindman168/JointMixedDualProducts.lean', 'Hindman168/JointMixedDualDensity.lean']
COMPONENTS = ['The first-direction actual dual generators may now be required to have all nonroot unit inputs represented in both original factors. Their closed Hilbert span is defined and proved equal to the original factor intersection. Joint input structure survives finite products and translations selected separately by input, stage and original cell. Exact finite products of these actual dual generators lie in their joint closed span, and every actual unit represented member multiplies that span into itself. Unit-interval projection representatives, orthogonal residual separation and projection continuity prove the full completed-Hilbert-space density equality. Every intersection vector has actual uniformly bounded approximants in the original algebraic span of joint dual families, with all original cell weights retained. The same statement can be applied with the two factors interchanged.']
REMAINING = 'The common-system master estimates, first-order Bessel, dual energy reduction, recursion and stability are proved. Actual dual functions now have a common finite empirical approximation preserving arbitrary cell probabilities, unit bounds and uniform bounded-test correlations. Exact arbitrary-vertex reflection of the actual subgroup cube law and mixed products is now proved. Mixed cubes now have exact arbitrary-vertex duality and weighted single-vertex replacement estimates. Finite products of dual functions now have quantitative empirical approximation uniform over bounded tests. Exact translated-product expansions and extraction for each fixed test are now proved. The exact mixed face split, projected-face correlation and one-step face Cauchy-Schwarz inequality are now proved. Face energies are now identified with actual copied cube means, with nonnegativity and copy algebra verified. Arbitrary-coordinate permutation invariance, copied-mean nonnegativity and reflection bounds are now established. Full multidimensional mixed Gowers Cauchy-Schwarz, the product-root bound and the single-vertex bound are now proved. Actual dual anti-uniformity, its weighted version and the finite zero-root orthogonality characterization are now proved. Mixed dual recursion, covariance and exact subgroup-shift expansions are now established. Same-subgroup mixed-dual finite products now have an exact averaged dual representation and retain weighted anti-uniformity. The actual unit-input mixed-dual convex hull now has multiplicative and translation closure with unchanged weighted anti-uniform bounds. For varying finite groups and cell types, the exact weighted Haar Hilbert realization and vanishing-Gowers/closed-dual-span orthogonality equivalence are now proved. The dual Hilbert span now has uniformly bounded scaled-hull representatives dense in its closure; their bound may depend on the approximation. Fixed-polynomial and continuous functional calculus for scaled-hull representatives, their clipping closure, and unit-interval-valued approximation of the actual dual Hilbert projection are now proved. The actual dual projection now controls the limiting Gowers power and yields unit-interval models with arbitrarily small Gowers error along the same ultrafilter. For ultrafilters containing every tail, diagonalization now provides one exact unit-interval representative of the dual projection and residual Gowers convergence to zero. Actual unit mixed-dual-hull multiplication now preserves the closed dual space and its orthogonal complement and satisfies the genuine projection pull-out identity on represented inputs. Every unit-bounded actual representative in the closed mixed-dual subspace now multiplies that subspace and its orthogonal complement into themselves. The genuine projection pull-out identity extends to these structured multipliers without requiring cellwise convex-hull membership. Actual translations, with shifts allowed to vary by stage and cell, act linearly on weighted-Haar L2-bounded families, preserve their Hilbert distances, and have inverse-shift adjoints. They preserve the closed mixed-dual subspace and its orthogonal complement; the genuine dual projection commutes with translation on actual represented inputs. Closed Hilbert subspaces containing every selected actual unit family now contain their internal finite averages, using fixed sample counts and the original weighted L2 variance bound. Finite products of unit represented structured inputs remain structured. Taking a mixed dual along any second subgroup system preserves the first closed dual space for such inputs. A unit represented member of the first space orthogonal to the intersection has vanishing second-system Gowers seminorm and is orthogonal to the entire second dual space. For tail-containing ultrafilters and positive degrees, actual dual projections now preserve the other closed dual space and commute on the entire completed Hilbert space. The proof first transfers orthogonality using actual unit-bounded projection representatives, proves unit-interval compatibility and an exact intersection model, then extends closed-space preservation from bounded generators by projection continuity and derives full commutation by self-adjointness. The first-order mixed dual is now identified with actual subgroup Haar averaging. Its unit hull consists of subgroup-invariant functions, and unit invariant functions belong to it. Actual first-order projections have exact unit Haar representatives. The first-order closed dual space is antitone in the subgroup, and its base concatenation is proved as the full equality of the two first-order spaces intersection with the first-order space of the subgroup sum, for every ultrafilter. The actual lower-order recursive coefficient now has a unit-bounded representative in both the lower first-direction dual space and the positive-degree second-direction dual space, for shifts varying by stage and cell. A dependent-selection argument gives uniform small correlation from vanishing correlation for every selected parameter family, without bounded cardinality assumptions. Orthogonality to the lower intersection therefore controls all these recursive coefficients uniformly along the ultrafilter. A tail-containing ultrafilter now supplies a positive uniform testing threshold from null testing of every dependent selected sequence, proved by slow-stage diagonalization. Every selected actual unit family in a positive-degree dual space therefore admits one eventual Gowers threshold controlling all parameters and all unit tests. The result also applies to fixed finite products of structured families and to recursive coefficients under the explicitly displayed lower-space containment. The original cube average is invariant under ambient translation. Averaging a pair-shift multiplicative derivative gives exactly the next cube order, and the corresponding Gowers moment identity preserves the original cell weights. A finite Haar testing estimate bounds mean absolute correlation by epsilon plus the next-order weighted Gowers power divided by a positive threshold power. Under an explicit eventual uniform small-test hypothesis, vanishing next-order Gowers values imply vanishing mean absolute correlation for varying finite subgroup systems along any filter. The actual mixed-dual families with unit inputs represented in the other dual space now generate a defined closed Hilbert subspace. Root normalization is proved harmless. This localized span contains the constant one and is contained in the original factor intersection when the other degree is positive. Finite products of localized actual duals lie in the localized closed span by an exact averaged dual representation and the verified internal-average theorem. Generic unit-generated spans have uniformly bounded actual algebraic-span representatives and dense actual approximants. Unit multipliers whose products with the generators lie in the closed span preserve that span, and pairwise generator closure extends to every actual unit represented member. Consequently actual unit members of the localized span multiply it into itself. An actual unit represented member of the other factor orthogonal to this localized span has vanishing first-factor Gowers value and is orthogonal to the entire first factor. A closed unit multiplier algebra containing the constant one now has actual power and polynomial representatives for uniformly bounded represented members, continuous functional calculus for such representatives, unit-interval approximants of its actual orthogonal projection, and an exact unit-interval projection representative for tail-containing ultrafilters. These results are discharged for the previously constructed localized dual span. Unit-interval actual members of the original factor intersection belong to that localized span: their residual after the localized projection remains in both original factors, and the localized separation theorem makes that residual orthogonal to the first factor, so it vanishes. Projection continuity extends this argument from bounded first-factor generators to the entire completed Hilbert space. Consequently the actual localized dual span is proved equal to the original factor intersection, with actual uniformly bounded algebraic-span approximants and unchanged cell weights. The first-direction actual dual generators may now be required to have all nonroot unit inputs represented in both original factors. Their closed Hilbert span is defined and proved equal to the original factor intersection. Joint input structure survives finite products and translations selected separately by input, stage and original cell. Exact finite products of these actual dual generators lie in their joint closed span, and every actual unit represented member multiplies that span into itself. Unit-interval projection representatives, orthogonal residual separation and projection continuity prove the full completed-Hilbert-space density equality. Every intersection vector has actual uniformly bounded approximants in the original algebraic span of joint dual families, with all original cell weights retained. The same statement can be applied with the two factors interchanged. The two-level approximation and nested recursive coefficient expansions still need to be connected to the higher-order concatenation induction. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'


def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1115
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 20
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 16
    root, registry = read('Hindman168.lean'), read('Verification.lean')
    for path in MODULES:
        line = 'import ' + path[:-5].replace('/', '.')
        assert line not in root.splitlines()
        root += '\n' + line + '\n'
    for name in names:
        line = '#print axioms ' + name
        assert line not in registry.splitlines()
        registry += '\n' + line + '\n'
    Path('Hindman168.lean').write_text(root, encoding='utf-8')
    Path('Verification.lean').write_text(registry, encoding='utf-8')
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1115, 'modules': MODULES,
        'names': names, 'theorem_count': 16, 'declarations': ds})
    print(json.dumps({'registered': len(names), 'modules': len(MODULES)}))


def run_build(kind):
    command = ['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean']
    if kind == 'kernel':
        result = obj(PREFIX + '-build-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + '-build.txt')
    log = PREFIX + ('-build.txt' if kind == 'build' else '-axioms.txt')
    start = time.monotonic()
    with open(log, 'wb') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record = dict(command=command, exit_code=result.returncode, terminal=True,
                  elapsed_seconds=time.monotonic() - start, log_sha256=digest(log))
    write(PREFIX + '-' + kind + '-result.json', record)
    print(json.dumps(record))
    if result.returncode:
        print(read(log)[-16000:])
        sys.exit(result.returncode)


def check():
    baseline = obj(PREFIX + '-baseline.json')
    registration = obj(PREFIX + '-registration.json')
    changed = [f['path'] for f in baseline['files'] if digest(f['path']) != f['sha256']]
    assert changed == ['Hindman168.lean', 'Verification.lean']
    own = sorted(Path('Hindman168').glob('*.lean'))
    pnt = sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
    assert len(own) == 1100 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 20
    for p in own + pnt + [Path('Hindman168.lean'), Path('Verification.lean')]:
        code = old.lean_code(read(p))
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b', code), p
        assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b', code, re.M), p
    for p in MODULES:
        assert not re.search(r'\b(?:set_option|setOptions)\b', old.lean_code(read(p)))
        olean = Path('.lake/build/lib/lean') / Path(p).with_suffix('.olean')
        assert olean.stat().st_mtime_ns >= Path(p).stat().st_mtime_ns
    for kind, log in [('build', '-build.txt'), ('kernel', '-axioms.txt')]:
        result = obj(PREFIX + '-' + kind + '-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + log)
        assert result['command'] == (['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean'])
        assert not re.search(r'(?:error:|warning:)', read(PREFIX + log))
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)\.', read(PREFIX + '-build.txt'))
    assert len(jobs) == 1 and int(jobs[0]) >= baseline['build_job_count'] + len(MODULES)
    previous, actual = old.reports(OLD + '-axioms.txt'), old.reports(PREFIX + '-axioms.txt')
    assert obj(OLD + '-kernel-result.json')['log_sha256'] == digest(OLD + '-axioms.txt')
    registered = re.findall(r'^#print axioms (\S+)', old.lean_code(read('Verification.lean')), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 5211
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == old.AXIOM_FREE | {'Hindman168.intervalResidueParent', 'Hindman168.completeResidueCellPoint'}
    assert old.run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']) == baseline['mathlib_commit']
    assert old.run(['git', '-C', '../reference-pntplus', 'rev-parse', 'HEAD']) == baseline['pntplus_commit']
    lean = old.run(['lake', 'env', 'lean', '--version'])
    assert 'version 4.32.2,' in lean and 'f3b06c705e6c85f5314019d5d3baab0fec5b580c' in lean
    fixed = obj(OLD + '-preprint-local-check.json')
    assert fixed['fixed_openai_math_commit'] == baseline['openai_math_commit']
    for section in fixed['sections']:
        data = (Path('E:/codex-build/math') / section['path']).read_bytes().replace(b'\r\n', b'\n')
        pinned = subprocess.run(['git', '-C', 'E:/codex-build/math', 'show',
            fixed['fixed_openai_math_commit'] + ':' + section['path']], stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=True).stdout.replace(b'\r\n', b'\n')
        assert data == pinned and hashlib.sha256(data).hexdigest() == section['normalized_sha256']
    files = [{'path': f['path'], 'sha256': digest(f['path'])} for f in baseline['files']]
    files += [{'path': p, 'sha256': digest(p)} for p in MODULES]
    assert len(files) == len({f['path'] for f in files}) == 1118
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=16, new_definitions=3, new_instances=1, new_axiom_reports=20, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The localized-intersection-density round was rechecked before edits. Retained proof source hashes and axiom sets remain unchanged.', 'The new generators are actual first-direction mixed duals with nonroot unit inputs represented in the intersection of both original factors. This joint input condition is explicit and is stronger than the preceding localized-family condition. The unused root is normalized using the previously proved exact nonroot congruence.', 'Joint families are shown to be a subset of the earlier localized families. Their closed Hilbert span therefore lies in the original factor intersection when the second degree is positive. The actual constant-one family is supplied with explicit membership in both factors, so it belongs to the joint span as well.', 'The shifted-product helper proves membership separately in both original factors, using their previously verified positive-degree unit multiplication and translation closure. Shifts may vary by input, stage and original cell. No pointwise structure or invariance is assumed in place of actual Hilbert factor membership.', 'The exact averaged dual identity for finite products is applied with its original subgroup Haar law. For every selected internal shift array, the new inputs are unit and remain in both factors by the shifted-product helper. Each selected dual is a genuine joint generator, so the internal-average theorem places the actual finite product in the joint closed span without a bounded-cardinality assumption.', 'Pairwise joint generator closure is discharged by the finite-product theorem. The generic unit-generated-algebra theorem then proves that every actual unit represented member of the joint closed span multiplies it into itself. Both positive degrees are displayed where the two factor multiplication closures are used.', 'For an actual unit represented member of the original intersection orthogonal to the joint span, its own first-direction pure dual has joint inputs and is a joint generator. The exact weighted correlation-power identity gives a vanishing first Gowers moment and seminorm, hence orthogonality to the whole first factor.', 'The previously audited generic algebra projection theorem is applied with its one and unit-product premises discharged. For a unit-interval actual intersection member, its residual after the joint projection remains in both factors and is unit bounded. The new separation theorem makes this residual orthogonal to the first factor, so its Hilbert norm is zero.', 'Projection continuity extends the argument to all completed Hilbert vectors by using bounded first-factor generators and the second-factor projection. This proves the full joint-span/intersection equality. The approximation corollary supplies actual members of the original joint-family algebraic span with arbitrary Hilbert error and a pointwise bound that may depend on the approximation.', 'The specialization scripts only read retained proof sources. The stronger membership conditions, both-degree requirements, changed selected-input proof, joint pure-dual separation premise and residual intersection membership are written to new modules and individually compiled. No retained theorem is changed or assumed stronger than its audited statement.', 'This matches the Section 7 requirement that the first dual inputs, and subsequently the second dual inputs obtained by swapping the factors, retain both original factors. Multilinear continuity for inserting finite dual approximations and the actual two-level recursive expansion still need to be integrated; no higher-order concatenation containment is claimed.', 'Sixteen theorems, three definitions and one projection instance are audited. Joint actual generator-density is now proved. Full higher-order concatenation, qualitative Bessel and the original StrongConjecture remain unproved.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 joint input localization')
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=1100, pntplus_module_count=9,
        selected_axiom_report_count=5211, source_scan_module_count=1109,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=3, new_theorem_count=16,
            new_selected_report_count=20, retained_proof_sources_changed=False,
            root_and_registry_changed=True, review_file=PREFIX+'-review.json', remaining=REMAINING))
    manifest['proved_components'] = baseline['proved_components'] + COMPONENTS
    audit = read('AUDIT.txt')
    marker = 'Remaining proof work:'
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline['last_round']['remaining']
    note = '\n2026-10-10 ' + PREFIX + ': PROGRESS. ' + ' '.join(COMPONENTS) + '\n'
    note += json.dumps(summary) + '\nReview: ' + PREFIX + '-review.json\n\n'
    Path('AUDIT.txt').write_text(audit.split(marker, 1)[0]+note+marker+'\n'+REMAINING+'\n', encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n' +
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    write(PREFIX+'-review.json', review)
    write('verification-manifest.json', manifest)
    write(PREFIX+'-preprint-local-check.json', fixed)
    write(PREFIX+'-checks.json', summary)
    print(json.dumps(summary))


def recheck():
    _, files, summary, _ = check()
    manifest = obj('verification-manifest.json')
    assert manifest['files'] == files and manifest['last_round']['remaining'] == REMAINING
    assert obj(PREFIX+'-review.json')['verified'] == summary
    assert read('AUDIT.txt').split('Remaining proof work:', 1)[1].strip() == REMAINING
    assert Path('BUILD-EVIDENCE.txt').read_bytes() == b'=== COMPLETE BUILD OUTPUT ===\n' + \
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+ \
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n'
    print(json.dumps(summary))


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    mode = sys.argv[1]
    if mode == 'register': register()
    elif mode in {'build', 'kernel'}: run_build(mode)
    elif mode == 'record': record()
    elif mode == 'recheck': recheck()
    else: raise ValueError(mode)
