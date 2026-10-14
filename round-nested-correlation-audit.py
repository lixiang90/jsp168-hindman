"""Register and audit the actual product quotient and representation increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-nested-correlation'
OLD = 'round-nested-recursion'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/WeightedHaarRecursiveCauchySchwarz.lean', 'Hindman168/SubgroupSumPairMoment.lean', 'Hindman168/NestedMixedDualCorrelation.lean', 'Hindman168/NestedMixedDualCorrelationLimit.lean']
COMPONENTS = ['The original weighted correlation now has a verified recursive Cauchy-Schwarz duplication bound. Actual translated representations are averaged over shift and core parameters, preserving the original cell probabilities; only the core needs unit bounds for this estimate. Exact subgroup-sum Haar and paired-shift identities reduce independently sampled summand shifts to the Haar law on the subgroup sum. The corresponding genuine next-order Gowers moment and finite threshold bound are proved. The exact two-level dual expansion supplies the recursive representation, giving a finite correlation-square bound by epsilon plus the next-order subgroup-sum Gowers power divided by a positive threshold power. Under the two explicit lower intersection containments, the audited uniform paired-coefficient threshold supplies this finite bound eventually for every selected unit test. Thus vanishing next-order subgroup-sum Gowers values imply vanishing actual nested-dual correlation along the same tail-containing ultrafilter. No subgroup-cardinality bound or replacement of original cell weights is used.']
REMAINING = 'The common-system master estimates, first-order Bessel, dual energy reduction, recursion and stability are proved. Actual dual functions now have a common finite empirical approximation preserving arbitrary cell probabilities, unit bounds and uniform bounded-test correlations. Exact arbitrary-vertex reflection of the actual subgroup cube law and mixed products is now proved. Mixed cubes now have exact arbitrary-vertex duality and weighted single-vertex replacement estimates. Finite products of dual functions now have quantitative empirical approximation uniform over bounded tests. Exact translated-product expansions and extraction for each fixed test are now proved. The exact mixed face split, projected-face correlation and one-step face Cauchy-Schwarz inequality are now proved. Face energies are now identified with actual copied cube means, with nonnegativity and copy algebra verified. Arbitrary-coordinate permutation invariance, copied-mean nonnegativity and reflection bounds are now established. Full multidimensional mixed Gowers Cauchy-Schwarz, the product-root bound and the single-vertex bound are now proved. Actual dual anti-uniformity, its weighted version and the finite zero-root orthogonality characterization are now proved. Mixed dual recursion, covariance and exact subgroup-shift expansions are now established. Same-subgroup mixed-dual finite products now have an exact averaged dual representation and retain weighted anti-uniformity. The actual unit-input mixed-dual convex hull now has multiplicative and translation closure with unchanged weighted anti-uniform bounds. For varying finite groups and cell types, the exact weighted Haar Hilbert realization and vanishing-Gowers/closed-dual-span orthogonality equivalence are now proved. The dual Hilbert span now has uniformly bounded scaled-hull representatives dense in its closure; their bound may depend on the approximation. Fixed-polynomial and continuous functional calculus for scaled-hull representatives, their clipping closure, and unit-interval-valued approximation of the actual dual Hilbert projection are now proved. The actual dual projection now controls the limiting Gowers power and yields unit-interval models with arbitrarily small Gowers error along the same ultrafilter. For ultrafilters containing every tail, diagonalization now provides one exact unit-interval representative of the dual projection and residual Gowers convergence to zero. Actual unit mixed-dual-hull multiplication now preserves the closed dual space and its orthogonal complement and satisfies the genuine projection pull-out identity on represented inputs. Every unit-bounded actual representative in the closed mixed-dual subspace now multiplies that subspace and its orthogonal complement into themselves. The genuine projection pull-out identity extends to these structured multipliers without requiring cellwise convex-hull membership. Actual translations, with shifts allowed to vary by stage and cell, act linearly on weighted-Haar L2-bounded families, preserve their Hilbert distances, and have inverse-shift adjoints. They preserve the closed mixed-dual subspace and its orthogonal complement; the genuine dual projection commutes with translation on actual represented inputs. Closed Hilbert subspaces containing every selected actual unit family now contain their internal finite averages, using fixed sample counts and the original weighted L2 variance bound. Finite products of unit represented structured inputs remain structured. Taking a mixed dual along any second subgroup system preserves the first closed dual space for such inputs. A unit represented member of the first space orthogonal to the intersection has vanishing second-system Gowers seminorm and is orthogonal to the entire second dual space. For tail-containing ultrafilters and positive degrees, actual dual projections now preserve the other closed dual space and commute on the entire completed Hilbert space. The proof first transfers orthogonality using actual unit-bounded projection representatives, proves unit-interval compatibility and an exact intersection model, then extends closed-space preservation from bounded generators by projection continuity and derives full commutation by self-adjointness. The first-order mixed dual is now identified with actual subgroup Haar averaging. Its unit hull consists of subgroup-invariant functions, and unit invariant functions belong to it. Actual first-order projections have exact unit Haar representatives. The first-order closed dual space is antitone in the subgroup, and its base concatenation is proved as the full equality of the two first-order spaces intersection with the first-order space of the subgroup sum, for every ultrafilter. The actual lower-order recursive coefficient now has a unit-bounded representative in both the lower first-direction dual space and the positive-degree second-direction dual space, for shifts varying by stage and cell. A dependent-selection argument gives uniform small correlation from vanishing correlation for every selected parameter family, without bounded cardinality assumptions. Orthogonality to the lower intersection therefore controls all these recursive coefficients uniformly along the ultrafilter. A tail-containing ultrafilter now supplies a positive uniform testing threshold from null testing of every dependent selected sequence, proved by slow-stage diagonalization. Every selected actual unit family in a positive-degree dual space therefore admits one eventual Gowers threshold controlling all parameters and all unit tests. The result also applies to fixed finite products of structured families and to recursive coefficients under the explicitly displayed lower-space containment. The original cube average is invariant under ambient translation. Averaging a pair-shift multiplicative derivative gives exactly the next cube order, and the corresponding Gowers moment identity preserves the original cell weights. A finite Haar testing estimate bounds mean absolute correlation by epsilon plus the next-order weighted Gowers power divided by a positive threshold power. Under an explicit eventual uniform small-test hypothesis, vanishing next-order Gowers values imply vanishing mean absolute correlation for varying finite subgroup systems along any filter. The actual mixed-dual families with unit inputs represented in the other dual space now generate a defined closed Hilbert subspace. Root normalization is proved harmless. This localized span contains the constant one and is contained in the original factor intersection when the other degree is positive. Finite products of localized actual duals lie in the localized closed span by an exact averaged dual representation and the verified internal-average theorem. Generic unit-generated spans have uniformly bounded actual algebraic-span representatives and dense actual approximants. Unit multipliers whose products with the generators lie in the closed span preserve that span, and pairwise generator closure extends to every actual unit represented member. Consequently actual unit members of the localized span multiply it into itself. An actual unit represented member of the other factor orthogonal to this localized span has vanishing first-factor Gowers value and is orthogonal to the entire first factor. A closed unit multiplier algebra containing the constant one now has actual power and polynomial representatives for uniformly bounded represented members, continuous functional calculus for such representatives, unit-interval approximants of its actual orthogonal projection, and an exact unit-interval projection representative for tail-containing ultrafilters. These results are discharged for the previously constructed localized dual span. Unit-interval actual members of the original factor intersection belong to that localized span: their residual after the localized projection remains in both original factors, and the localized separation theorem makes that residual orthogonal to the first factor, so it vanishes. Projection continuity extends this argument from bounded first-factor generators to the entire completed Hilbert space. Consequently the actual localized dual span is proved equal to the original factor intersection, with actual uniformly bounded algebraic-span approximants and unchanged cell weights. The first-direction actual dual generators may now be required to have all nonroot unit inputs represented in both original factors. Their closed Hilbert span is defined and proved equal to the original factor intersection. Joint input structure survives finite products and translations selected separately by input, stage and original cell. Exact finite products of these actual dual generators lie in their joint closed span, and every actual unit represented member multiplies that span into itself. Unit-interval projection representatives, orthogonal residual separation and projection continuity prove the full completed-Hilbert-space density equality. Every intersection vector has actual uniformly bounded approximants in the original algebraic span of joint dual families, with all original cell weights retained. The same statement can be applied with the two factors interchanged. The actual mixed dual is now a linear contraction in any single nonroot input when its other nonroot inputs are unit bounded. The replaced input needs only L2 boundedness, not a pointwise unit bound. The contraction preserves the original weighted finite Haar norm and passes to Hilbert distances along every ultrafilter. Genuine nested dual families are defined by requiring one distinguished nonroot input of a joint first-direction dual to be an actual joint second-direction dual. Their closed Hilbert span is proved equal to the original factor intersection for positive degrees and tail-containing ultrafilters. The proof inserts actual finite second-direction dual approximants through the contraction and uses linearity to keep the output in the nested generator span. Consequently every intersection vector has actual uniformly bounded algebraic-span approximants of genuine nested duals, with both original factor memberships retained at the inputs and all original cell weights unchanged. The actual lower recursive coefficient and the product of its two shifted directions are now defined. Their unit bounds are proved, and the zero-degree coefficient is identified exactly with the constant one. A genuine outer dual whose distinguished singleton input is a second-direction actual dual has an exact two-level finite Haar expansion after subgroup shifts n and m, with the shifted coefficient product and translated inner singleton input displayed. Every genuine nested generator supplies actual unit inputs retaining both factors and this exact expansion. Each shifted lower coefficient lies in a positive-degree target factor under an explicit positive-lower-degree containment premise, with the zero-degree branch discharged by constant-one membership. Under the two explicit lower intersection containments, the actual double coefficient is unit bounded and target structured for arbitrary shifts selected by stage and original cell. A uniform eventual positive Gowers threshold consequently tests every pair of double coefficients against every actual unit test. The lower containments remain premises to be discharged by the higher-order concatenation induction; no full concatenation theorem is claimed here. The original weighted correlation now has a verified recursive Cauchy-Schwarz duplication bound. Actual translated representations are averaged over shift and core parameters, preserving the original cell probabilities; only the core needs unit bounds for this estimate. Exact subgroup-sum Haar and paired-shift identities reduce independently sampled summand shifts to the Haar law on the subgroup sum. The corresponding genuine next-order Gowers moment and finite threshold bound are proved. The exact two-level dual expansion supplies the recursive representation, giving a finite correlation-square bound by epsilon plus the next-order subgroup-sum Gowers power divided by a positive threshold power. Under the two explicit lower intersection containments, the audited uniform paired-coefficient threshold supplies this finite bound eventually for every selected unit test. Thus vanishing next-order subgroup-sum Gowers values imply vanishing actual nested-dual correlation along the same tail-containing ultrafilter. No subgroup-cardinality bound or replacement of original cell weights is used. Null correlation for genuine nested generators still needs to be extended to membership in the next-order subgroup-sum closed dual space, and both lower containments discharged by the higher-order concatenation induction. Higher-order concatenation controlling dual correlations and the full qualitative Bessel theorem remain missing, as do remaining replica integration, cyclic-to-interval transfer and inverse correlator existence. Coloring-derived targets, Calibration/Alignment and final ordered positive rapidly separated monochromatic extraction remain. StrongConjecture is unchanged and unproved. No unavoidable blocker is established; publication, PR and prize application remain pending.'


def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|instance)\s+([A-Za-z][A-Za-z0-9_\.]*)', old.lean_code(read(p)), re.M) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 1124
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 12
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 12
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
    write(PREFIX + '-registration.json', {'baseline_hash_count': 1124, 'modules': MODULES,
        'names': names, 'theorem_count': 12, 'declarations': ds})
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
    assert len(own) == 1110 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 12
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
    assert len(registered) == len(set(registered)) == len(actual) == 5248
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
    assert len(files) == len({f['path'] for f in files}) == 1128
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=12, new_definitions=0, new_instances=0, new_axiom_reports=12, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. The nested-recursion round was rechecked before edits. Retained proof hashes, kernel axiom sets and pinned dependencies remain unchanged.', 'Finite weighted Haar means commute with internal finite averaging by finite-sum and Haar linearity. The cell weights remain the original p(c); there is no unweighted replacement of the cell law. The average-square identity is proved by two independent finite Haar averages.', 'Ambient translations, allowed to depend on the shift parameter and original cell, preserve the original weighted correlation exactly. For an actual translated recursive representation, the correlation is reorganized as an average of core-weighted shift averages. Cauchy-Schwarz first squares the core average and then discards the unit core in the original weighted law. The resulting squared shift average is expanded exactly into two copies and bounded by the absolute paired correlation.', 'The generic recursive square estimate assumes normalized nonnegative original cell weights, nonempty finite shift/core parameter types and a pointwise exact representation. It needs unit bounds only on the core, not on either the recursive coefficients or the tested function. All of these premises are displayed in the statement.', 'The sum-subgroup Haar identity specializes the audited surjective addition-homomorphism result. Independently averaging a pair of Q-by-R shifts gives exactly the paired Haar law on Q sup R. The genuine weighted next-order Gowers moment is then transferred to this sampling law, with no bound on fiber size or subgroup cardinality.', 'The finite power-threshold estimate is applied to each sampled shift pair. Averaging and the verified sum-subgroup moment yield epsilon plus the next-order weighted Gowers power divided by the positive threshold power. The lower order is explicitly positive, and the threshold is strictly positive; no unsupported division or zero-order norm identity is used.', 'For an actual nested dual, the shift parameters and core parameters are both Q times R. The actual two-level expansion discharges the generic representation premise. The core is the translated distinguished inner singleton input, so its unit bound follows from the nonroot inner input bound.', 'The finite nested correlation bound supplies the trivial paired-test unit bound using the actual double-coefficient bounds, the unit test bound, normalized original cell weights and the finite Haar absolute bound. Its small-test condition is explicit. The Markov estimate is uniform in the core parameter, which permits averaging over the entire core law without a cardinality bound.', 'The varying-stage limit theorem applies the audited uniform paired-coefficient threshold under both explicitly displayed lower intersection containments. For each sampled shift pair, its multiplicative test derivative is unit bounded. The two coefficient parameter choices are inserted into the Fin 2 product threshold, and their exact product is matched by finite-product evaluation and commutative ring identities.', 'The threshold is selected for epsilon squared divided by two before using convergence of the next-order Gowers value. Its reciprocal power is therefore fixed along the limit. The remaining Gowers-power term tends to zero; the finite squared-correlation bound gives absolute correlation less than epsilon. This establishes genuine scalar null correlation on the same ultrafilter.', 'A development elaboration timeout was repaired by explicitly supplying the Q-by-R shift and core parameter types. The default heartbeat bound was not raised. Failed development commands are not treated as evidence; only terminal successful focused compilations, full build and complete selected kernel reports are accepted.', 'This follows Section 7 correlation duplication, threshold and moment steps, specialized to actual finite subgroup Haar laws. The positive lower intersection containments remain premises for the induction hypothesis. Closed-space membership of all nested generators, extension through the nested density equality and discharge of the induction remain work.', 'Twelve theorems in four modules are audited. The actual nested correlation-limit step is now proved. Full higher-order concatenation, qualitative Bessel, inverse correlator existence and the original StrongConjecture remain unproved.'], new_modules=MODULES, verified=summary, remaining=REMAINING,
        primary_reference='https://arxiv.org/html/1603.07815v4', reference_scope='Section 7 correlation duplication, threshold and moment; subgroup uniformity variant')
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=1110, pntplus_module_count=9,
        selected_axiom_report_count=5248, source_scan_module_count=1119,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=4, new_theorem_count=12,
            new_selected_report_count=12, retained_proof_sources_changed=False,
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
