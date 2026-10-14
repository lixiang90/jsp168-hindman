"""Audit actual same-frequency pair derivative, diagonal-center descent, compact family and exact original shifted polynomial samples.

This is author-side checking, not an independent kernel replay or a complete
verification of StrongConjecture. All original proof files are hash-retained.
"""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-native-fourier-pair'
OLD = 'round-native-central-pullback'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/CentralSubgroupFactorMap.lean', 'Hindman168/CentralSubgroupFactorFibers.lean', 'Hindman168/DiagonalCenterSubgroup.lean', 'Hindman168/ContinuousConjugatePair.lean', 'Hindman168/CentralSubgroupFactorObservable.lean', 'Hindman168/NativeFourierPairObservable.lean', 'Hindman168/NativeFourierPairInvariance.lean', 'Hindman168/NativeFourierPairFactor.lean', 'Hindman168/RoughVectorMvPairPolynomial.lean', 'Hindman168/NativeFourierPairPolynomial.lean', 'Hindman168/NativeFourierPairFactorCompact.lean']
COMPONENTS = ['ACTUAL normal-subgroup quotient/image-lattice map on ORIGINAL nonnormal lattice cosets is constructed, surjective, invariant under original subgroup action and an OPEN quotient map. True continuous image of original compact cosets supplies actual factor compactness. Original lattice normality is never assumed.', 'For an ACTUAL central subgroup N, genuine factor fibers equal ORIGINAL N-action orbits exactly, by original quotient equality and actual lattice representatives. No fiber-orbit equivalence is assumed.', 'The ACTUAL diagonal of ORIGINAL center in G times G is constructed. Membership is exactly a pair (z,z) with z in original center. Its center inclusion and normality are PROVED. Original product coset equivalence is equivariant under ACTUAL diagonal action.', 'Actual continuous conjugate pair F(q)*star(G(r)) has genuine uniform norm bound and joint continuous dependence on original continuous functions. An ACTUAL compact input family has compact paired image; not asserted spatially Lipschitz.', 'Genuine continuous descent of ACTUAL central-subgroup-invariant original observables to actual quotient/image lattice retains ALL point values, has uniqueness and pointwise bounds. Actual generic hypotheses are later fully discharged for original Fourier pair, rather than assumed at native application.', 'ACTUAL product coset projection into ORIGINAL specified metric factors is continuous using PROVED product-metric/original quotient topology equality. ACTUAL same-frequency original paired Fourier observable on original product lattice cosets is constructed with exact pointwise formula. Its functionspace dependence is continuous and image of ORIGINAL unit family is compact.', 'ACTUAL original Fourier eigencharacters have modulus one, so phase and conjugate phase cancel EXACTLY in original paired observable. Genuine ORIGINAL diagonal center action invariance and ACTUAL diagonal subgroup invariance are PROVED for all frequencies, including nonzero. No derivative invariance premise.', 'The ORIGINAL same-frequency paired Fourier observable genuinely descends to ACTUAL ORIGINAL diagonal-center group quotient/image lattice, with exact values on original product cosets and unique continuous descent. Actual factor is compact and projection open. This is actual factor coset geometry, not yet a fully constructed native filtered nilmanifold; closedness/rational lattice/compatible metric/induction complexity still need work.', 'An ACTUAL product-model vector polynomial is constructed by true linear inclusions and addition. Original degree bounds and actual product-model evaluations are preserved.', 'The ACTUAL shift-pair polynomial retains original degree and gives EXACTLY the ORIGINAL shifted and unshifted integer polynomial orbit under the TRUE product coset map. Actual factor observable evaluated on actual projected pair orbit is EXACT original same-frequency derivative value. For EVERY actual finite sample set, factor sample mean is EXACT original derivative average. Polynomial coefficients and shifts are unrestricted; no replacement samples.', 'Descent of ACTUAL paired observables is contractive on uniform-norm differences, from actual factor-map surjectivity and exact values. This gives genuine continuous dependence on original F and ACTUAL COMPACT descended pair family for every fixed frequency. ORIGINAL unit family yields actual factor pointwise norm at most ONE. No spatial Lipschitz bound, canonical factor Haar agreement, nilpotency/dimension decrease or quantitative inverse is inferred.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic FS/FP remains prize target. ALL retained scalar/standard-torus/native ABELIAN inverse/obstructions, original group/quotient Haar, central Fourier reconstruction/finite frequency detection, original zero-mode descent and actual low-step child native data/metric/exp-log projection, actual relatively compact measurable section/counting lift and compact finite Haar scalar classification remain proved. ACTUAL transversal restriction/counting recovery now EXACTLY recovers original arbitrary base nu with probability mass ONE. GENERAL ORIGINAL NONNORMAL invariant coset probability uniqueness is NOW genuinely proved by actual group Haar scalar normalization and actual original fundamental-domain independence. ACTUAL original center-factor pushforward probability NOW equals genuine child NativeData(s-1) canonical Haar, under actual PROVED Borel sigma-algebra compatibility; true zero-mode child canonical integral/discrepancy identities retain SAME original samples/observables. No normal-lattice converse or homogeneous uniqueness/measure agreement input remains in this compatibility step. The actual child-metric zero-mode family now has genuine uniform compactness and spatial Lipschitz approximation, with one fixed finite ACTUAL UNIT child family and positive fixed discrepancy threshold before all original observables and finite sample sets. SAME actual projected samples and child canonical Haar are retained. No topology-to-Lipschitz inference or assumed descended spatial regularity remains in this step. Actual child character pullback NOW genuinely preserves nonzero/horizontal/original lattice-integral properties with explicit operator bounds and ORIGINAL finite-grid membership. Actual polynomial orbit/degree/log representations and COMPLETE scalar polynomial/monomial/spatial-specialization coefficients are retained. ABELIAN root inverse NOW uses genuine ORIGINAL canonical Haar with proved measure/integral agreement. The actual step-at-most TWO ZERO-FREQUENCY inverse branch is NOW proved, producing a genuine ORIGINAL nonzero finite-grid horizontal character with BOTH monomial and paper-binomial bounds from the PROVED actual abelian child inverse. This is NOT a full step-two inverse: NONZERO central-frequency discrepancies and general child/nonabelian orbit inverse still remain open. Actual same-frequency Fourier pair observable is NOW constructed on ORIGINAL product lattice cosets, with genuine diagonal-center invariance and unique continuous descent to ACTUAL diagonal-center quotient/image lattice. Its actual shifted-pair polynomial preserves degree and gives SAME original shifted/unshifted integer orbit; actual factor sample mean equals original derivative average for EVERY finite sample set. Actual descended pair family is uniform-norm COMPACT and pointwise bounded by ONE for original unit inputs. This is NOT a quantitative inverse or a completed rational filtered nilmanifold: diagonal subgroup closedness/rational image lattice/compatible metric and actual filtered subgroup induction geometry still need to be constructed and verified. NEXT actual product/factor canonical Haar compatibility, actual diagonal quotient native/rational geometry and suitable fiber-product filtration, then genuine nonzero-frequency quantitative Leibman induction. Product/diagonal-center quotient does NOT automatically decrease nilpotency step or original dimension. Existing group-difference polynomial/iterated filtration facts remain proved and should be reused; no unproved inverse interface may count as completion. Then genuine original nonzero central-frequency derivative/product-group polynomial compatibility and NONABELIAN quantitative Leibman induction, fixed-data existence bounds only and no unsupported power laws. Projected/descended families are actual uniform-norm compact, not asserted spatially unit Lipschitz. Canonical-measure abelian root inverse is now proved. Generic finite-index rough API, actual original residue affine/scales finite obstruction density/descent, full rough-step/dimension/length/cofinal-scale comparison remain open. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence input remains unproved; it is distinct from orbit quantitative Leibman. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final original positive ordered separated FS/FP extraction remain unproved. Retain corrected large-N scope/actual unrestricted short-box O(eps) counterexample; no unavoidable full-goal blocker. Author build/hash/source/standard-axiom audits are not independent kernel replay or external peer review. No public repository, PR or prize submission yet; do so at actual completion or genuine unavoidable obstruction with honest scope.'

def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}


def run(command, log):
    start = time.monotonic()
    with open(log, 'wb') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    data = dict(command=command, terminal=True, exit_code=result.returncode,
                elapsed_seconds=time.monotonic()-start, log=log, log_sha256=digest(log))
    assert result.returncode == 0, (command, read(log))
    assert not re.search(r'(?:warning:|error:)', read(log)), log
    return data


def prepare():
    baseline = obj('verification-manifest.json')
    assert baseline['last_round']['review_file'] == OLD + '-review.json'
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    assert obj(OLD + '-axioms-result.json')['exit_code'] == 0
    assert obj(OLD + '-axioms-result.json')['log_sha256'] == digest(OLD + '-axioms.txt')
    write(PREFIX+'-baseline.json', baseline)
    results = []
    for p in MODULES:
        result = run(['lake', 'env', 'lean', '-DautoImplicit=false', p],
                     PREFIX+'-'+Path(p).stem+'-focused.txt')
        assert not Path(result['log']).read_bytes().strip()
        result.update(module=p, source_sha256=digest(p))
        results.append(result)
        print('Checked '+p, flush=True)
    write(PREFIX+'-focused-results.json', results)
    ds = declarations()
    names = [('Hindman168.FiniteMass.' if 'namespace Hindman168.FiniteMass' in read(p) else 'Hindman168.')+name for p, values in ds.items() for _, name in values]
    assert len(names) == len(set(names))
    root, registry = read('Hindman168.lean'), read('Verification.lean')
    for p in MODULES:
        line = 'import '+p[:-5].replace('/', '.')
        assert line not in root.splitlines()
        root += '\n'+line+'\n'
    for name in names:
        assert '#print axioms '+name not in registry.splitlines()
        registry += '\n#print axioms '+name+'\n'
    Path('Hindman168.lean').write_text(root, encoding='utf-8')
    Path('Verification.lean').write_text(registry, encoding='utf-8')
    write(PREFIX+'-registration.json', dict(modules=MODULES, names=names, declarations=ds))


def check():
    baseline = obj(PREFIX+'-baseline.json')
    changed = [f['path'] for f in baseline['files'] if digest(f['path']) != f['sha256']]
    assert changed == ['Hindman168.lean', 'Verification.lean']
    own = sorted(Path('Hindman168').glob('*.lean'))
    pnt = sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
    assert {p.as_posix() for p in own} == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', read('Hindman168.lean'), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {p.with_suffix('').as_posix().replace('/', '.') for p in own}
    ds = declarations()
    names = [('Hindman168.FiniteMass.' if 'namespace Hindman168.FiniteMass' in read(p) else 'Hindman168.')+name for p, values in ds.items() for _, name in values]
    assert names == obj(PREFIX+'-registration.json')['names']
    focused = obj(PREFIX+'-focused-results.json')
    assert [x['module'] for x in focused] == MODULES
    for r in focused:
        assert r['terminal'] and r['exit_code'] == 0
        assert r['command'] == ['lake', 'env', 'lean', '-DautoImplicit=false', r['module']]
        assert r['source_sha256'] == digest(r['module'])
        assert r['log_sha256'] == digest(r['log']) and not read(r['log']).strip()
    for p in own+pnt+[Path('Hindman168.lean'), Path('Verification.lean')]:
        code = helpers.lean_code(read(p))
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b', code), p
        assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b', code, re.M), p
    for p in MODULES:
        assert not re.search(r'\b(?:set_option|setOptions|instance|structure)\b', re.sub(r'\[local instance(?: \d+)?\]', '', helpers.lean_code(read(p))))
        assert (Path('.lake/build/lib/lean')/Path(p).with_suffix('.olean')).stat().st_mtime_ns >= Path(p).stat().st_mtime_ns
    for kind in ['build', 'axioms']:
        r = obj(PREFIX+'-'+kind+'-result.json')
        assert r['terminal'] and r['exit_code'] == 0 and r['log_sha256'] == digest(r['log'])
        assert not re.search(r'(?:warning:|error:)', read(r['log']))
    previous, actual = helpers.reports(OLD+'-axioms.txt'), helpers.reports(PREFIX+'-axioms.txt')
    registered = re.findall(r'^#print axioms (\S+)', read('Verification.lean'), re.M)
    assert len(registered) == len(set(registered)) == len(actual)
    assert set(registered) == set(actual) and set(actual)-set(previous) == set(names)
    assert all(actual[n] == v for n,v in previous.items())
    assert all(v <= helpers.ALLOWED for v in actual.values())
    assert helpers.run(['git','-C','.lake/packages/mathlib','rev-parse','HEAD']) == baseline['mathlib_commit']
    assert helpers.run(['git','-C','../reference-pntplus','rev-parse','HEAD']) == baseline['pntplus_commit']
    assert 'version 4.32.2,' in helpers.run(['lake','env','lean','--version'])
    fixed = obj(OLD+'-preprint-local-check.json')
    assert len(fixed['sections']) == len({s['path'] for s in fixed['sections']}) == 6
    for section in fixed['sections']:
        data = (Path('E:/codex-build/math')/section['path']).read_bytes().replace(b'\r\n',b'\n')
        pinned = subprocess.run(['git','-C','E:/codex-build/math','show',fixed['fixed_openai_math_commit']+':'+section['path']], capture_output=True, check=True).stdout.replace(b'\r\n',b'\n')
        assert data == pinned and hashlib.sha256(data).hexdigest() == section['normalized_sha256']
    files = [dict(path=f['path'],sha256=digest(f['path'])) for f in baseline['files']]
    files += [dict(path=p,sha256=digest(p)) for p in MODULES]
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)',read(PREFIX+'-build.txt'))
    assert len(jobs) == 1
    summary = dict(project_modules=len(own),pntplus_modules=len(pnt),build_jobs=int(jobs[0]),
        selected_axiom_reports=len(actual),new_declarations=len(names),
        new_theorems=sum(k in {'theorem','lemma'} for vs in ds.values() for k,_ in vs),
        new_definitions=sum(k in {'def','abbrev'} for vs in ds.values() for k,_ in vs),
        retained_proof_sources_unchanged=True,retained_axiom_sets_unchanged=True,
        standard_axioms_only=True,full_target_proved=False,independent_kernel_replay=False)
    return baseline,files,summary,fixed


def record():
    baseline,files,summary,fixed = check()
    review = dict(date='2026-10-12', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: ACTUAL Fourier pair derivative and diagonal-center descent, compact bounded family and exact original shifted pair polynomial samples; rational filtered geometry/canonical pair-factor Haar/nonzero-frequency quantitative Leibman/full prize theorem open')
    manifest=dict(baseline)
    manifest.update(date='2026-10-12',files=files,hindman_module_count=summary['project_modules'],
        source_scan_module_count=summary['project_modules']+summary['pntplus_modules'],
        selected_axiom_report_count=summary['selected_axiom_reports'],build_job_count=summary['build_jobs'],
        build_log=PREFIX+'-build.txt',axiom_log=PREFIX+'-axioms.txt',
        proved_components=baseline['proved_components']+COMPONENTS,
        last_round=dict(classification='PROGRESS',new_module_count=len(MODULES),
            new_theorem_count=summary['new_theorems'],new_selected_report_count=summary['new_declarations'],
            retained_proof_sources_changed=False,root_and_registry_changed=True,
            review_file=PREFIX+'-review.json',remaining=REMAINING))
    audit=read('AUDIT.txt'); marker='Remaining proof work:'
    assert audit.count(marker)==1 and audit.split(marker)[1].strip()==baseline['last_round']['remaining']
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-12 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n'+Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    write(PREFIX+'-review.json',review); write(PREFIX+'-checks.json',summary)
    write(PREFIX+'-preprint-local-check.json',fixed); write('verification-manifest.json',manifest)
    print(json.dumps(summary))


if __name__ == '__main__':
    mode=sys.argv[1]
    if mode=='prepare': prepare()
    elif mode=='build': write(PREFIX+'-build-result.json',run(['lake','build'],PREFIX+'-build.txt'))
    elif mode=='axioms': write(PREFIX+'-axioms-result.json',run(['lake','env','lean','Verification.lean'],PREFIX+'-axioms.txt'))
    elif mode=='record': record()
    elif mode=='recheck':
        _,files,summary,_=check()
        assert obj('verification-manifest.json')['files']==files
        assert obj(PREFIX+'-review.json')['verified']==summary
        print(json.dumps(summary))
    else: raise ValueError(mode)
