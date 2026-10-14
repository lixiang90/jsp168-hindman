"""Audit rational conjugated lattices and the actual kernel orbit maps.

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

PREFIX = 'round-rough-binomial-obstruction-transfer'
OLD = 'round-rough-box-character-translation'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughBinomialDenominator.lean', 'Hindman168/RoughBinomialTriangularCoefficients.lean', 'Hindman168/RoughBinomialClearedExpansion.lean', 'Hindman168/RoughBinomialCoefficientBudget.lean', 'Hindman168/RoughBinomialToMonomial.lean', 'Hindman168/RoughBinomialCubeTranslation.lean', 'Hindman168/RoughBinomialCubeScale.lean', 'Hindman168/RoughNativeCharacterMultiplier.lean', 'Hindman168/RoughNativeBinomialObstruction.lean']
COMPONENTS = ['RoughBinomialDenominator defines actual multivariate falling, binomial and integer denominator-cleared polynomials. It proves that multiplication by (q!)^(number of spatial variables) is exactly the real coefficient map of the specified integer polynomial, and that the real binomial polynomial evaluates to products of natural binomial coefficients.', 'RoughBinomialTriangularCoefficients proves coordinatewise degree bounds for actual falling and cleared polynomials. A cleared coefficient vanishes whenever its output multiindex is not coordinatewise bounded by its input multiindex.', 'RoughBinomialClearedExpansion proves equality of the actual denominator-cleared polynomial expansion and exact integer linear combinations for all its positive coefficients. The separate scalar constant contributes nothing to positive-degree coefficients.', 'RoughBinomialCoefficientBudget constructs a positive finite matrix budget depending only on degree and finite spatial type. It bounds modulo-one errors of all fixed-support integer coefficient combinations without dependence on scalar coefficients, using triangularity and Z >= 1 to retain the output degree exponent.', 'RoughBinomialToMonomial constructs the positive natural multiplier and proves positive ordinary monomial coefficient bounds for the actual polynomial from an exact binomial expansion and its modular coefficient estimates. It covers degrees greater than q by actual vanishing from totalDegree, so its conclusion applies to all positive multiindices.', 'RoughBinomialCubeTranslation combines denominator clearing with signed integer inverse translation. The resulting monomial coefficient budget is independent of coefficients and allows cube origins of either sign bounded by C*Z.', 'RoughBinomialCubeScale transfers the equal-cube coefficient scale N to Z when N >= lam*Z for a fixed positive lam <= 1. The factor lam^(-q) is uniform in all contributing degrees. It combines this with the binomial clearing and inverse translation.', 'RoughNativeCharacterMultiplier proves exact real scalar multiplication of the actual vector and spatial scalar polynomial projections. Integer multiplication preserves character integrality on the actual native lattice, and positive integer multiplication preserves nonvanishing on a specified vector.', 'RoughNativeBinomialObstruction derives the spatial total degree bound from the actual vector logarithm polynomial, and connects a translated binomial coefficient obstruction directly to ordinary coefficients of the actual multiplied native scalar character projection.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The full algebraic coefficient transfer from an exact binomial cube obstruction to ordinary coefficients of the actual multiplied native scalar projection is now proved: fixed integer denominator clearing, triangularity, a uniform finite coefficient budget, cube scale conversion and signed inverse translation. Exact binomial representation and its modular obstruction remain explicit inputs; this does not establish the equal-side quantitative Leibman theorem or produce an obstructing character from failed equidistribution. Still prove the equal-side quantitative Leibman input, actual integer equal-cube tiling with boundary fraction estimates, a uniform finite nonzero horizontal character list and stretched-filtration applicability; assemble these into the corrected arbitrary-box obstruction. Connect finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
    review = dict(date='2026-10-11',classification='PROGRESS',full_target_proved=False,
        application_review=COMPONENTS+['The denominator multiplier is the fixed natural number (q!)^(card spatial type), including q = 0 and an empty spatial type. It is proved positive. Coordinate degree bounds imply each input coordinate is <= q on the fixed total-degree support, supplying the factorial divisibility hypotheses.', 'The cleared polynomial is defined over integers before taking its real coefficient map. Integer coefficients therefore follow from the exact equality, rather than from a rounded approximation or a real-weight modular estimate.', 'The binomial polynomial equals the usual product of binomial coefficients at natural integer sample points, using installed mathlib falling Pochhammer evaluation. The conversion assumes equality of actual real multivariate polynomials, not merely equality on a finite set of samples.', 'Triangularity is coordinatewise, not only a comparison of total degree: a contributing input exponent must dominate every output coordinate. The degree bound is proved for all q and inputs, even when the factorial divisibility hypothesis does not hold; only clearing equality needs divisibility.', 'The finite coefficient matrix budget sums absolute integer coefficients over fixed input and output supports and is at least one. Each row is bounded by this budget. It is independent of scalar coefficients, cube size, sampling length, cube origin and the actual support of a chosen polynomial.', 'For Z >= 1, inverse powers decrease with degree. Thus errors at dominated input degrees bound errors at the output degree. Outside total degree q, actual coefficients vanish; no positive multiindex is omitted from the final estimate.', 'Cube scale conversion requires an explicit fixed positive lam <= 1 and N >= lam*Z. It does not assert that such a cube exists in the original integer box. The lam^(-q) factor is coefficient-independent.', 'Signed inverse translation is applied to the actual cleared polynomial, whose degree is bounded by that of the original polynomial. Exact affine substitution on constants is proved explicitly, and its inverse recovers original coefficients.', 'Native character multiplication is equality of actual scalar projections, derived by induction on the vector polynomial terms and then the option-variable equivalence and evaluation coefficient map. Lattice integrality and nonvanishing are proved separately; character existence and a uniformly finite list are not inferred from these algebraic identities.', 'The native spatial degree bound uses support inclusion under the coefficient evaluation map and the existing weighted option-variable support bound, so it is derived from actual vector polynomial degree rather than a separate scalar premise.', 'The final native obstruction transfer still assumes an exact translated binomial expansion and its modular coefficient estimates. It neither assumes nor proves quantitative Leibman as an axiom. Actual cube selection, boundary mass estimates, filtered polynomiality and the analytic character existence input remain open.', 'The primary Green--Tao expanded erratum arXiv:1311.6170v3 explicitly repairs the equal-side case and allows deleting the small-side alternative there. Unrestricted unequal-side equidistribution is not used. Primary PDF inspection is additional author-side mathematical review, not a formal import or an independent Lean replay.', 'All retained proof source hashes and transitive axiom sets are unchanged. Focused autoImplicit=false checks, full build, standard-only selected axiom reports and six pinned primary paper sections are checked before recording progress.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions exact binomial denominator clearing, uniform coefficient budget, cube-scale inverse translation and native character multiplication')
    manifest=dict(baseline)
    manifest.update(date='2026-10-11',files=files,hindman_module_count=summary['project_modules'],
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
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-11 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
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
