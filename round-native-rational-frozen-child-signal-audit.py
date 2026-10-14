"""Audit actual complex freezing, genuine short progression and smaller-filtration UNIT child signal.

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

PREFIX = 'round-native-rational-frozen-child-signal'
OLD = 'round-native-rational-conjugate-right-factors'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/BalancedComplexResidueGeometry.lean', 'Hindman168/BalancedComplexResidueSelection.lean', 'Hindman168/FiniteComplexFiberSelection.lean', 'Hindman168/FiniteComplexSampleStability.lean', 'Hindman168/FinitePositiveThresholdMinimum.lean', 'Hindman168/IntegerResidueProgressionEnumeration.lean', 'Hindman168/NativeCompactFamilyUnitDetection.lean', 'Hindman168/NativeConjugateFourierUnitDetection.lean', 'Hindman168/NativeRationalErrorFourierFreezing.lean', 'Hindman168/NativeRationalFiniteResidueUnitDetection.lean', 'Hindman168/NativeRationalFourierScalarFreezing.lean', 'Hindman168/NativeRationalFrozenProgressionMean.lean', 'Hindman168/NativeRationalFrozenProgressionUnitSignal.lean', 'Hindman168/NativeRationalFrozenResidueMean.lean', 'Hindman168/NativeRationalIntegerResidueCoset.lean', 'Hindman168/NativeRationalNonlinearityChildSignal.lean', 'Hindman168/NativeRationalProgressionSource.lean', 'Hindman168/NativeRationalRightSampleFreezing.lean', 'Hindman168/ScalarNonlinearIntegerPeriod.lean']
COMPONENTS = ['ACTUAL COMPLEX original terminal Fourier signal has a PROVED uniform scalar LEFT-action modulus on bounded real parameters BEFORE every raw polynomial/sample. Genuine compact original quotient times actual compact UNIT observable subtype, original Fourier function-space continuity and true continuous evaluation/action supply the modulus. No spatial Lipschitz Fourier projection or uniformly spatially Lipschitz action is assumed.', 'TRUE original REAL error coefficient/value/variation bounds now prove genuine COMPLEX signal freezing on a fixed positive fractional short interval. Radius precedes ALL raw E/M/N/samples. Actual right-ordered group identity and original right-coset residue equality PROVE actual approximation by the genuine frozen observable on TRUE conjugated native data, with correct group order and original samples.', 'An ACTUAL finite complex sample partition has a NONEMPTY fiber mean norm at least the original mean norm, using TRUE cardinal weights and exact finite fiber sums. Genuine balanced interval/residue partition of ALL original 0<=n<N samples yields a true large cell with length>=N/(4*K*period) once N>=4*K*period. True original range/short-distance/congruence are PROVED. No equal cell size, phase alignment or discarded-tail signal is assumed.', 'ACTUAL integer polynomial divisibility proves the rational-factor original right coset CONSTANT for ANY two congruent original integer inputs, including negative differences. Real error freezing on the selected true cell and actual complex finite-mean error stability PROVE a GENUINELY LARGE frozen child mean >delta/2 and ZERO child canonical Haar mean, with a TRUE finite rational representative and original-scale cell length.', 'ACTUAL original residue cell is EXACTLY one affine image of standard integer interval 0<=t<T, with exact cardinal/mean and no endpoint loss. Genuine affine source substitution keeps TRUE smaller-filtration weights and original degree. Exact child native samples, actual conjugated rational filtration, strict same-degree nonlinearity loss and GENUINE large standard-progression mean are PROVED, with TRUE original-scale length and bounded frozen scalar.', 'An ACTUAL compact continuous-observable family on genuine native data has one fixed finite UNIT-Lipschitz discrepancy detector, by true compact finite Lipschitz approximation, exact normalization and actual discrepancy norm/error bounds. Actual nonzero original frozen Fourier family uses PROVED ZERO canonical Haar mean to turn the large frozen mean into discrepancy. A TRUE finite representative pool over ALL 0<M<=S, m<M*q gives ONE positive threshold BEFORE every raw source/sample/error, using actual finite minimum and true compact scalar LEFT family.', 'For ACTUAL fixed nonzero-difference/zero-pairing character, highest rational j/y/positive lattice power q, block K and ONE positive UNIT threshold are selected BEFORE every bounded M/raw p/N. Actual COMPLETE native Q coefficient bounds plus SAME original Fourier signal yield a TRUE smaller-rational-filtration source on a standard child Unit cube with GENUINELY LARGE UNIT-observable canonical discrepancy. Threshold N>=4*K*S*q and length>=N/(4*K*S*q) are fixed before all sources. Child has SAME layers as original true kernel and STRICT natural nonlinearity loss. ACTUAL error/rational source factors and exact affine child sample relation are RETAINED for future original-coefficient transport. No same-degree child inverse is assumed.']
REMAINING = 'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products remains the prize target. All prior native geometry/inverse branches, complete Q second tables, small/rational/right factors, genuine rational kernel/nonlinearity descent, correct conjugated native/Haar/observable/character transport are retained. ACTUAL COMPLEX original Fourier freezing, true balanced interval/residue complex-mean selection, constant integer rational-factor right coset, REAL freezing errors and exact standard-progression enumeration now PROVE GENUINELY LARGE zero-Haar-mean child signal with original-scale length. True affine source weights/degree/strict smaller nonlinearity and actual compact-family UNIT detection are PROVED. Finite representative pool over bounded positive M and fixed q has ONE positive threshold BEFORE all raw samples. For each ACTUAL fixed valid relative character, highest j/y/q and block/UNIT threshold precede all M/p/N: true complete Q bounds and SAME original Fourier signal give genuine standard child Unit-cube discrepancy >theta, true smaller source, length>=N/(4*K*S*q), and retained exact source factor/progression relationships. Full same-degree inverse is NOT yet proved. Remaining: finite simultaneous geometry/threshold budgeting over the original finite CHARACTER pool and explicit composition with all original native Fourier branches; actual child-character progression/translation/length/rational-denominator/REAL-error coefficient transport back to BOTH COMPLETE raw ORIGINAL tables; genuine well-founded degree+nonlinearity induction and all original small-N cases. P first/full diagonal alternative, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final StrongConjecture remain OPEN. Fixed-data existential bounds are NOT explicit delta-power laws. Only true positive exponential lattice powers are asserted, not Exp(y) lattice membership. Author build/hash/axiom/source review is NOT independent kernel replay or external peer review. Repaired source slab estimate is NOT an unavoidable obstruction. Public repository/PR/prize milestone has NOT been reached.'

def declarations():
    result = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}
    return result


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
    write(PREFIX+'-slab-certificate-result.json',run(['python','bracket-slab-volume-counterexample.py'],PREFIX+'-slab-certificate.txt'))
    Path(PREFIX+'-slab-review.json').write_bytes(Path('round-native-rational-fractional-bracket-input-slab-review.json').read_bytes())
    results = []
    saved = obj(PREFIX+'-focused-results.json') if Path(PREFIX+'-focused-results.json').exists() else []
    for p in MODULES:
        prior = next((r for r in saved if r['module']==p), None)
        if (prior and prior['terminal'] and prior['exit_code']==0
            and prior['command']==['lake','env','lean','-DautoImplicit=false',p]
            and prior['source_sha256']==digest(p)
            and prior['log_sha256']==digest(prior['log']) and not read(prior['log']).strip()):
            results.append(prior)
            print('Retained exact explicit check '+p, flush=True)
            continue
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
        code = re.sub(r'\[local instance(?: \d+)?\]', '', helpers.lean_code(read(p)))
        assert not re.search(r'\b(?:set_option|setOptions|instance)\b', code)
        structures = re.findall(r'^\s*structure\s+(\w+)', code, re.M)
        assert structures == (['NativeRationalLieFiltration'] if p.endswith('/NativeRationalLieFiltration.lean') else [])
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
        new_structures=sum(k=='structure' for vs in ds.values() for k,_ in vs),
        new_structure_generated_reports=sum(k=='structure_generated' for vs in ds.values() for k,_ in vs),
        retained_proof_sources_unchanged=True,retained_axiom_sets_unchanged=True,
        standard_axioms_only=True,full_target_proved=False,independent_kernel_replay=False)
    certificate = obj(PREFIX+'-slab-review.json')
    cr = obj(PREFIX+'-slab-certificate-result.json')
    assert cr['terminal'] and cr['exit_code']==0 and cr['log_sha256']==digest(cr['log'])
    assert cr['command']==['python','bracket-slab-volume-counterexample.py']
    assert certificate['violates_displayed_volume_bound'] and not certificate['refutes_proposition_itself'] and not certificate['unavoidable_obstruction']
    from fractions import Fraction as F
    xs = [(F(i['left']),F(i['right']),i['nearby_integer']) for i in certificate['intervals']]
    assert len(xs)==101 and sum((b-a for a,b,k in xs),F(0))==F(1,5)>F(1,200)
    assert all(xs[j][1]<xs[j+1][0] for j in range(100))
    assert all(abs(100*a-k)<=F(1,10) and abs(100*b-k)<=F(1,10) for a,b,k in xs)
    assert certificate['exact_slab_volume']=='1/5' and certificate['displayed_upper_bound']=='1/200'
    return baseline,files,summary,fixed


def record():
    baseline,files,summary,fixed = check()
    review = dict(date='2026-10-13', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='OpenAI quantitative Leibman route; actual complex freezing, original-scale short residue progression and genuine smaller-filtration Unit-cube signal; full character-pool/source-coefficient induction and final target remain open')
    manifest=dict(baseline)
    manifest.update(date='2026-10-13',files=files,hindman_module_count=summary['project_modules'],
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
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-13 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n'+Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    review.update(mathematical_review_file=PREFIX+'-mathematical-review.txt', mathematical_review_sha256=digest(PREFIX+'-mathematical-review.txt'))
    review.update(source_slab_certificate=PREFIX+'-slab-review.json',source_slab_certificate_sha256=digest(PREFIX+'-slab-review.json'),source_slab_script_sha256=digest('bracket-slab-volume-counterexample.py'))
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
