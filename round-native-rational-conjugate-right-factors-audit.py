"""Audit actual conjugated source, right quotient/native geometry, Haar and observable transport.

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

PREFIX = 'round-native-rational-conjugate-right-factors'
OLD = 'round-native-rational-small-rational-factors'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeConjugateCanonicalProbability.lean', 'Hindman168/NativeConjugateFourierObservable.lean', 'Hindman168/NativeConjugateHorizontalCharacter.lean', 'Hindman168/NativeConjugateNilmanifoldData.lean', 'Hindman168/NativeConjugateRightObservable.lean', 'Hindman168/NativeRationalConjugateFiltration.lean', 'Hindman168/NativeRationalDegreeTwoDenseRightFactors.lean', 'Hindman168/NativeRationalDenseRightFactors.lean', 'Hindman168/NativeRationalKernelConjugateSource.lean', 'Hindman168/NativeRationalNonlinearRightFactors.lean', 'Hindman168/NativeRationalResidueFiltration.lean', 'Hindman168/RoughConjugateRightCosetEquiv.lean', 'Hindman168/RoughConjugateRightCosetMetric.lean', 'Hindman168/ScalarUnitPolynomialInverse.lean']
COMPONENTS = ['TRUE scalar-to-Unit Mv conversion preserves actual degree/evaluations/coefficients. ACTUAL variable conjugation gamma*gK*gamma^-1 is constructed by native BCH/Picard products then genuine aggregate coefficient collection/zero trimming. Old L weights, EXACT horizontal scalar projection and actual affine degree prove TRUE smaller-kernel weights and original degree ell. The conjugating direction itself is NOT assumed kernel-filtered.', 'TRUE original group samples now factor in CORRECT order g=epsilon*gK_conjugated*gamma for ALL real inputs. Actual finite original right-coset representatives of gamma therefore apply to ACTUAL whole original samples by original LEFT action, with the same bounded error factor. SAME original nonzero Fourier signal now yields full original inverse OR these actual right-ordered factors/whole-sample residues, retaining complete Q/P(1)/higher P tables, same common bounded positive M, same dense V/relative/bracket bounds and actual strict nonlinearity drop. General degree has ONLY full lower-degree inverse premise; degree two has NO child inverse premise.', 'GENUINE right-coset equivalence/homeomorphism from G/(rho Gamma rho^-1) to ORIGINAL G/Gamma sends [x] to [x*rho]. Its actual inverse, both identities, original LEFT equivariance and continuity are PROVED. No arbitrary right action on ORIGINAL nonnormal quotient is asserted. Original compatible metric is ACTUALLY pulled back, true isometry equivalence and the new open quotient map/topology are PROVED.', 'TRUE conjugated native nilmanifold data copies ORIGINAL model/manifold/group and PROVED conjugate lattice discreteness/compactness, with actual transported compatible metric. ACTUAL rational conjugation preserves original rational log span, so EVERY true original rational Lie filtration transports to SAME layers on actual conjugated data. EVERY genuine finite rational representative Exp((m/M)*y) receives the true smaller rational filtration, actual source weights and SAME strict natural nonlinearity drop.', 'ACTUAL conjugated native canonical probability pushes through true right-coset homeomorphism to ORIGINAL canonical probability. Measurability, probability, actual left equivariance/invariance and PROVED uniqueness of invariant probability establish genuine Haar agreement and true integrals for every original function. No assumed common Haar normalization or measure-identification oracle is used.', 'ACTUAL continuous original observables pull back through true right-coset isometry with PROVED unit Lipschitz preservation and canonical integral transport. Actual frozen LEFT parameter plus original terminal Fourier projection gives a GENUINE compact continuous-observable family on conjugated native data, norm <=ONE for original unit inputs, ZERO canonical Haar mean for original nonzero mode, and ACTUAL group-sample evaluation formula. Arbitrary compatible-metric left actions are NOT asserted uniformly spatially Lipschitz; no freezing error or child correlation is assumed.', 'ACTUAL original horizontal logarithmic characters are PROVED conjugation invariant. TRUE nonzeroness, Lie commutator annihilation and original lattice integrality hold iff on actual conjugated lattice. A bounded genuine child horizontal character consequently belongs to ORIGINAL finite horizontal grid with SAME norm budget. Complete source-table/correlation induction transport remains open.']
REMAINING = 'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Prize target remains full original positive distinct rapidly separated monochromatic finite sums/products. Existing native inverse branches, complete Q second tables, actual nearest-integer small/rational split, strict kernel nonlinearity descent, original lattice periods/error variation are retained. ACTUAL rational variable conjugation now constructs a TRUE weighted smaller-filtration source and exact right-ordered real factorization g=epsilon*gK_conjugated*gamma. SAME Fourier packet keeps full original inverse OR actual whole-sample finite right representatives, all complete Q/higher P/P(1)/original dense V bounds and genuine strict descent. TRUE conjugated right-coset homeomorphism/metric/native data/rational filtration and ACTUAL canonical Haar probability/integral transport are proved. Frozen LEFT parameter / original nonzero Fourier projection yields actual compact bounded zero-Haar-mean continuous-observable families on TRUE conjugated native data; unit right-pullback and original horizontal/grid character transport are proved. This does NOT establish actual freezing error or large child correlation. Remaining: choose finite simultaneous highest-direction/lattice-power/period/geometry budgets BEFORE all raw sources; actual compact-parameter action error from genuine uniform continuity, short original residue progression with large mean and length>=tau*N, correct continuous-family to unit-observable inverse detection, actual translated-progression/source coefficient/denominator clearing back to BOTH complete raw ORIGINAL tables, and genuine degree+nonlinearity induction. P first/full diagonal alternative, all small-N original inverse branches, corrected multivariate inverse, separate interval Gowers correlation inverse, rough progressions, cube/Alignment and final StrongConjecture remain OPEN. Fixed-data existential budgets are NOT explicit delta-power laws. Only true positive exponential lattice powers are asserted, not Exp(y) lattice membership. Author build/hash/axiom/source review is NOT independent kernel replay or peer review. Repaired source slab estimate is NOT an unavoidable obstruction. Public repository/PR/prize milestone has NOT been reached.'

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
        reference_scope='OpenAI quantitative Leibman route; ACTUAL conjugated smaller source, correct right quotient/native data/Haar/zero-mean compact observable families; freezing/short-progression correlation and full target remain open')
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
