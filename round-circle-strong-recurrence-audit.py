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

PREFIX = 'round-circle-strong-recurrence'
OLD = 'round-circle-linear-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/UnitCircleNormBump.lean', 'Hindman168/UnitCircleDenseSmallValues.lean', 'Hindman168/FiniteIntegerSpanCard.lean', 'Hindman168/LinearNearestIntegerHitCount.lean', 'Hindman168/UnitCircleProgressionHitCount.lean', 'Hindman168/UnitCircleStrongLinearRecurrence.lean', 'Hindman168/UnitCircleAffineSmallValueInverse.lean']
COMPONENTS = ['The actual circle norm bump max(0,c-norm(t)) is genuinely unit Lipschitz, nonnegative and at most c. Its actual complex continuous observable is admissible for 0<=c<=1. Actual normalized Haar ball measure equals 2c for 0<=2c<=1; true support domination by a ball indicator gives actual Haar integral<=2c^2.', 'Actual cardinal density of modular small values gives the actual real bump mean lower bound, not an assumed expectation. With c=delta/4 and eps<=delta/10, actual average minus Haar has norm>=delta^2/40. The previously proved genuine affine analytic inverse supplies one fixed positive A, chosen before slope, offset, N and eps, with nonzero integer k of natAbs<=A and N*norm(k*x mod 1)<=A.', 'Actual finite natural and integer cardinalities are bounded by their actual maximum minus minimum plus one, via containment in genuine integer intervals. No spacing or counting estimate is assumed.', 'Actual integer indices in one lifted affine interval have abs(a)*card<=abs(a)+2eps. True maximum/minimum indices prove this, including zero and negative a without division. Actual nearest-integer labels have cardinality<=abs(a)*J+2eps+1. Summing the actual fibers gives abs(a)*card(hits)<=(abs(a)*J+2eps+1)*(abs(a)+2eps).', 'The original modular hit indices are genuinely partitioned by residues modulo positive q, with actual quotient indices and injective reconstruction n=n%q+q*(n/q). Subtracting the true integer multiple of round(q*x) preserves the actual circle value. Actual row counting and q*(floor(N/q)+1)<=N+q yield beta*card(hits)<=(beta*N+3q)*(beta+2eps), where beta=norm(q*x mod 1). The bound includes zero and negative nearest-integer increments.', 'Actual dense hits, actual coarse q<=A and beta*N<=A, and the explicit threshold 8A<=delta*N give N*beta<=16A*eps/delta. The genuine coarse analytic inverse produces this q; its positive natural absolute value preserves the actual circle norm. This proves genuine strong scalar linear recurrence rather than an interface assuming a character or count bound.', 'An actual small-value sample exists by actual positive density. True circle subtraction and natural-multiplier bounds give norm(q*b mod 1)<=17A*eps/delta for the SAME q as the refined slope bound. Actual ceilings choose one positive B depending only on delta. For ALL affine coefficients x,b, lengths N>=B, and 0<=eps<=delta/10, actual density>=delta yields positive q<=B with N*norm(q*x)<=B*eps and norm(q*b)<=B*eps. The actual large-box threshold is retained, including eps=0. No power-law dependence on delta is claimed.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. This does not prove the genuine higher-degree scalar polynomial inverse, higher-dimensional torus inverse, or general one-parameter nilsequence quantitative character existence and binomial coefficient smoothness. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Next prove the genuine higher-degree scalar polynomial inverse and large-box polynomial small-value estimates, higher-dimensional torus and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
    review = dict(date='2026-10-12',classification='PROGRESS',full_target_proved=False,
        application_review=COMPONENTS+['The bump is the actual circle norm and actual max operation. The normalized Haar measure is identified with true volume at period one before invoking the library closed-ball measure theorem. The integral comparison is between genuinely integrable functions. The complex discrepancy is identified with the actual real mean minus real Haar integral; taking absolute value cannot decrease the real discrepancy.', 'All quantifiers in the coarse inverse are ordered correctly: delta is fixed and one A is chosen before x,b,N,eps. The observable is constructed, its Lipschitz and pointwise bounds are proved, and the real finite mean lower bound follows from actual filtered cardinality. Dense small values are a premise about the actual samples, not an assumed inverse conclusion.', 'The hit count uses actual nearest-integer labels and actual cardinality of every fiber. The finite-cardinality bounds are proved from actual extremal indices and integer interval cardinalities. Signed increments are handled by absolute value and real arithmetic; no positivity of the slope is silently assumed and no division by beta occurs.', 'Residue rows use a true injection through n/q restricted to n%q=r. The exact modular identity subtracts the true integer (n/q)*round(q*x). The row length floor(N/q)+1 is an actual uniform upper bound, valid also at N=0. The original hit count, not the cardinality of a replacement sampling law, is summed over every residue in range q.', 'Refinement multiplies the actual density by beta>=0. The coarse upper bound and q<=A control the entire count factor by 4A. The large-N condition absorbs the term 4A*beta. This proves a division-free estimate before dividing by genuine delta>0; beta=0 and eps=0 are fully included. The constant and slope error conclusions never assert an unrestricted short-box O(eps) bound.', 'The offset proof selects a real sample from the actual dense set, uses its actual n<N and the SAME q. It bounds the true modular norm of q*b via q*(b+n*x)-n*(q*x). One B contains A and both genuine ceiling bounds 8A/delta and 17A/delta. The length threshold N>=B is fixed before coefficients and eps, and guarantees the refinement threshold. Both actual affine coefficients satisfy B*eps bounds.', 'Primary route references: OpenAI Section 06_rough_progressions; Green-Tao https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Section 3 Proposition 3.1 and Lemma 3.2; erratum https://arxiv.org/pdf/1311.6170v3 Section 2 Proposition 2.3 and Section 3 large-N application. This continuation completes the genuine affine scalar analytic and strong-recurrence base case only. All prior sources and axiom sets and six pinned OpenAI sections remain retained.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions corrected equal-cube analytic input: genuine affine scalar norm bump, Haar support control, actual interval-hit count, strong linear recurrence and large-box affine small-value inverse; higher-degree and general nilsequence inverse remain open')
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
