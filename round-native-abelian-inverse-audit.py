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

PREFIX = 'round-native-abelian-inverse'
OLD = 'round-mv-binomial-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeHorizontalTorusProjection.lean', 'Hindman168/NativeAbelianTorusEquivalence.lean', 'Hindman168/NativeAbelianMetricTorus.lean', 'Hindman168/UnitTorusCompactObservableSelection.lean', 'Hindman168/TorusMvCompactObservableInverse.lean', 'Hindman168/NativeAbelianTorusHaar.lean', 'Hindman168/NativeHorizontalTorusFunctional.lean', 'Hindman168/NativeAbelianMvPolynomialInverse.lean']
COMPONENTS = ['ACTUAL original filtered horizontal coordinates modulo one define a continuous SURJECTIVE group-to-torus factor, with multiplicativity/additivity, inverse, lattice-zero and true coset descent. Original Gamma need not be normal. No coordinate surjectivity or lattice image assumption is introduced.', 'Original nilpotencyClass<=1 implies horizontal layer start equals actual full model dimension; ALL original lattice indices are horizontal. Actual torus kernel equals ORIGINAL Gamma using the retained true filtered diffeomorphism lattice iff. Actual original coset map is injective and compact-to-Hausdorff continuity gives a genuine abelian quotient homeomorphism.', 'Genuine homeomorphism is transported into the SPECIFIED original compatible metric via actual IsOpenQuotientMap and proved topology equality. Actual original metric quotient is compact. The entire original unit Lipschitz observable family has COMPACT continuous sup-function pullback. No Lipschitz property of the homeomorphism is assumed.', 'Actual uniform finite Fourier approximation and genuine nonzero bounded integer mode selection are proved for EVERY FIXED COMPACT torus observable family, with arbitrary finite target index type. The genuine original-cube scalar inverse then yields a full SAME-character polynomial inverse on EVERY positive N for the fixed family. Constants precede polynomial, length and observable.', 'EXPLICIT normalized product circle Haar is pushed through the actual inverse metric homeomorphism to a measure on the ORIGINAL abelian quotient with explicit Borel measurable space. Actual probability normalization, true coordinate pushforward, integral change-of-variables, original-group action equivariance and original-group translation invariance are proved. No default volume or invariant native measure is assumed.', 'ACTUAL integer mode vector gives a CONTINUOUS LINEAR functional on the ORIGINAL real Lie model by actual filtered-basis coordinates. Genuine nonzero, kills-commutator and ORIGINAL Gamma-integral properties are proved. True fixed original basis operator norm budget bounds its norm by integer l1 size; true ORIGINAL vector polynomial projection is the sum of the SAME coordinate polynomial projections.', 'COMPLETE genuine native ABELIAN multiparameter polynomial observable inverse is proved with ORIGINAL quotient, SPECIFIED compatible metric, EXPLICIT normalized invariant measure, ORIGINAL vector polynomial/degree and EVERY positive original cube length. ACTUAL bounded nonzero continuous-linear lattice-integral horizontal character controls EVERY original positive monomial coefficient with the SAME character. No native inverse, character or metric Lipschitz bridge assumed.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. COMPLETE genuine scalar TARGET-circle multiparameter polynomial phase/observable and large-box all-coefficient small-value inverses are now proved for every fixed input dimension and degree. COMPLETE genuine standard HIGHER-DIMENSIONAL TARGET TORUS monomial-coefficient observable inverse is now proved for every fixed target/input dimension and degree, on every positive original N, with an ACTUALLY produced bounded nonzero integer horizontal character and true continuous lattice-integral real character. General native/nonabelian one-parameter nilsequence inverse remains open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery IH is now GENUINELY discharged by the proved full natural-degree scalar small-value induction. The full scalar multiparameter phase and arbitrary-observable inverses now GENUINELY construct ALL original nonconstant coefficient estimates on EVERY positive N without any inverse existence hypothesis. Genuine multivariable O(eps) small-value refinement includes original constant and eps=0 on original sufficiently large cubes, and full natural degree induction is closed. Actual full multivariable monomial-to-binomial transformation, original rough-box basis expansion and genuine same-character scalar/standard-target-torus binomial inverses are now proved, including scalar constant/zero-tolerance small-value input. Next native/nonabelian orbit-equidistribution quantitative Leibman input; finish native general polynomial/difference compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target. Distinguish the remaining nonabelian orbit-equidistribution/quantitative Leibman input from the separate HasNativePeriodicIntervalInverse finite-list interval Gowers-to-nilsequence correlation existence input; neither that Gowers inverse nor HasAlignmentMonomialRecurrence is discharged by the standard torus result. COMPLETE native ABELIAN original-metric multiparameter monomial inverse is now genuinely proved, with original quotient homeomorphism, explicit normalized translation-invariant Haar and compact-family Fourier transfer, and ACTUAL continuous-linear original lattice-integral horizontal character/operator budget. Next transfer native binomial coefficient form and actual finite native obstruction grid, then NONABELIAN orbit-equidistribution quantitative Leibman induction. General native/nonabelian inverse, SEPARATE interval Gowers correlation inverse and full StrongConjecture remain open.'

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
        application_review=COMPONENTS+['Quantifier review: fixed data D,n,d,delta precede the compact native family, finite Fourier family, mode budget and scalar inverse bound; they precede ALL Q,p,N,F. Every positive original N is retained. No assumed orbit discrepancy, invariant probability, coordinate inverse, Fourier mode or horizontal character exists at the root.', 'Boundary review: target dimension zero is supported; the unit torus is a point, so bad probability discrepancy on a nonempty cube is impossible and no nonzero character is falsely produced. Input dimension zero and degree zero are retained by the actual finite cube and true scalar inverse. No positive-dimension hypothesis is silently introduced.', 'The original vector polynomial is a finite list of genuine real multivariable polynomials times original E vectors, with true degree bound on each component. Every original coordinate projection has the same bounded degree. The original Q wrapper uses exact original global log(Q)=roughVectorMvEval(p), then exp(log(Q))=Q; samples are ORIGINAL Q at integer real casts, not replacement coefficients or changed lengths.', 'Operator norm is bounded by the FIXED original basis operator budget times A. This is a genuinely proved native norm bound; the new root does not yet claim a common natural A for operator norm, original coefficient bound, binomial bound and fixed native grid. The immediate next bridge may enlarge A by ceiling, keeping the SAME original character.', 'The new root is for NativeNilmanifoldData 1 and the actual UNIT native Lipschitz observable family. It proves native ABELIAN MONOMIAL form. Native binomial/finite-grid and arbitrary fixed B/L observable normalization remain next steps; native NONABELIAN quantitative Leibman and full StrongConjecture remain unproved. No full prize or publication completion is claimed.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: COMPLETE actual native abelian original-metric equal-cube observable inverse, original normalized invariant measure, compact-family Fourier reduction and actual original continuous-linear horizontal character; nonabelian and full prize target open')
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
