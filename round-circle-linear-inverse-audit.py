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

PREFIX = 'round-circle-linear-inverse'
OLD = 'round-leibman-common-character'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/PolynomialSmallValueShortBoxCounterexample.lean', 'Hindman168/UnitCirclePhaseDistance.lean', 'Hindman168/UnitCircleGeometricMean.lean', 'Hindman168/CompactUnitLipschitzObservables.lean', 'Hindman168/UnitCircleUniformFourierApproximation.lean', 'Hindman168/UnitCircleOrbitDiscrepancy.lean', 'Hindman168/UnitCircleLinearInverse.lean']
COMPONENTS = ['The actual real polynomial sqrt(2)*(X-1)*(X-2) has actual degree two and is zero at every actual integer sampling point 1<=n<=2. Its constant value 2*sqrt(2) is irrational. Every positive natural multiple has positive actual modular norm. For every fixed positive multiplier/error budget B, a sufficiently small actual positive eps<1/40 makes every positive q<=B fail the constant O(B*eps) conclusion, despite exact zeros on the full original sampling box.', 'For the genuine canonical character AddCircle.toCircle on the actual unit additive circle, 4*norm(x mod 1)<=norm(character(x)-1). A true nearest-integer representative, the genuine sine norm identity and the true sine lower bound prove this estimate. Actual natural multiples map to actual complex powers.', 'The actual complex geometric sum times the actual character distance has norm<=2, including resonant characters. Thus N*norm(actual N-term phase mean)*norm(x mod 1)<=1/2. Actual phase mean>=delta>0 gives actual norm(x mod 1)<=1/(2*delta*N), with N genuinely positive.', 'The genuine family of continuous complex observables with true Lipschitz constant<=1 and pointwise norm<=1 is compact. Its image in the actual pointwise function space is a closed subset of the product of true compact closed unit disks. True common Lipschitz control gives equicontinuity, and genuine Arzela-Ascoli transfers this to the continuous-map topology.', 'The genuine pinned Fourier linear-span density gives an actual finitely supported Fourier approximation to every continuous circle observable. Compactness yields one fixed finite family approximating ALL unit Lipschitz observables to any fixed positive eps. This family is chosen before actual orbit coefficients and length. Actual Haar integrals of Fourier modes are 1 for zero frequency and 0 otherwise, proved by genuine Haar translation.', 'The actual finite linear orbit average minus the actual normalized Haar integral is a genuine complex linear map, with norm bound 2 on each actual observable. True mode evaluation identifies every nonzero Fourier discrepancy with the actual finite phase mean; the constant mode cancels exactly for positive N.', 'A genuine scalar linear torus inverse is proved without any assumed per-orbit character or approximation input. For each fixed delta>0, one fixed positive natural A works for all actual slopes, positive lengths and all actual bounded unit Lipschitz observables. Average discrepancy>=delta produces a nonzero actual integer k with natAbs(k)<=A and N*norm(k*x mod 1)<=A. Genuine Haar translation invariance gives the SAME uniform result for arbitrary affine offsets. Only fixed-data bounds are asserted, not a power-law dependence on delta.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. This does not prove the genuine higher-degree scalar polynomial inverse, higher-dimensional torus inverse, or general one-parameter nilsequence quantitative character existence and binomial coefficient smoothness. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Next prove genuine modular interval-hit counting and linear strong recurrence using the actual analytic base, then higher-degree scalar inverse/small-value estimates and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The short-box example is an actual real Polynomial, with actual degree two proved from monic linear factors and a nonzero actual leading scalar. Its real evaluations at the actual integer endpoints 1 and 2 are exactly zero. The irrational constant gives strictly positive actual modular norm for every positive q. A true finite minimum over 1<=q<=B chooses eps>0 before checking ALL these multipliers. This rules out any finite uniform multiplier and O(eps) constant budget, not merely one unsuccessfully chosen multiplier. Negative integer multipliers have the same modular norm as their positive absolute values. At delta=1/4 the full two-point box is more than dense enough and eps<delta/10. The printed unrestricted Proposition 2.3 scope therefore cannot be introduced as a formal theorem.', 'The canonical circle character is the actual library AddCircle.toCircle, not an arbitrary formal phase. Its distance estimate uses the actual nearest-integer representative u=x-round(x), actual |u|<=1/2 and genuine sine lower bound. Actual quotient equality is proved before replacing representatives. No false arbitrary real scalar map on the quotient circle is asserted.', 'The genuine ring geometric-sum identity gives norm(sum)*norm(z-1)<=2 from actual |z|=1. Multiplication by the character-distance lower bound proves the actual mean inequality without dividing by a possibly zero character distance. N=0 is handled separately; the inverse conclusion divides only by true positive N and delta. Resonant phases are included.', 'The pointwise observable image is exactly the true Lipschitz/norm-constrained function set, including continuity from true Lipschitz control. Its closedness and actual product compactness are proved, followed by actual equicontinuity and Arzela-Ascoli. On the actual compact unit circle, this is the uniform/supremum norm topology used for approximation. No compactness assumption about polynomial coefficient families is added.', 'Actual Fourier span density is the genuine pinned mathlib span_fourier_closure_eq_top. Span membership is converted into a true Finsupp coefficient sum. The actual compact observable family has a finite ball cover; approximating each center gives one fixed finite Fourier coefficient family for every later observable. The family may depend on delta, exactly as allowed by the OpenAI Section 06 fixed-data constant; no polynomial rate is claimed.', 'Actual Haar integration of nonzero modes is proved via a true half-period translation negating that mode. The actual Haar measure is normalized probability. True integrability of continuous functions on the compact circle proves complex linearity of the actual average discrepancy. The actual pointwise supremum bound and actual probability integral bound give norm<=2*norm(F). Constant cancellation is only used at positive N.', 'The inverse chooses the finite Fourier family before slope, offset, N and observable. One global positive B bounds coefficient norm sums, one natural K bounds all frequencies. If every nonzero mode average were too small, the true norm-of-sum estimate would contradict the actual approximating polynomial discrepancy. This avoids selecting a common complex phase. The actual selected nonzero frequency then satisfies the genuine geometric mean inverse. Rounding 2*B/delta and the fixed K gives one actual positive A for all orbits. Arbitrary affine offset is removed by a true circle translation, which preserves the original Lipschitz/norm constraints and true Haar integral.', 'Primary sources reviewed: https://arxiv.org/pdf/1311.6170v3 Section 2 Proposition 2.3 and Section 3 large-N application; https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Section 3 Proposition 3.1 and Lemma 3.2. The main corrected equal-cube target does not require O(eps) control on arbitrarily short boxes. The scalar affine linear analytic inverse is now genuinely proved, but the complete nilsequence inverse and prize target are not. All six pinned OpenAI sections and prior proof source hashes/axiom sets remain unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions corrected equal-cube analytic input: genuine scalar affine linear torus inverse, uniform Fourier approximation, actual geometric phase bound and proved short-box scope counterexample; full nilsequence inverse remains open')
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
