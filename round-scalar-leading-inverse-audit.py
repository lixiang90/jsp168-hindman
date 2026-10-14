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

PREFIX = 'round-scalar-leading-inverse'
OLD = 'round-circle-strong-recurrence'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/FinitePositiveLagReindex.lean', 'Hindman168/FiniteComplexLagEnergy.lean', 'Hindman168/FinitePositiveLagDensity.lean', 'Hindman168/ScalarPolynomialDifference.lean', 'Hindman168/ScalarPolynomialPhaseLags.lean', 'Hindman168/ScalarPolynomialLinearPhaseInverse.lean', 'Hindman168/FiniteBoundedCandidateDensity.lean', 'Hindman168/UnitCircleDensePowerInverse.lean', 'Hindman168/ScalarPolynomialLeadingInverse.lean', 'Hindman168/FinitePositiveLagShortIntervalCounterexample.lean']
COMPONENTS = ['Actual ordered sample pairs i<j are genuinely reindexed by positive lag h=j-i and original index i. A true finite sigma-set bijection proves equality of the actual triangular sum and the actual positive-lag sum, retaining the exact remaining length N-h.', 'The actual complex finite sum square equals the true diagonal norm-square sum plus twice the real sum of actual positive-lag correlations. Genuine induction and complex norm-square algebra prove the identity. Actual correlation norms are at most N-h and vanish for h>=N.', 'For true unit-bounded samples and actual mean norm>=delta>0, the explicit condition delta^2*N>=4 gives at least delta^2*N/8 actual positive lags with correlation norm>=delta^2*N/8. The proof uses the actual energy identity, diagonal bound, real-part versus norm bound and actual filtered cardinality. Each such lag has actual remaining length N-h>=delta^2*N/8 and actual normalized correlation mean>=delta^2/8.', 'The scalar polynomial difference is the actual real Polynomial Taylor translate minus the actual original Polynomial. Its actual evaluation is p(x+h)-p(x); a bound natDegree(p)<=d+1 gives natDegree(difference)<=d. The true degree-d coefficient equals (d+1)*h*p.coeff(d+1), including lower-degree and zero differences, by genuine Hasse derivative coefficients and Taylor translation.', 'The actual polynomial phase is the genuine canonical circle character of actual real polynomial evaluations. True character subtraction identifies the actual lag product with the actual polynomial difference phase. The actual dense-lag theorem supplies a genuine finite dense set T of nonzero shifts, with the SAME actual remaining lengths and genuine large lower-degree phase means.', 'For a true degree-at-most-one real polynomial, actual phase evaluation factors into the true constant unit phase and true linear orbit phase. The actual finite mean norm therefore equals the linear mean norm, and the genuine geometric inverse gives a fixed-data leading-coefficient multiplier bound. No affine phase-removal hypothesis is assumed.', 'Actual existence of positive natural candidates<=B on each member of an actual finite set yields one actual common candidate on at least card(set)/B members. A true finite union count and actual finite averaging prove the statement. In the main degree induction, the per-member existence is constructed by the induction hypothesis on the actual lower-degree polynomial and actual remaining interval.', 'True positive fractional remaining length transfers a genuine t^e error bound to an actual N^e bound. The previously proved genuine strong linear recurrence improves actual dense modular errors C/N^e to C/N^(e+1), with fixed A and M chosen before coefficients and N, for all positive e and genuine N>=M. Actual ceilings enforce epsilon<=delta/10 and the strong recurrence length threshold.', 'A GENUINE scalar Weyl leading-coefficient inverse is proved for EVERY fixed positive degree bound, by actual natural degree induction. One fixed positive A depending only on d and delta precedes every real Polynomial and positive N. Actual phase mean>=delta yields positive q<=A with N^(d+1)*norm(q*p.coeff(d+1) mod 1)<=A. The induction applies the lower-degree inverse to actual nonzero differences on their actual remaining intervals, pigeons the constructed bounded multipliers, and applies actual dense multiple strong recurrence. Actual bounded short N are handled separately by the genuine circle half-period bound. No per-polynomial multiplier, character, approximation, lag density or recurrence existence is assumed. This controls the top coefficient only, not all coefficients simultaneously.', 'An actual one-unit-sample phase mean exceeds 1/2 while every actual positive-lag zero-extended correlation is zero. The true published [N] convention at N=1 has zero positive correlations, contradicting an unrestricted positive-lag cardinal lower bound. The explicit large-N condition in the actual density theorem excludes this auxiliary scope defect; the original OpenAI route applications use sufficiently large N.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. This does not prove the genuine higher-degree scalar polynomial inverse, higher-dimensional torus inverse, or general one-parameter nilsequence quantitative character existence and binomial coefficient smoothness. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Next prove actual short arithmetic progression localization and top-coefficient stripping to obtain simultaneous nonconstant scalar coefficient control, then large-box polynomial small-value estimates, higher-dimensional torus and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The pair reindexing map (j,i)->(j-i,i) is an actual bijection of the genuine finite sigma sets; its inverse is (h,i)->(i+h,i). The memberships require 0<h<N and i<N-h. No zero lag is counted, and no replacement sampling law is used.', 'The energy identity expands genuine complex norm squares and pairs, with the actual conjugation/star identity checked before real-part summation. Correlations are true truncated sums over range(N-h), not hypothetical zero-extended full-length means. Their bound N-h follows from the actual original unit bounds at both n and n+h.', 'The large-N input delta^2*N>=4 is explicit. Actual diagonal energy<=N and correlation norms<=N give the true density inequality for the original filtered positive-lag set. The remaining-length estimate is derived from the SAME actual correlation bound. Its normalized mean uses the true positive N-h, and no full-N untruncated phase mean is substituted.', 'The true scalar difference uses Polynomial.taylor, with actual coefficient cancellation at the top degree. The next coefficient is evaluated through the genuine Hasse derivative of degree at most one. The formula is valid for arbitrary real coefficients and arbitrary signed real shift and remains true below the degree bound. The main inverse does not need a nonzero leading-coefficient assumption.', 'The polynomial phase uses the actual AddCircle.toCircle, with true norm one and true product/negative laws. Its lag product equals the phase of p(n+h)-p(n) at each actual index, so the same original dense lag set gives the actual lower-degree polynomial means on range(N-h). Degree, index, phase and length data belong to the same polynomial and shift.', 'One affine phase constant has actual norm one and factors through the genuine finite sum. The actual linear geometric inverse supplies the degree-one base. It holds for every positive N, including bounded N, and no degree-zero constant coefficient claim is made.', 'The common-multiplier selection counts the actual relation on the actual lag set. Its proof is a genuine finite union/averaging argument. In the final theorem the existence premise is discharged by the actual induction hypothesis; it is not an unproved input at the root.', 'The dense-power inverse chooses both its output bound and actual length threshold before x,N. The true lower bound N^e>=N for e>0 enforces the original epsilon restriction. The genuine strong recurrence is applied to actual n*x samples. Dividing only by positive delta and N^e, it then clears the true denominator to get N^(e+1) control.', 'The leading inverse chooses tau=delta^2/8, then the lower-degree bound B, density mu=tau/B, fixed error budget C=B/tau^(d+1)+1, the dense-power inverse bound K and threshold M0, and finally A BEFORE p and N. Actual lag h has N-h>=tau*N; the lower-degree bound on its true top coefficient transfers to N^(d+1) norm(h*q*(d+2)*alpha)<=C. A genuine common q yields actual dense n*x modular small values with x=q*(d+2)*alpha. Strong recurrence gives qPrime, and the actual output Q=qPrime*q*(d+2) is positive and bounded. The multiplier and degree factor are retained; arbitrary real coefficients and negative phases are allowed. The explicit small-N case uses Q=1 and the actual period-one half-period norm bound. Thus the top inverse covers ALL positive lengths, even though the analytic induction uses large lengths.', 'The counterexample is about an auxiliary unrestricted positive-lag density assertion, not the polynomial leading inverse, the quantitative Leibman theorem or the original prize target. No unavoidable route obstruction is claimed. Simultaneous scalar coefficient control still needs actual short arithmetic progression localization and top-coefficient stripping; the full scalar and general nilsequence inverses remain unproved.', 'Primary references: OpenAI Section 06_rough_progressions; https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Section 4, Corollary 4.2, Lemma 4.4 and Proposition 4.3; https://arxiv.org/pdf/1311.6170v3 Section 2 and Section 3. All formerly registered source hashes/axioms and all six pinned OpenAI sections remain unchanged. Checks are author-side Lean verification, not independent kernel replay or external mathematical review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions corrected equal-cube scalar analytic input: actual positive-lag density and polynomial differences, genuine all-degree Weyl leading inverse; simultaneous scalar and general nilsequence inverse remain open')
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
