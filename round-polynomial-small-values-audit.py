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

PREFIX = 'round-polynomial-small-values'
OLD = 'round-scalar-simultaneous-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/UnitCirclePolynomialDiscrepancy.lean', 'Hindman168/UnitCirclePolynomialFourierSelection.lean', 'Hindman168/UnitCirclePolynomialInverse.lean', 'Hindman168/UnitCirclePolynomialSmallValuesCoarse.lean', 'Hindman168/PolynomialSmallValueNaturalMultiples.lean', 'Hindman168/PolynomialSmallValueRescale.lean', 'Hindman168/PolynomialSmallValueConstantRecovery.lean', 'Hindman168/PolynomialSmallValuesPositiveNonconstant.lean', 'Hindman168/PolynomialSmallValuesPositive.lean', 'Hindman168/FiniteUniformErrorZero.lean', 'Hindman168/PolynomialSmallValuesInverse.lean']
COMPONENTS = ['The actual polynomial orbit finite average minus actual normalized circle Haar integral is a genuine complex linear map with true norm bound<=2*norm(F). The true nonzero Fourier mode is the actual phase of C(k)*p, and the actual constant mode cancels at genuine N>0.', 'Actual finite Fourier polynomial discrepancy and actual coefficient norm budget force an actual nonzero frequency with actual phase mean>=delta/(4B). True sum estimates prove mode existence, including actual cancellation of the zero mode, without an assumed phase/character input.', 'A COMPLETE genuine one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables is proved. The actual compact uniform Fourier family, coefficient budget and maximum frequency are chosen BEFORE the polynomial, arbitrary coefficients, N and observable. The complete actual phase inverse at min(delta/(4B),1/2)>0 yields one true multiplier for all original nonconstant monomial coefficients of C(k)*p. Its positive natural absolute-frequency product preserves every actual modular coefficient norm, including negative k. One fixed A depending only on degree and delta works for ALL positive N and all original observables. No character, approximation or inverse existence is assumed.', 'The ACTUAL norm bump on ACTUAL polynomial samples and original small-value cardinal density give true mean/Haar discrepancy>=delta^2/40, uniformly over eps<=delta/10. The genuine observable inverse supplies ONE fixed coarse B controlling ALL actual nonconstant polynomial coefficients, before p,N,eps. No coarse constant coefficient control is assumed or claimed.', 'Every ACTUAL permitted natural multiple C(m)*p has the true degree bound and retains the ACTUAL original dense small-value samples when m*eps<=delta/10. The true natural modular multiplier inequality proves the density inclusion at the original integer sampling points, not an assumed new sampling law.', 'The genuine linear recurrence inequality is cleared using only positive delta, mu, eps and original scale N^i. The ACTUAL multiplier-index length lower bound L>=delta/(20eps) improves the true original coefficient error from O(N^-i) to O(eps)*N^-i. No division by zero tolerance is made.', 'A TRUE original small-value sample recovers the ACTUAL constant coefficient from the SAME multiplier and ALL original nonconstant coefficient bounds. True polynomial evaluation, actual integer powers, actual nearest integers and actual finite absolute-sum bounds give norm(q*beta0)<=q*eps+D*C*eps. No constant estimate is inserted as an input.', 'The GENUINE positive-tolerance large-box nonconstant inverse chooses coarse B, true linear recurrence K, fixed thresholds and budgets BEFORE p,N,eps. Larger eps uses the actual coarse inverse. Smaller eps uses actual L=floor(delta/(10eps)) and true original densities of ALL natural multiples. Actual finite common-candidate selection retains one q on a true dense set of multiplier indices for ALL coefficients. Genuine strong linear recurrence yields true coordinate multipliers on that SAME dense set; a genuine bounded common product retains EVERY coefficient bound. One actual positive Q is bounded uniformly and N^i*norm(Q*beta_i)<=C*eps for all original i>0, under a fixed original large-N threshold.', 'The ACTUAL dense original sample exists by genuine positive cardinal density. Combining true constant recovery with the SAME positive Q and actual nonconstant estimates yields one fixed rounded budget controlling EVERY original coefficient, INCLUDING i=0, for every positive eps in the permitted range. The original large-N threshold remains explicit.', 'A true finite minimum over genuine nonnegative finite error sums proves that uniformly arbitrarily small positive errors with bounded candidates yield ONE actual candidate with EVERY error exactly zero. The nonempty error index set is derived if its minimum were positive; all divisions are genuinely positive. This is a checked finite argument, not a compactness or zero-tolerance inverse assumption.', 'A COMPLETE genuine one-variable large-box scalar polynomial small-value inverse is proved: for every fixed degree D and 0<delta<=1, one fixed positive B precedes ALL real polynomial coefficients, N and eps. For N>=B, 0<=eps<=delta/10 and actual small-value density>=delta on ORIGINAL range N, ONE positive q<=B has N^i*norm(q*p.coeff(i))<=B*eps for EVERY original 0<=i<=D, INCLUDING the constant and eps=0. Positive eps uses the genuine constructed inverse; eps=0 is proved by the actual finite bounded-candidate minimum applied to those actual uniformly bounded positive-eps outputs. No small-value, character, mode, multiplier or zero-error existence is assumed. Only fixed-data constants are asserted, not power-law dependence on delta.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse and binomial compatibility remain open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Next connect actual monomial/binomial compatibility and integer translation scope, then prove multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The discrepancy is the ACTUAL original average and actual normalized Haar integral. Actual integrability and actual finite linearity prove the complex linear map. The zero mode cancels only for N>0. Every selected nonzero mode evaluates on the SAME original p.eval(n) samples and equals the TRUE scaled Polynomial phase.', 'The uniform Fourier approximation family is supplied by the retained PROVED compact family theorem, selected before orbit data. All coefficient budgets and frequency bounds come from that SAME actual finite family. Actual Fourier sum norms and true approximation errors prove existence of a nonzero mode. The phase inverse is a retained PROVED universal degree induction. Negative k is handled by true natAbs modular norm equality on every original coefficient. The output is the SAME positive product for all coefficients.', 'The bump discrepancy uses actual filtered small-value cardinality, the true original polynomial sample values and the retained PROVED real Haar support estimate. No per-orbit bump, Haar bound or Fourier approximation is assumed. The original coarse inverse supplies only nonconstant control; constant control is proved later from an ACTUAL sample.', 'The positive small-value proof chooses mu=1/B and genuine strong-recurrence K before coefficients, lengths and eps. The fixed original threshold enforces B/N^i<=mu/10 for every positive i. Actual L=floor(delta/(10eps)) is only introduced at genuine eps>0; true floor bounds show L*eps<=delta/10, L>=delta/(20eps), and the genuine strong recurrence length condition. The larger-eps branch uses the SAME actual coarse B with an explicit fixed eps lower bound.', 'For every actual multiplier m in range L, the original dense sample points remain actual small-value points for C(m)*p. The genuine scalar observable inverse yields bounded q_m controlling ALL its nonconstant coefficients. Finite common-candidate selection is applied to the TRUE relation requiring ALL original coefficients, retaining one q and a dense original multiplier-index set. Each coordinate recurrence uses this SAME set and the SAME q; the actual common natural product preserves all coordinate bounds. Per-coordinate recurrence and per-multiple inverse existence are proved/discharged, not unproved interfaces at the root.', 'Original constant recovery uses the SAME output Q and a REAL n<N from the original dense sample set. Actual evaluation is beta0+sum_{i>0} beta_i*n^i. Actual integer powers n^i and true nearest integers prove the modular triangle estimate; n<=N preserves each actual N^-i error. No absent coarse constant conclusion is borrowed from the observable inverse.', 'At eps=0, actual original zero values are also small values for every actual positive epsPrime<=delta/10. The positive-eps theorem has a UNIFORM fixed multiplier bound independent of epsPrime. True finite minimum over positive q<=A and the sum of ALL actual N^i modular errors supplies one actual q with all errors zero. The original degree, original coefficients and original N are the SAME for every positive-eps application; no limiting value is renamed as a proof.', 'The final B is chosen before p,N,eps and contains both the multiplier/error budget and original length threshold. Every coefficient from i=0 through D is controlled by the SAME q. Actual range N uses indices 0,...,N-1, as in the OpenAI equal-cube application; correspondence to a one-based auxiliary convention requires integer translation, not a claim that the constant coefficient is invariant. The retained short-box degree-two counterexample precludes removing the fixed original large-N threshold.', 'The scalar observable inverse and corrected scalar large-box small-value inverse are now GENUINELY proved. Monomial/binomial compatibility, multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse remain open. The original full prize target, rough descent and Alignment/final extraction remain unproved. No unavoidable obstruction, public repository, PR or prize entitlement is claimed.', 'Primary route: OpenAI Section 06_rough_progressions; Green-Tao https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Proposition 4.3 and Lemma 4.5; corrected polynomial small-value argument https://arxiv.org/pdf/1311.6170v3 Section 2/3, retaining sufficiently large original boxes. All previously registered source hashes and axiom sets and six pinned OpenAI sections remain retained. Author-side verification only, not independent kernel replay or external mathematical review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions scalar analytic input: complete arbitrary-observable one-variable inverse and corrected actual large-box scalar small-value inverse including all coefficients and zero tolerance; binomial/multivariable/general nilsequence inverse remain open')
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
