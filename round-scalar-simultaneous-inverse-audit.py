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

PREFIX = 'round-scalar-simultaneous-inverse'
OLD = 'round-scalar-leading-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/FiniteNaturalBlockReindex.lean', 'Hindman168/FiniteNaturalBlockMeans.lean', 'Hindman168/UnitCirclePhaseVariation.lean', 'Hindman168/NormalizedNaturalPowerVariation.lean', 'Hindman168/UnitCircleTopPowerProgression.lean', 'Hindman168/ScalarPolynomialTopRemoval.lean', 'Hindman168/FiniteComplexUnitFactorTransfer.lean', 'Hindman168/PositiveFractionalBlockLength.lean', 'Hindman168/ScalarPolynomialStrippingFraction.lean', 'Hindman168/ScalarPolynomialTopStripping.lean', 'Hindman168/ScalarPolynomialIntegerCoefficientRecovery.lean', 'Hindman168/IntegerWeightedModOneNorm.lean', 'Hindman168/ScalarPolynomialRecoveryWeights.lean', 'Hindman168/ScalarPolynomialRecoveryModOne.lean', 'Hindman168/ScalarPolynomialSimultaneousInverse.lean']
COMPONENTS = ['Actual finite interval indices are genuinely reindexed into complete integer blocks and original residue progressions of one common length H. A true quotient/remainder bijection proves the sum identities, including zero-width cases, and every actual selected progression index is proved to stay inside its original full block.', 'The actual complete-block prefix mean equals the actual nested uniform progression means. The actual discarded tail has exact cardinal N mod(qH). Actual unit sample bounds retain a true large prefix mean, prove the prefix is nonempty, and genuine finite maximum/mean bounds select one true progression with large mean. Neither progression existence nor a replacement sampling law is assumed.', 'The genuine canonical circle phase satisfies the actual real upper bound norm(character(x)-1)<=2*pi*abs(x). Actual phase differences reduce to the actual difference character by true unit multiplication. Subtracting any true integer preserves the actual circle phase.', 'The actual power variation on [0,N] is bounded by d*(L/N)*N^d, through true normalization of the existing power oscillation bound. For actual n=a+q*j, the true integer q divides the actual integer n^d-a^d, proved by genuine difference-of-powers divisibility.', 'If actual N^d*norm(q*alpha)<=B, true round(q*alpha) and the actual integer quotient of n^d-a^d remove the rational phase EXACTLY. The genuine remaining real error gives actual top-power phase variation<=2*pi*d*B*H/N along the same actual progression. No real scalar quotient-circle map or modular division is introduced.', 'Actual removal of the top monomial lowers the true degree bound and gives the exact real evaluation/phase factorization. The original sample phase error is exactly the actual top-monomial phase error, using a true unit lower phase. Actual affine polynomial substitution evaluates at the actual integer progression and preserves the true lower degree bound.', 'Actual pointwise errors between complex samples and a true constant unit factor times lower samples bound the actual finite mean difference. The genuine triangle inequality then retains a large lower mean. No phase alignment or approximation conclusion is assumed.', 'For an actual fixed fraction rho and rho*N>=2, the actual natural floor H is positive and satisfies rho*N/2<=H<=rho*N. Actual fixed positive fractions chosen from the degree, top bound and delta satisfy BOTH original tail-width and top-phase-error budgets before polynomial coefficients and N.', 'GENUINE top stripping is proved with B,M,rho chosen BEFORE the polynomial and N. Actual leading inverse yields q<=B; actual H=floor(rho*N) and actual finite block selection yield the SAME original progression. After true top-monomial removal, the actual lower polynomial on that actual progression has degree at most d and actual phase mean>=delta/4. All original indices, floor lengths, coefficient control and sample errors are retained. No conditional localization/existence input remains.', 'Actual Taylor coefficients are expanded by the true finite polynomial monomial sum, and true affine scaling multiplies coefficient j by q^j. Actual inverse Taylor translation recovers q^D*p.coeff(i) as a sum of actual affine coefficients times genuine INTEGER weights q^(D-j)*choose(j,i)*(-a)^(j-i). Those actual weights vanish below i; all scale denominators are cleared without division on the quotient circle.', 'A true weighted modular norm bound is proved using actual nearest integers and actual finite absolute-sum bounds. Actual recovery-weight norms are bounded by q^D*2^D*N^(j-i), using true binomial bounds and original a<=N. Actual H>=rho*N transfers the original affine coefficient errors H^-j to N^-j. The SAME integer recovery gives original coefficient i error N^-i, with an actual uniform budget (D+1)*q^D*2^D*A/rho^D. The constant coefficient is not assumed controlled: its weight is exactly zero for every positive i.', 'A GENUINE simultaneous scalar Weyl phase inverse is proved for EVERY fixed natural degree bound and ALL positive N. One positive A is chosen before every real Polynomial and N. Actual phase mean>=delta yields ONE positive Q<=A such that N^i*norm(Q*p.coeff(i))<=A for EVERY original nonconstant i<=D. True natural degree induction uses genuine top stripping, actual lower-degree inverse on the selected actual progression, and true integer recovery at fraction rho/2. The actual output Q=k*q^(D+1) retains both the original top multiplier and all lower recovery multipliers. Bounded short N use the actual circle half-period norm bound. No inverse, character, localization, coefficient reconstruction or per-polynomial existence conclusion is assumed. Only fixed-data bounds are asserted, not polynomial rates in delta.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. This does not prove the genuine higher-degree scalar polynomial inverse, higher-dimensional torus inverse, or general one-parameter nilsequence quantitative character existence and binomial coefficient smoothness. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Next connect genuine uniform Fourier reduction to arbitrary bounded Lipschitz scalar observables and binomial compatibility, then prove large-box polynomial small-value estimates, higher-dimensional torus and general one-parameter nilsequence inverse; finish polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The original sampling interval is range N. Its exact complete prefix has length q*H*floor(N/(q*H)); its tail is the true original remainder. The complete-block progression samples have actual positions q*H*b+r+q*j. The selected start a is an original natural integer a<N, and EVERY actual sample a+q*j, j<H, remains <N.', 'Actual finite maximum selection is applied to the true nested means after the genuine block-sum identity. Actual unit samples bound the tail before selection. The proof shows the actual prefix and outer block set are nonempty rather than assuming these properties. The actual block mean is retained at delta/2; no cancellation or common complex direction is assumed.', 'The top variation uses actual alpha, q, round(q*alpha) and the true integer quotient of (a+q*j)^d-a^d. It subtracts the true integer round(q*alpha)*quotient, proves equality of the actual circle values, and only then bounds the genuine real error. Normalized power variation preserves the required factor H/N. Negative alpha and arbitrary coefficients are included.', 'The top-stripping fraction is a fixed minimum of actual positive real budgets. Its floor length is chosen from rho*N after N, with a fixed positive M guaranteeing H>=rho*N/2. q<=B, the actual floor upper bound and the original width budget enforce the tail restriction; the same data enforce pointwise phase error<=delta/8. The actual polynomial after top removal and affine substitution has large phase mean>=delta/4 on exactly this H-term progression.', 'The coefficient recovery is an actual equality of real polynomial coefficients. It uses genuine Taylor translation, actual affine scaling and actual integer clearing by q^D. Every recovery weight is an explicitly defined true integer. Terms below i vanish by true choose(j,i)=0, so no nonconstant estimate accidentally calls a constant-coefficient hypothesis.', 'The recovery norm proof uses actual nearest integers for the actual affine coefficients, followed by the actual weighted finite norm inequality. Original a<=N gives actual integer weight growth N^(j-i). The true fractional-length transfer at H>=rho*N controls N^j times each actual affine error; summing after multiplication by N^i retains N^-i. All divisions have positive real rho powers. There is no modular division by q or H.', 'The simultaneous inverse is a genuine degree induction rooted in a vacuous degree-zero case. For degree D+1 it selects fixed top-stripping B,M,rho and fixed lower-degree K at delta/4 BEFORE p,N. The actual chosen q,a,H come from genuine top stripping; the lower-degree induction is applied to the actual polynomial on that actual progression. ONE actual k controls every lower coefficient. The output Q=k*q^(D+1) is positive and bounded before checking ALL original i. The same q controls the original top coefficient, and Q includes it even at D=0. Lower original coefficients are recovered with the SAME integer weights and multiplied by the extra q. Fixed ceiling budgets contain the lower and top errors. The separate bounded-N case uses Q=1 and controls every coefficient by the actual circle half-period bound. Thus no extra character, coefficient, progression or inverse existence hypothesis remains at the root.', 'The result here is the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse, not yet the inverse for arbitrary bounded Lipschitz observables, higher-dimensional torus or general nilsequence. Actual uniform Fourier reduction and binomial compatibility still need connection, followed by large-box polynomial small-value estimates and the general one-parameter/equal-cube route. The original full prize target remains unproved and no unavoidable obstruction is established.', 'Primary references: OpenAI Section 06_rough_progressions; https://annals.math.princeton.edu/wp-content/uploads/annals-v175-n2-p02-p.pdf Section 4 Proposition 4.3, including actual short arithmetic progression stripping; https://arxiv.org/pdf/1311.6170v3 Sections 2/3. All formerly registered sources/axioms and six pinned OpenAI sections remain unchanged. Verification is author-side, not independent kernel replay or external review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions scalar analytic input: genuine original short progression localization, top stripping, integer coefficient recovery and complete all-degree simultaneous scalar PHASE inverse; arbitrary scalar observables and general nilsequence inverse remain open')
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
