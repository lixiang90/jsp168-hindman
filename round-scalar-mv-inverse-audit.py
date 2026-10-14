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

PREFIX = 'round-scalar-mv-inverse'
OLD = 'round-scalar-mv-degree-step'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/ScalarMvConstantRecovery.lean', 'Hindman168/ScalarMvSmallValuesPositiveNonconstant.lean', 'Hindman168/ScalarMvSmallValuesPositive.lean', 'Hindman168/ScalarMvSmallValuesZero.lean', 'Hindman168/ScalarMvPolynomialInverse.lean']
COMPONENTS = ['Actual original cube integer monomials have true absolute weight<=N^totalDegree. The SAME original multiplier and an ACTUAL original dense sample recover the ACTUAL original constant coefficient with bound q*eps+fixedPositiveIndexCount*C*eps. True polynomial expansion and INTEGER weights prove this recovery without an assumed coarse constant estimate.', 'A genuine multivariable positive-tolerance nonconstant inverse is constructed from an actual coarse estimate. True permitted natural multiples retain ORIGINAL dense samples. Actual finite bounded-candidate density keeps ONE q on the SAME actual dense multiplier-index set for EVERY positive coefficient. True scalar strong linear recurrence at each fixed positive multiindex and the actual common finite product give ONE bounded Q retaining EVERY original N^-totalDegree error with O(eps) accuracy.', 'Actual positive-tolerance inversion now controls EVERY original multivariable coefficient INCLUDING the constant with the SAME Q. A TRUE original dense sample and proved integer-monomial recovery supply the constant, a fixed rounded budget contains all errors, and true above-degree zero coefficients extend to EVERY multiindex. Original sufficiently-large-N threshold is explicit.', 'A true finite minimum over ACTUAL bounded positive integer candidates and a fixed finite coefficient set INSERTING zero supplies ONE multiplier for ALL exact zero errors at eps=0. Actual original zero-value samples remain dense for every permitted positive epsPrime, whose multiplier budget is UNIFORM. Missing coefficients are genuinely zero. One fixed B contains both multiplier/error budget and original length threshold, giving the complete all-coefficient estimate from the actual coarse inverse.', 'COMPLETE genuine scalar MULTIPARAMETER polynomial inverse is proved for EVERY fixed input dimension and EVERY degree. Actual NATURAL DEGREE INDUCTION closes every former lower-degree small-value IH. The original large-box small-value inverse controls ALL original coefficients, INCLUDING constant and eps=0, with ONE bounded multiplier. Actual full phase and arbitrary unit Lipschitz circle-observable inverses control ALL original positive coefficients on EVERY positive N. NO phase, character, localization, multiplier, sample or lower-degree inverse existence is assumed at these root scalar theorems. Full general nilsequence/prize target still unproved.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. COMPLETE genuine scalar TARGET-circle multiparameter polynomial phase/observable and large-box all-coefficient small-value inverses are now proved for every fixed input dimension and degree. Higher-dimensional TARGET torus and general one-parameter nilsequence inverse remain open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery IH is now GENUINELY discharged by the proved full natural-degree scalar small-value induction. The full scalar multiparameter phase and arbitrary-observable inverses now GENUINELY construct ALL original nonconstant coefficient estimates on EVERY positive N without any inverse existence hypothesis. Genuine multivariable O(eps) small-value refinement includes original constant and eps=0 on original sufficiently large cubes, and full natural degree induction is closed. Next actual multivariable binomial transformation, higher-dimensional TARGET torus and general one-parameter nilsequence inverse; finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['ScalarMvConstantRecovery uses exactly the original scalarMvIntegerCube piFinset(Ico(0,N)). Every coordinate is an actual integer with 0<=x_j<N. True integer cast/product/power identities prove abs(product x_j^I_j)<=N^sum I_j, including zero dimension and degree zero. Retained true rough_fixed_spatial_expansion evaluates the SAME original polynomial, including original constant and EVERY fixed positive-degree index. The actual modular integer weighted sum inequality and true sample q multiplier inequality prove constant recovery; no coarse constant control is borrowed.', 'The positive nonconstant construction chooses coarse B, actual recurrence density mu=1/B, true strong recurrence K, fixed finite positive multiindex set U, amplification K^(U.card+1), floor-length/error thresholds and budgets BEFORE p,N,eps. The number of coordinates is U.card, not the scalar degree. Empty U is genuinely permitted by the retained finite common multiplier theorem.', 'For larger eps>=fixed eps0, actual coarse N^-degree errors are bounded by fixed O(eps) budget. For smaller eps>0, ACTUAL L=floor(delta/(10eps)) has L*eps<=delta/10, L>=delta/(20eps), and true strong-recurrence length condition. Every actual m in range L produces an actual permitted C(m)*p on the ORIGINAL cube and retains ORIGINAL dense samples. The actual coarse inverse supplies bounded q_m controlling EVERY positive coefficient. The actual finite candidate relation requires ALL positive fixed-degree coefficients; one q and the SAME true dense multiplier-index set are retained for every coordinate.', 'Each true fixed multiindex has positive total weight, so the original N threshold gives B/N^weight<=mu/10. The ACTUAL dense multiplier-index set is a true subset of each actual scalar linear small-value set. Genuine one-variable strong recurrence and the proved denominator-clearing rescale give real O(eps)*N^-weight errors. Actual common natural product on subtype U gives ONE M<=K^(U.card+1); output Q=M*q preserves ALL actual coefficients. All divisions are positive; eps=0 never enters this division branch.', 'The actual positive all-coefficient result uses ONE Q and one ACTUAL original dense sample. Original constant is recovered with actual INTEGER monomials, not by assuming a coarse constant bound. Fixed real/natural ceiling budgets contain q and the true fixed-index-count constant estimate. Every zero-weight multiindex is actually zero; every above-degree coefficient is actually zero. All original multiindices, including constant, use the SAME Q and original N.', 'At eps=0, the SAME actual polynomial and SAME original N are retained for every positive epsPrime. Actual zero-sample inclusion preserves original density. The multiplier bound A is selected BEFORE all such epsPrime. Actual finite_uniform_error_zero applies to candidates Icc(1,A) and actual nonnegative weighted modular coefficient errors over V=insert zero U. V includes constant even at degree zero/zero dimension. True above-degree zeros extend exact zero control to every multiindex. No limiting multiplier, zero-error theorem or compactness existence is assumed.', 'ScalarMvPolynomialInverse proves natural degree induction for the actual ScalarMvSmallValueEstimate, with genuine zero-degree base. Successor applies the PROVED scalar_mv_small_values_coarse_degree_step with the ACTUAL smaller-degree induction result at EVERY positive density<=1, then the PROVED positive/constant/zero refinement from that actual coarse output. This closes all formerly explicit hsmall hypotheses. The complete phase theorem uses the genuine degree-zero coefficient base or PROVED degree step with the newly PROVED smaller-degree inverse. Actual arbitrary-observable theorem then uses the genuine complete phase theorem and actual finite Fourier selection. No circular appeal to an equal/higher-degree small-value or phase inverse remains.', 'Scope: scalar TARGET circle, ANY fixed number n of INPUT variables, ANY fixed real total-degree bound D, arbitrary real coefficients. Phase/observable inverse works for EVERY positive original N, including the genuinely handled bounded short-N branch. Full O(eps) small-value result requires ORIGINAL N>=B and retains eps<=delta/10; the actual short-box counterexample remains valid and the threshold is not removed. Degree-zero and zero input dimension are supported. Fixed-data constants only; no polynomial dependence on delta claimed.', 'The general corrected quantitative Leibman input for higher-dimensional target tori and nonabelian nilmanifolds is still open. Actual multivariable binomial compatibility, rough-step descent/density/dimension/scales and positive-probability Alignment/full separated extraction remain open. Full StrongConjecture, public repo/PR and prize application are NOT claimed complete.', 'Primary route: fixed OpenAI Section 06_rough_progressions and corrected multiparameter scalar polynomial phase/small-value input, using actual dense short-line/common-direction reconstruction. All old registered sources/axiom sets and pinned OpenAI/Lean/mathlib/PNT+ data retained. Author verification only, not independent kernel replay or external peer review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: COMPLETE actual scalar target-circle multiparameter polynomial inverse for all fixed degrees/dimensions, all positive phase/observable lengths, and original large-box all-coefficient small values including constant/zero tolerance; general nilsequence/full prize target still open')
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
