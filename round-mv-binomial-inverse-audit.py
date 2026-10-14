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

PREFIX = 'round-mv-binomial-inverse'
OLD = 'round-torus-mv-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/MvBinomialCoefficients.lean', 'Hindman168/MvBinomialMonomialExpansion.lean', 'Hindman168/MvPolynomialBinomialExpansion.lean', 'Hindman168/MvBinomialCoefficientModOne.lean', 'Hindman168/MvBinomialPolynomialInverse.lean']
COMPONENTS = ['The fixed FULL exponent box including zero and true NATURAL INTEGER tensor Stirling weights are defined before polynomial data. Exact coordinate membership, original bounded-weight membership, true zero weights below any coordinate and true nonzero-weight total-degree monotonicity are proved.', 'The actual univariate polynomial Stirling identity is mapped into each actual MvPolynomial coordinate. True finite product/sum exchange and ACTUAL positive factorial cancellation yield exact ordinary monomial expansion in the ORIGINAL roughMvBinomialPolynomial basis, with genuine natural integer weights. No multivariate basis identity is assumed.', 'Every ACTUAL original polynomial of totalDegree<=D has true support in the fixed full exponent box and a TRUE binomial-basis polynomial expansion with computed coefficients. Original binomial coefficients above totalDegree D are genuinely zero. Actual projection linearity and exact constant-plus-positive-index form used in the paper are proved, retaining zero degree/dimension. No assumed representation or correspondence.', 'One fixed positive natural tensor coefficient budget, equal to scalarBinomialCoefficientBudget(D)^inputDimension, contains EVERY actual Stirling row. True integer weighted modular norm bound, vanishing low-degree weights and N>=1 give actual N^-totalDegree preservation. The lower-weight parameter handles nonconstant-only or all-coefficient inputs without borrowing absent constant control.', 'COMPLETE genuine scalar and standard TARGET-TORUS binomial observable inverses are proved for every fixed dimension/degree and EVERY positive original N, retaining the SAME original multiplier/nonzero horizontal character. The genuine scalar original large-box binomial small-value inverse controls ALL binomial coefficients INCLUDING constant and eps=0 with SAME q and retained original large-N threshold. All bounds precede coefficients,N,F,eps; no character, inverse or coefficient existence assumed.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. COMPLETE genuine scalar TARGET-circle multiparameter polynomial phase/observable and large-box all-coefficient small-value inverses are now proved for every fixed input dimension and degree. COMPLETE genuine standard HIGHER-DIMENSIONAL TARGET TORUS monomial-coefficient observable inverse is now proved for every fixed target/input dimension and degree, on every positive original N, with an ACTUALLY produced bounded nonzero integer horizontal character and true continuous lattice-integral real character. General native/nonabelian one-parameter nilsequence inverse remains open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery IH is now GENUINELY discharged by the proved full natural-degree scalar small-value induction. The full scalar multiparameter phase and arbitrary-observable inverses now GENUINELY construct ALL original nonconstant coefficient estimates on EVERY positive N without any inverse existence hypothesis. Genuine multivariable O(eps) small-value refinement includes original constant and eps=0 on original sufficiently large cubes, and full natural degree induction is closed. Actual full multivariable monomial-to-binomial transformation, original rough-box basis expansion and genuine same-character scalar/standard-target-torus binomial inverses are now proved, including scalar constant/zero-tolerance small-value input. Next native/nonabelian orbit-equidistribution quantitative Leibman input; finish native general polynomial/difference compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target. Distinguish the remaining nonabelian orbit-equidistribution/quantitative Leibman input from the separate HasNativePeriodicIntervalInverse finite-list interval Gowers-to-nilsequence correlation existence input; neither that Gowers inverse nor HasAlignmentMonomialRecurrence is discharged by the standard torus result.'

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
        application_review=COMPONENTS+['The full exponent box is actual piFinset(range(D+1)) independent of p and includes zero, including the unique empty vector at zero dimension. Every actual support exponent has total weight<=D and each coordinate<=D, so its true Finsupp equivalence belongs to the box. Finsupp.sum_of_support_subset and actual p.as_sum prove the original polynomial expansion; missing coefficients are genuinely zero.', 'Tensor weights are product_j (I_j! * StirlingSecond(J_j,I_j)), actual NATURAL INTEGERS. StirlingSecond(J_j,I_j)=0 when J_j<I_j gives a true zero product. Nonzero weight implies every original exponent at least the output exponent and hence total original weight>=total output weight. This is an actual algebraic proof, not an assumed triangularity law.', 'The true retained univariate X^r Stirling identity is sent through actual Polynomial.eval2RingHom(MvPolynomial.C)(X_j). Actual polynomial maps preserve powers/sums/products. True Finset.prod_univ_sum gives tensor expansion. Original roughMvBinomialPolynomial is EXACTLY product factorial inverses times product falling factors; real factorial positivity permits exact cancellation in the REAL coefficient ring. No quotient-circle division or new binomial basis naming shortcut is used.', 'Double finite-sum exchange and true original polynomial support expansion prove actual p=sum_I C(alpha_I)*roughMvBinomialPolynomial(I). alpha_I is computed from SAME original beta_J with true integer weights. Actual above-degree zero coefficients and true zero weights remove all total-degree>D output terms. The original paper constant-plus-positive-degree expansion is proved exactly, including actual basis at zero=1, all-zero weight iff zero vector, and zero not in positive index set.', 'The actual coefficient of the character projection is exactly sum_j k_j*alpha_I(p_j), by true original monomial projection coefficients and finite sum exchange. The same original vector polynomial and SAME original character appear in both representations. No independent alpha values, representative selection, coefficient preservation or expansion is supplied as an unproved input.', 'Row budget is a true product of the actual one-coordinate row sums via Finset.prod_univ_sum. Every actual output coordinate I_j<=D allows the retained PROVED scalar row budget; true product inequality yields the fixed tensor budget scalarBinomialCoefficientBudget(D)^dimension. It is genuinely positive, including dimension zero. The budget precedes arbitrary coefficients,N and accuracy.', 'For modular transfer, SAME q*alpha_I is an ACTUAL finite INTEGER weighted sum of SAME q*beta_J. The retained nearest-integer weighted modular inequality is proved. True zero weights remove all J below the permitted lower weight; nonzero weights ensure |J|>=|I|, so genuine N^|I|<=N^|J| at N>=1 retains N^-|I| errors. Positive-weight observable input never borrows constant control; all-weight small-value input legitimately controls constant. Every natural weight is nonnegative and its actual row sum is bounded by fixed budget.', 'Scalar binomial observable result applies the GENUINELY PROVED complete scalar observable inverse to SAME p/N/F, retains SAME q, and increases only fixed budget. Scalar binomial small-value result applies the GENUINELY PROVED original all-coefficient small-value inverse with its actual N>=A condition and zero-tolerance case, retains SAME q and SAME original samples, and enlarges one fixed original length/error budget. Above-degree binomial coefficients are genuinely zero and all multiindices are covered.', 'Standard target-torus result applies the GENUINELY PROVED torus monomial inverse to SAME vector p/N/F, producing ACTUAL nonzero v. Actual projection alpha linearity reduces original projected binomial errors to binomial coefficients of the SAME true scalar projection xi_v(p). True projection degree and integer row estimate retain SAME v and EVERY positive original coefficient. Character l1 size remains the ORIGINAL bound; uniform enlarged B contains both original size and tensor error. No character is reselected and no extra multiplier existence assumed. All positive N, fixed arbitrary target/input dimensions and degrees are covered.', 'This proves the standard TARGET-TORUS binomial coefficient form of the corrected equal-cube input, and genuine scalar all-coefficient binomial small-value input. It does not prove the native/nonabelian quantitative Leibman orbit inverse, the SEPARATE finite-list interval Gowers-to-nilsequence correlation existence HasNativePeriodicIntervalInverse, HasAlignmentMonomialRecurrence, general rough-step comparison or full positive separated extraction. Full StrongConjecture/public repo/PR/prize application NOT complete.', 'Primary route: fixed OpenAI Section 06_rough_progressions actual binomial coefficients and corrected equal-side statement; true Mathlib finite polynomial/product machinery and retained genuine scalar/torus inverse. Fixed-data constants only; no power-law delta rates asserted. Every old registered source/axiom set and pinned OpenAI/Lean/mathlib/PNT+ data retained. Author verification only, not independent kernel replay or external peer review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: actual full multivariable binomial basis/integer coefficient transform and COMPLETE genuine same-character standard torus binomial equal-cube inverse, plus all-coefficient scalar binomial small values including zero tolerance; native/general nilsequence/full prize target still open')
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
