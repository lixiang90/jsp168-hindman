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

PREFIX = 'round-torus-mv-inverse'
OLD = 'round-scalar-mv-inverse'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/UnitTorusUniformFourierApproximation.lean', 'Hindman168/UnitTorusFiniteDiscrepancy.lean', 'Hindman168/UnitTorusFiniteObservablePhaseSelection.lean', 'Hindman168/TorusPolynomialCharacterProjection.lean', 'Hindman168/TorusMvPolynomialInverse.lean', 'Hindman168/TorusIntegerHorizontalCharacter.lean']
COMPONENTS = ['Actual multidimensional Fourier monomials span densely by the PROVED Mathlib theorem. True uniform approximation and actual compact unit Lipschitz family supply ONE finite Fourier family BEFORE all orbit data and observables. Actual mode integrals under EXPLICIT normalized Pi(circle Haar) are 1 at zero vector and 0 at every nonzero vector, proved by true product integration and actual circle mode integrals.', 'The actual finite TARGET-torus mean minus EXPLICIT normalized product Haar is a genuine complex linear map with norm<=2*norm(F). Actual zero vector mode cancels at nonempty domains, every nonzero mode is the actual finite Fourier mean, and true finite sum budgets force an ACTUAL nonzero integer-vector mode.', 'One fixed compact Fourier family chooses accuracy eta>0,eta<=1 and natural character l1 budget K BEFORE EVERY finite sample set, actual torus orbit and arbitrary unit Lipschitz observable. True approximation and finite-mode selection produce an ACTUAL k!=0 with sum_j natAbs(k_j)<=K and actual eta-large mode mean. No character/mode existence is assumed.', 'The ACTUAL original integer character projection xi_k(p)=sum_j C(k_j)*p_j has true degree<=D, actual original coefficient sums and actual evaluation. True multiplicative circle-phase identity gives the exact multidimensional Fourier sample phase of that SAME original projection. Positive natural scaling retains a genuinely nonzero integer vector, exact l1 size and exact projected coefficient identity.', 'COMPLETE genuine HIGHER-DIMENSIONAL TARGET TORUS polynomial observable inverse is proved for ANY fixed target dimension m, INPUT dimension n and degree D, on EVERY positive original N. One fixed bound precedes all original real coefficients,N,F. Actual nonzero Fourier character and the PROVED complete scalar projection inverse produce ONE actual nonzero integer vector v with bounded l1 size, controlling EVERY original positive-weight PROJECTED coefficient by the SAME v. No phase, character, Fourier approximation, inverse or coefficient existence is assumed at this torus root.', 'The actual real integer-coordinate horizontal character is a true additive homomorphism, genuinely continuous, genuinely nonzero for nonzero vector, and ACTUALLY integer-valued on every original integer lattice point. Exact original coordinate sums prove lattice integrality and single-coordinate evaluation proves nonzeroness, not an assumed character certificate.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. COMPLETE genuine scalar TARGET-circle multiparameter polynomial phase/observable and large-box all-coefficient small-value inverses are now proved for every fixed input dimension and degree. COMPLETE genuine standard HIGHER-DIMENSIONAL TARGET TORUS monomial-coefficient observable inverse is now proved for every fixed target/input dimension and degree, on every positive original N, with an ACTUALLY produced bounded nonzero integer horizontal character and true continuous lattice-integral real character. General native/nonabelian one-parameter nilsequence inverse remains open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery IH is now GENUINELY discharged by the proved full natural-degree scalar small-value induction. The full scalar multiparameter phase and arbitrary-observable inverses now GENUINELY construct ALL original nonconstant coefficient estimates on EVERY positive N without any inverse existence hypothesis. Genuine multivariable O(eps) small-value refinement includes original constant and eps=0 on original sufficiently large cubes, and full natural degree induction is closed. Next actual multivariable binomial transformation and native/nonabelian one-parameter nilsequence inverse; finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target. Distinguish the remaining nonabelian orbit-equidistribution/quantitative Leibman input from the separate HasNativePeriodicIntervalInverse finite-list interval Gowers-to-nilsequence correlation existence input; neither that Gowers inverse nor HasAlignmentMonomialRecurrence is discharged by the standard torus result.'

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
        application_review=COMPONENTS+['The target is genuine UnitAddTorus(kappa), with arbitrary fixed finite target index type in helper theorems and Fin(m) at the root. Dense span is the actual Mathlib UnitAddTorus.span_mFourier_closure_eq_top proved by Stone-Weierstrass. Actual compact unit_lipschitz_observables_compact gives a true fixed finite approximation family before ANY orbit/observable. The approximation is in true sup norm, with actual finite Finsupp coefficients.', 'The normalized target measure is EXPLICIT Measure.pi(fun j=>AddCircle.haarAddCircle). Mathlib AddCircleMulti uses local MeasureSpace instances internally; our code never assumes its default volume normalization and declares no new measure instance. Actual integral_fintype_prod_eq_prod and actual circle Haar Fourier integral prove exact zero/nonzero vector integrals. A nonzero vector has an ACTUAL nonzero coordinate. Empty target dimension is retained with the genuine empty product=1 and no nonzero vector.', 'Actual torus discrepancy is the TRUE original finite sample mean and true normalized Pi Haar integral. Every integral is genuinely integrable by compact support on the actual compact torus. The true norm<=2*norm(F), finite complex linearity and nonempty-domain zero-mode cancellation are proved. The true finite coefficient norm budget yields actual nonzero vector mode selection. No discrepancy norm, normalized measure, mode or frequency existence is supplied as an unproved input.', 'Actual finite approximation family determines both coefficient budget B and l1 frequency budget K, selected BEFORE sample set/orbit/F. eta=min(delta/(4B),1/2)>0<=1 is fixed BEFORE any coefficients/N. The SAME original orbit is used in approximation and Fourier mean; true map linearity and true approximation error retain large finite Fourier discrepancy. Actual finite-mode selection gives k!=0 and its total natAbs sum<=K. No coordinate frequency or hidden inverse input.', 'TorusPolynomialCharacterProjection is an ACTUAL real multivariable polynomial sum with integer coordinate weights, not a placeholder scalar sequence. True total-degree, coefficient and evaluation identities are proved. Actual AddCircle.toCircle addition and genuine finite-sum/product identities prove EXACT multi-Fourier sample equality with the phase of that SAME projection. Negative integers are handled via actual integer scalar quotient-circle multiplication. No real division on a quotient circle is used.', 'The root fixes target m,input n,degree D and delta, then actual eta,K and genuine scalar phase budget A0 BEFORE p,N,F. The actual vector polynomial p has arbitrary real coefficients and each component degree<=D. Actual selected k gives an actual scalar projection of true degree<=D and true large phase on the SAME original integer cube. The PROVED scalar_mv_polynomial_phase_inverse supplies ONE q>0,q<=A0 for EVERY original positive-weight coefficient. Original character v_j=q*k_j is genuinely nonzero; its true size sum_j natAbs(v_j)=q*sum_j natAbs(k_j)<=A0*K. Exact original projected coefficient=sum_j v_j*beta_{j,I}=q*coeff_I(xi_k(p)) transfers EVERY N^-|I| bound with SAME v. Uniform A=A0*K+1 contains character and coefficient budgets.', 'Quantifiers cover EVERY positive original N, including the scalar inverse genuinely proved bounded short-N branch; no sufficiently-large-N restriction is added at this observable/character stage. Input n=0, degree D=0 and target m=0 are permitted. At target m=0, actual bad nonempty-orbit discrepancy would force an impossible nonzero vector by the PROVED Fourier selection, so the implication is genuinely vacuous, not an omitted special case. For nonempty target and constant polynomial, nonconstant projected coefficients are ACTUALLY zero. No bound on the original constant phase is asserted.', 'The horizontal character is the ACTUAL additive real map x->sum_j k_j*x_j. Finite coordinate continuity proves it continuous; true integer cast/product/sum proves its value at every integer lattice vector equals a TRUE integer. Nonzero coordinate has ACTUAL single-coordinate real evaluation k_j!=0, proving the additive hom itself nonzero. The root character vector corresponds to this real map and projects every original coefficient exactly. Scope is the concrete standard product torus; a native general nilmanifold quotient bridge is still required.', 'This completes the genuine standard TARGET-torus monomial-coefficient inverse and the arbitrary-observable/equal-cube analytic input. It does NOT yet prove actual multivariable binomial transformation, general nonabelian one-parameter nilsequence inverse or the full native nilmanifold quantitative Leibman input. General corrected equal-cube assembly, rough-step descent/density/dimension/scales, Alignment and full positive rapidly separated extraction remain open. StrongConjecture/public repository/PR/prize application NOT claimed complete.', 'The retained HasNativePeriodicIntervalInverse is a SEPARATE finite-list interval Gowers-to-nilsequence CORRELATION existence statement, as inspected in NativePeriodicIntervalInverseThreshold.lean. It is not the orbit-equidistribution inverse proved here. It remains explicitly unproved, and no torus Fourier/coefficient theorem is claimed to discharge it. HasAlignmentMonomialRecurrence also remains an explicit independent existence input.', 'Primary route: fixed OpenAI Section 06_rough_progressions, genuine torus Fourier/character base of the quantitative Leibman input, Mathlib Analysis/Fourier/AddCircleMulti.lean and actual proved scalar multiparameter inverse. Fixed-data constants only, no power-law delta rates asserted. Every earlier registered source and axiom set and fixed OpenAI/Lean/mathlib/PNT+ pin retained. Author verification only, not independent kernel replay or external peer review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: COMPLETE genuine standard target-torus polynomial monomial-coefficient inverse with actual bounded nonzero integer horizontal character, arbitrary fixed target/input dimension/degree and all positive lengths; native/nonabelian nilsequence/full prize target still open')
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
