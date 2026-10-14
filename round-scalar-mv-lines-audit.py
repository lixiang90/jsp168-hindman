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

PREFIX = 'round-scalar-mv-lines'
OLD = 'round-scalar-binomial-translation'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/ScalarMvLinePolynomial.lean', 'Hindman168/ScalarMvLineHomogeneous.lean', 'Hindman168/ScalarMvPhaseShortLines.lean', 'Hindman168/ScalarMvHomogeneousIndices.lean', 'Hindman168/ScalarMvIntegerCube.lean', 'Hindman168/ScalarMvLowerDegreeLineRecovery.lean']
COMPONENTS = ['The ACTUAL multivariable substitution x_j+u_j*t is a true lifted polynomial with an extra Option variable. Actual basepoint coefficient polynomials and actual numerical line polynomials are defined via the genuine Mathlib algebra equivalence. Their true evaluations, coefficients, scalar scaling, line degree<=D and coefficient totalDegree<=D-r are proved from actual linear substitution, not assumed.', 'The actual zero-basepoint line restriction equals the true original monomial sum grouped by total degree. The constant of its actual r-th basepoint coefficient polynomial equals the actual original degree-r homogeneous direction evaluation. Every product/exponent identity follows from true integer monomial powers; no coefficient or homogeneous expansion is assumed.', 'The actual scalar phase on original integer points equals the actual scalar phase of the true restricted line polynomial. The PROVED universal scalar phase inverse supplies one fixed A BEFORE multivariable polynomial, basepoint, direction, H,N,L, controlling ALL positive line coefficients with the SAME c. Actual equal-cube short-line averaging and true finite candidate selection yield ONE bounded c and true dense original basepoints on many actual directions. The retained analytic production existence hypothesis is GENUINELY discharged.', 'Fixed homogeneous index sets are chosen before polynomial coefficients. Their exact membership, true missing-coefficient zero extension, actual line constant sum and actual Leibman monomial-vector correspondence are proved. Original coefficients above the true total-degree bound are genuinely zero. Fixed indices and actual original polynomial support are connected exactly.', 'The actual original zero-origin integer cube has true cardinal N^dimension and is nonempty at N>0, including zero dimension. Genuine positive density gives an ACTUAL small-value sample. Actual constant-polynomial degree-zero small-value and phase bases are proved on these ORIGINAL samples, including changing coefficient conventions and epsilon=0.', 'The actual lower-degree line-recovery STEP is proved with the explicit degree-D small-value INDUCTION HYPOTHESIS. True degree<=D of each actual scaled positive line coefficient, SAME original dense sample inclusion, actual tolerance A/H^r<=mu/10, actual constant recovery and genuine finite common product yield ONE M<=B^(D+2) controlling ALL actual original homogeneous direction values. The universal multivariable small-value induction hypothesis remains to be discharged; no complete multivariable inverse is claimed.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. Multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse remain open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery step retains the explicit degree-D small-value induction hypothesis, still to be discharged globally. Next close actual multivariable scalar degree induction, higher-dimensional torus and general one-parameter nilsequence inverse; finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The lift is p evaluated in X(some j)+C(u_j)*X(none), genuinely linear in all variables. Retained proved rough_mv_linear_substitution_degree bounds its total degree. The actual optionEquivLeft coefficient identifies the true basepoint polynomial. The coefficient degree bound handles both r<=lift.totalDegree and r>lift.totalDegree (actual zero coefficient); it does not claim degree+r<=D for a zero coefficient above D.', 'Actual polynomial evaluation under Option.elim gives p(x+u*t). Actual Polynomial.map of evaluation preserves the true scalar line polynomial and coefficients. The true zero-basepoint power expansion uses the SAME original p.support and original p coefficients; polynomial extensionality over REALS proves actual polynomial equality. Integer monomial exponent sums and products are exact, including degree zero.', 'Actual phase equality is proved at every natural line sample using true integer/natural cast identities. A genuine function equality, rather than an assumed distribution, transfers the actual finiteComplexSetMean. One universal scalar bound at delta/2 works before ALL line data and dimension. The true short-line length H=N/L^2 is positive under L>0 and L^2<=N. The cube common-candidate theorem is applied with the TRUE Icc(1,A) list, true cardinal A, actual unit phase bound and an ACTUAL production proof using scalar_mv_short_line_inverse. No hproduce remains in the new cube theorem.', 'The original basepoint cube is exactly piFinset(Ico(0,N)), and original direction cube is exactly piFinset(range L). The boundary condition 8*dimension<=delta*L and true large line conditions are explicit. The output controls ALL r simultaneously on the SAME dense basepoint set, with the SAME positive c, and retains true direction and basepoint densities delta/(8A). No spanning or full coefficient conclusion is claimed at this stage.', 'The true homogeneous index set piFinset(range(r+1)) filtered by total weight=r is independent of p. Exact membership derives each individual exponent bound from the actual nonnegative total sum. True Finsupp equivalence and actual zero coefficients extend the original support to that fixed set. Actual Leibman monomial-vector equality uses the SAME original degree-r coefficients. Above-degree coefficient zero follows from the genuine total degree bound.', 'The actual integer cube cardinal uses genuine Int.card_Ico and finite product, including zero dimension where cardinal=1. Positive N proves original cube nonemptiness; positive density proves the actual filtered set nonempty. Degree-zero p is actually C(coeff(0,p)), and original sample evaluation gives the true constant small-value bound. All positive-weight coefficients are genuinely zero; all zero-weight indices are actually zero. No zero-error limit assumption or omitted empty-domain case.', 'ScalarMvLowerDegreeLineRecovery is EXPLICITLY an induction STEP, not a universal inverse theorem. Its hsmall is the degree-D all-coefficient small-value induction hypothesis on the SAME original integer cube, with a uniform B before f,N,eps. It is not discharged for arbitrary D yet, so the full original theorem remains unproved. Every other existence/degree/sample/multiplier input is constructed: actual C(c)*lineCoeff_r has degree<=D for r>=1, original simultaneous dense set is a true subset of its actual tolerance set, original N>=B is retained, H>=1 gives A/H^r<=A/H<=mu/10, and true finite common product on Fin(D+1) yields one actual M with bound B^(D+2). The same M controls EVERY r and original constant homogeneous direction evaluation.', 'NEXT actual degree induction must close the remaining hsmall via the genuine multivariable small-value construction. Finish actual common multiplier selection over directions, fixed-before-data L and original N thresholds, simultaneous dense direction integer reconstruction, bounded short N, true cube Fourier/bump bridge, natural-multiple refinement and actual sample constant recovery. Neither full multivariable inverse nor general nilsequence inverse is proved by these line components.', 'Primary route: OpenAI Section 06_rough_progressions and corrected equal-side quantitative Leibman input, retained genuine dense short-line and integer reconstruction machinery. Fixed-data constants only; no power-law delta rates. Author verification only, not independent kernel replay or external peer review. Full StrongConjecture, rough descent, Alignment and final extraction remain open.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: actual multivariable line coefficient algebra, genuine scalar short-line candidate existence and actual common-candidate cube density; explicit lower-degree small-value induction step, full multivariable/general nilsequence inverse still open')
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
