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

PREFIX = 'round-scalar-mv-degree-step'
OLD = 'round-scalar-mv-lines'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/ScalarMvSmallValueEstimate.lean', 'Hindman168/ScalarMvCommonHomogeneousDirections.lean', 'Hindman168/ScalarMvShortLineThreshold.lean', 'Hindman168/ScalarMvPhaseDegreeStep.lean', 'Hindman168/UnitCircleFiniteDiscrepancy.lean', 'Hindman168/UnitCircleFiniteObservablePhaseSelection.lean', 'Hindman168/ScalarMvObservableInverse.lean', 'Hindman168/ScalarMvSmallValuesCoarse.lean', 'Hindman168/ScalarMvNaturalMultiples.lean']
COMPONENTS = ['The precise original integer-cube all-coefficient small-value induction proposition is defined, not assumed as an axiom. Its degree-zero case is GENUINELY proved by the retained actual constant-polynomial sample theorem, uniformly with B=1 including zero tolerance and zero dimension.', 'The true lower-degree line recovery constructs actual bounded candidates for each actual good direction. Genuine finite bounded-candidate density supplies ONE m shared by an actual dense direction set, retaining ALL homogeneous degrees simultaneously. The only inverse hypothesis is explicitly the lower-degree small-value induction hypothesis.', 'One true original-length threshold is chosen before N. The ACTUAL quotient H=floor(N/L^2) is positive, N>=B, A/H<=mu/10 and N<=2*L^2*H. True ceiling, integer quotient and remainder identities prove every length/error condition without replacing H by an assumed real scale.', 'The COMPLETE multiparameter scalar phase degree STEP is proved, explicitly depending only on degree-D small-value induction. All actual short-line/common-character production, true dense basepoints and directions, common bounded multiplier, fixed-before-data L and N thresholds, actual simultaneous integer direction reconstruction and ALL original coefficient N^-degree bounds are constructed. Bounded short N is genuinely handled, so the phase STEP works for EVERY positive N. Degree-one phase inverse is UNCONDITIONAL, rooted in the genuine degree-zero small-value base. Arbitrary-degree induction remains to close.', 'The actual mean-minus-Haar discrepancy for ANY finite circle orbit is a genuine complex linear map with true norm<=2*norm(F). True nonzero mode equals actual finite Fourier mean, actual zero mode cancels on nonempty domains, and true finite-mode selection supplies a genuine nonzero frequency.', 'One fixed finite compact Fourier approximation family yields accuracy eta>0,eta<=1 and frequency budget K BEFORE ALL finite sample sets, orbits and arbitrary unit Lipschitz observables. Actual discrepancy supplies an ACTUAL nonzero k with k.natAbs<=K and a genuine eta-large finite phase. No mode existence is assumed.', 'The true Fourier value of the ORIGINAL multivariable polynomial is the true phase of C(k)*p. The actual phase degree theorem gives one q for all coefficients, and q*k.natAbs preserves ALL original modular coefficient norms including negative k. The arbitrary-observable degree STEP is proved with the explicit smaller-degree small-value IH; degree-one observable inverse is UNCONDITIONAL for ANY fixed input dimension and ALL positive N.', 'True original dense values on ANY nonempty finite circle orbit give actual fixed norm-bump Haar discrepancy>=delta^2/40. This genuine bump and the actual observable degree STEP prove the true simultaneous nonconstant coarse small-value degree STEP. Degree-one coarse inverse is UNCONDITIONAL. Constant and O(eps) refinement are not yet claimed at this coarse stage.', 'Every ACTUAL permitted natural multiple C(m)*p has the true degree bound and retains the ACTUAL original dense small-value samples on the SAME integer cube. The genuine natural modular multiplier norm inequality proves the actual set inclusion; no new sample distribution is assumed.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. Multivariable scalar/higher-dimensional torus and general one-parameter nilsequence inverse remain open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery step retains the explicit degree-D small-value induction hypothesis, still to be discharged globally. The actual multivariable phase and arbitrary-observable degree STEPS now construct ALL original nonconstant coefficient estimates on EVERY positive N, explicitly dependent on lower-degree all-coefficient small-value IH. Degree-one phase/observable/coarse small-value inverses are genuinely unconditional. Actual finite circle Fourier selection, bump discrepancy and natural-multiple sample inclusion are proved. Next finish genuine multivariable O(eps) small-value refinement including original constant and eps=0, close the paired degree induction, then higher-dimensional torus and general one-parameter nilsequence inverse; finish general polynomial/difference/binomial compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['ScalarMvSmallValueEstimate is an explicit quantified proposition with the actual original cube, real polynomial degree, actual modular sample density and EVERY actual coefficient including constant. The degree-zero proof supplies actual q=1 and uniform B=1. Definition of a proposition is not a proof for arbitrary degree, and arbitrary-degree hsmall remains explicit in subsequent induction STEP statements.', 'The common-direction lemma uses true scalar_mv_lower_degree_line_recovery on each original good direction and SAME original dense basepoint sets. The actual candidate relation requires EVERY homogeneous r simultaneously. Actual finite_bounded_candidate_density selects ONE m and an actual filtered subset T with density mu/B^(D+2). That multiplier budget is independent of L and precedes L in the phase degree theorem.', 'The actual threshold is L^2*(B+ceil(10*A/mu)+2), selected before original N. Genuine Nat.le_div_iff_mul_le proves the quotient lower bound; true positive mu clears A/H<=mu/10; genuine div_add_mod and mod_lt give N<=2*L^2*H. All divisions are positive; no zero quotient or real/natural division confusion is allowed.', 'The phase step fixes actual scalar line A at delta, mu=delta/(8A), true lower-degree B and P=B^(D+2) BEFORE L. Actual L exceeds both boundary ratio 8*n/delta and (D+1)*P/mu, yielding strict direction degree threshold. Only AFTER this fixed L, actual finite direction reconstruction C and original-length threshold T0 are chosen, still BEFORE p,N. There is no circular dependence of candidate size on L. The true original common c<=A and common m<=P are produced from actual large mean and real dense sets; no hproduce or candidate existence input remains apart from the named lower-degree small-value IH.', 'Actual homogeneous indices r=1,...,D+1 and true original line-constant identities connect the SAME original coefficients to retained actual simultaneous integer direction reconstruction. One k<=C controls every homogeneous row. Final Q=k*m*c is positive and bounded before p,N. True N/H<=2L^2 preserves each N^-r; one fixed budget C*P*A*(2L^2)^(D+1) bounds every actual coefficient. Above-degree coefficients are genuinely zero. Short original N<T0 uses Q=1, actual circle half-norm and T0^(D+1); every positive N is covered. Zero dimension is retained by genuine empty-coordinate cube/index results.', 'ScalarMvPhaseDegreeStep is CONDITIONAL ONLY on the smaller-degree all-coefficient small-value IH for every positive density<=1. That IH is NOT discharged for arbitrary D. The degree-one corollary IS UNCONDITIONAL: it explicitly supplies the already PROVED degree-zero estimate for each mu. No arbitrary-degree inverse or complete original target follows merely from this step.', 'The generic finite orbit discrepancy has actual Haar and actual finite mean, not an interface accepting arbitrary discrepancy. All integrals are genuinely integrable by compactness. Nonempty finite domains are required exactly for zero-mode cancellation. Actual compact Fourier family, true approximation error and finite sum bound force an actual nonzero character; both eta and K are selected before orbit data and observable.', 'Observable conversion uses the SAME p and SAME original cube. Actual Fourier equality identifies C(k)*p on each original integer sample; its actual degree is proved. One original phase multiplier q is retained for all coefficients, then multiplied by true k.natAbs. The proved modular natAbs equality covers negative k; no quotient-circle division is used. The observable degree step remains dependent on smaller-degree IH; its degree-one corollary is genuinely unconditional.', 'The genuine norm bump uses the actual original filtered sample cardinality, actual Haar support estimate and actual finite mean. Coarse control is only for positive-weight coefficients and is independent of epsilon. Original constant recovery and positive/zero-epsilon refinement still need proof for all multivariable degrees. The true natural multiples preserve actual original sample sets, including m=0; their degree and evaluation identities are proved.', 'NEXT finish the actual multivariable small-value refinement and constant/zero-error recovery, then close the paired natural-degree induction. The first remaining step is true same-dense-multiplier-index selection over the fixed positive multiindex set, followed by actual scalar strong linear recurrence and a genuine common product. Scalar sample constant recovery must use actual INTEGER monomials and actual original cube bounds. No full StrongConjecture or full corrected Leibman/nilsequence input is proved yet.', 'Primary route: fixed OpenAI Section 06_rough_progressions, true equal-cube short-line averaging and corrected multiparameter coefficient reconstruction. All old sources and axiom sets retained; fixed-data constants only, no power-law delta rates. Author verification only, not independent kernel replay or external peer review.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: actual scalar multiparameter phase/observable/coarse degree steps with explicit lower-degree small-value IH and unconditional degree-one cases; actual uniform finite Fourier/bump/natural-multiple bridges; full induction/general nilsequence still open')
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
