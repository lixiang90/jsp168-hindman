"""Audit actual restricted/image lattice rational layer geometry and both original native polynomial normalizations.

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

PREFIX = 'round-native-relative-layer-rational'
OLD = 'round-native-relative-filtered-degree'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeLieFilteredLayerSubalgebra.lean', 'Hindman168/NativeLinearStepFiltered.lean', 'Hindman168/NativeLinearStepHorizontal.lean', 'Hindman168/NativeLinearStepPolynomial.lean', 'Hindman168/NativeLinearStepSamples.lean', 'Hindman168/NativeRelativeLayerLatticeGeometry.lean', 'Hindman168/NativeRelativeLayerLieSubalgebras.lean', 'Hindman168/NativeRelativeLieLayerRational.lean', 'Hindman168/NativeRelativeRationalInclusion.lean', 'Hindman168/NativeRelativeReducedLayerRational.lean', 'Hindman168/NativeRelativeReducedLieInitial.lean', 'Hindman168/NativeRelativeReductionRationalSpan.lean', 'Hindman168/NativeTwoNormalizations.lean', 'Hindman168/RationalRealSpanTransport.lean']
COMPONENTS = ['True original relative native inclusion preserves AND reflects rational directions against actual restricted/product lattices, by genuine original Exp inclusion and positive integer power membership. Real-span comap transport lifts all rational generators and uses actual ambient-layer containment in the native inclusion range; all internal relative Lie layers, including ZERO, are now rational for SAME actual restricted lattice.', 'The actual smooth terminal quotient projection sends original lattice logarithms EXACTLY to actual image lattice logarithms. Their actual Q-linear spans map EXACTLY. Every actual projected reduced Lie layer is rational for SAME actual image lattice, via full real-span transport, with no closedness-to-rationality assumption.', 'Genuine native Lie subalgebras are constructed for ALL actual internal relative/reduced layers, with all bracket/antitone inputs discharged. Exact native Log membership identifies their native Exp subgroups LITERALLY with actual original layers. ALL actual lattice intersections are discrete, ALL layer quotients are compact, natural quotient inclusions are closed embeddings and original quotient orbits compact.', 'BOTH actual reduced Lie initial layers ZERO and ONE are TOP, from genuine native Exp/Log and proved group initial layers. Actual reduced image filtration retains proved brackets, rationality and terminal degree decrease; SAME native nilpotency-step bound s remains unchanged.', 'Original P(n)*gamma^(-n) is NOW a genuine native logarithmic coefficient polynomial with EXACT real product-log evaluation and actual integer exponential powers for positive/zero/negative samples. Original Lie weights and SAME stretch d survive, including basepoint source polynomials of ordinary degree s*d. Genuine real/integer filteredness and zero-trim ordinary degree at most s*d are proved without enlarging the original filtration.', 'Actual original lattice right correction preserves EVERY original nonnormal lattice coset sample, retains starting zero, and puts ACTUAL P(1) in ONE FIXED compact original representative set. ONE FIXED nonnegative original Log-norm bound is chosen before ALL original polynomials and horizontal characters. Representatives of P(1)^h are no longer substituted for a bound on ACTUAL P(1).', 'COMPLETE original horizontal scalar polynomial under lattice linear-step correction changes EXACTLY by -f(Log gamma)*X(). ALL non-linear coefficients are unchanged. For ACTUAL original lattice-integral functionals ALL scalar coefficients change by integers. Combined basepoint/linear-step normalization retains EVERY ORIGINAL nonconstant scalar coefficient modulo integers.', 'BOTH Green-Tao normalizations NOW have an actual original application for EVERY original ordinary-degree-bounded univariate polynomial with arbitrary starting values and UNBOUNDED coefficients. A SINGLE fixed original compact set contains both true representatives r,a; normalized zero is identity, true normalized P(1)=a has fixed Log-norm bound, all original samples are recovered by the actual basepoint translation, and SAME original stretch/weights/filteredness/degree bound are proved. No quantitative inverse conclusion is assumed.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Actual original normalized univariate relative/reduced polynomial weights, real/integer filteredness and genuine terminal quotient filtration-degree decrease are PROVED for arbitrary starting values, representatives, shifts and UNBOUNDED coefficients. ALL actual internal relative/reduced image Lie layers are NOW RATIONAL against SAME actual restricted/image lattices, with true Exp subgroup identities, actual discrete lattice intersections, compact layer quotients, closed natural quotient embeddings and compact original quotient orbits. Actual reduced group layers are closed/contractible/connected/simply connected; Lie initial layers zero/one are top. Actual original lattice linear-step polynomial P(n)*gamma^(-n) and BOTH original Green-Tao normalizations are NOW PROVED with original nonnormal coset samples, SAME stretch d/weights/filteredness, normalized zero identity, ACTUAL normalized P(1) in ONE FIXED compact original set with ONE FIXED Log-norm bound, and EVERY ORIGINAL nonconstant horizontal scalar coefficient preserved modulo integers for actual lattice-integral functionals. Compact choices precede ALL original polynomials and characters; no bound on original coefficients or gamma is assumed. NEXT: arbitrary native rational Lie-filtered recursive square/terminal quotient geometry and degree induction; weighted-input relative polynomial reconstruction feeding ACTUAL twice-normalized source without substituting ordinary-degree enlargement; ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction/pullback with genuine finite-list/operator/binomial bounds. SAME native nilpotency-step bound s is unchanged; actual reduced image filtration is NOT assumed another stretched lower-central series. Existing one-step original degree reduction does not by itself supply indefinite recursion. The univariate result does not supply the corrected equal-side multivariate inverse; justify that reduction or prove the multivariate branch. Fixed-data existence bounds only, no unsupported power laws or bounded original coefficients. Preserve corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample, which does not obstruct the corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION inverse remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports are preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute the authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.'

def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}


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
    review = dict(date='2026-10-12', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions and Green-Tao section 7: actual internal relative/reduced lattice rational layers and both original normalizations; arbitrary rational-filtered recursion/nonzero inverse/full prize theorem open')
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
    review.update(mathematical_review_file=PREFIX+'-mathematical-review.txt', mathematical_review_sha256=digest(PREFIX+'-mathematical-review.txt'))
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
