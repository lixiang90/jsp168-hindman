"""Audit actual finite vertical reconstruction and native Fourier discrepancy detection.

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

PREFIX = 'round-native-central-reconstruction'
OLD = 'round-native-central-fourier'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/UnitTorusPeakKernel.lean', 'Hindman168/UnitTorusKernelEvaluation.lean', 'Hindman168/UnitTorusPeakConvergence.lean', 'Hindman168/CompactTorusPeakApproximation.lean', 'Hindman168/UnitTorusFourierKernelEvaluation.lean', 'Hindman168/NativeCentralFourierReconstruction.lean', 'Hindman168/NativeCentralFourierCompactFamilies.lean', 'Hindman168/NativeNilmanifoldFiniteDiscrepancy.lean', 'Hindman168/NativeCentralFourierSelection.lean']
COMPONENTS = ['ACTUAL standard central torus peak base c(t)=1/(1+dist(t,0)) is positive continuous and has its UNIQUE maximum at the identity. Every ACTUAL original explicit Pi(circle Haar) integral of c^n is POSITIVE; actual normalized complex kernel is constructed using this genuine integral. Its ACTUAL integral norm equals ONE, including zero-dimensional tori. No peak kernel or positive normalization existence hypothesis.', 'ACTUAL explicit product-Haar kernel evaluation is genuinely integrable on compact tori. Exact observable/kernel subtraction and true sup norm product bound are proved. The genuinely normalized peak kernel has evaluation operator norm at most ONE from its ACTUAL integral norm one, not its potentially large uniform norm.', 'ACTUAL constructed peak-kernel evaluation equals original positive-mass-normalized real peak integral. Actual unique maximum, compactness, original product Haar open positivity and original observable continuity discharge ALL peak convergence hypotheses. True convergence to ORIGINAL identity evaluation and true eventually arbitrarily small error are proved for each original continuous orbital function.', 'ONE ACTUAL normalized peak kernel approximates identity evaluation for an ENTIRE fixed COMPACT uniform-norm family. Genuine finite cover and actual finitely many eventually-close estimates give a common actual n. TRUE operator norm one and point evaluation contraction transfer estimates to every family member. No pointwise-to-uniform convergence assumption.', 'ACTUAL finite Fourier polynomial kernel evaluation is EXACT finite sum of true Fourier integrals under EXPLICIT Pi(circle Haar), with integrability checked for each term. ONE fixed finite Fourier kernel, selected by actual normalized peak kernel approximation followed by genuine uniform Fourier approximation of THAT fixed kernel, reconstructs identity evaluation on every member of a fixed compact sup-one family. No frequency-count/tolerance circularity and no per-orbit guessed coefficients.', 'ACTUAL native finite VERTICAL FOURIER RECONSTRUCTION is genuinely proved for EVERY ORIGINAL NativeNilmanifoldData(s), including nonabelian and NONNORMAL original lattices, in its ORIGINAL specified compatible metric. One ACTUAL finite coefficient list precedes ALL ORIGINAL unit Lipschitz observables F and ALL original quotient points q, and its finite sum of ACTUAL nativeCentralFourierProjection at signed frequencies uniformly approximates F to any fixed positive tolerance. Original compact orbital family supplies ALL generic compactness/bound hypotheses; true exact signed integral identity retains original action, observable, group, lattice and Haar. No original action Lipschitz distortion estimate assumed.', 'ACTUAL original continuous vertical Fourier projection respects subtraction and is a contraction as a map of UNIFORM-NORM FUNCTION SPACES. Its image of ALL original unit Lipschitz observables is ACTUALLY compact. This does NOT assert that projected observables are unit Lipschitz on ORIGINAL quotient points; compatible metric topology alone gives no such spatial bound.', 'ACTUAL finite sampling minus CONSTRUCTED original quotient probability integral defines a genuine complex-linear discrepancy functional on ORIGINAL metric continuous observables. True norm bound 2*uniform norm and true NONZERO-frequency projected discrepancy equals ORIGINAL finite mean are proved using ACTUAL original continuous integrability and actual proved nonzero mean zero. Empty sample behavior is retained; original Gamma not assumed normal.', 'ACTUAL one fixed finite central-frequency list and a fixed POSITIVE detection threshold are genuinely produced before ALL original samples, orbit maps and unit observables. Every large ORIGINAL native Haar discrepancy gives a genuinely large discrepancy of an ACTUAL vertical projection at some frequency in that list. Actual uniform reconstruction and true linearity/norm budget prove this selection. TRUE fixed NATURAL l1 frequency bound and actual ZERO-mode-discrepancy OR NONZERO-mode original finite mean alternative are genuinely produced with the SAME fixed list and threshold. ZERO frequency must descend to lower-dimensional central quotient; NONZERO frequencies have actual zero Haar mean. No nonabelian inverse or zero-mode descent hypothesis is smuggled in.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The full original positive distinct rapidly separated monochromatic finite sums/products prize statement remains the goal, not an analytic subgoal. ALL retained genuine scalar single/multivariable phase/observable/small-value and standard target-torus monomial/binomial inverses, native ABELIAN original-metric monomial/binomial/equal-cube/real-box obstructions, original filtered lattice/horizontal classification/operator norm/fixed native grids, group bi-invariant Haar and original nonnormal normalized quotient probability remain proved. ACTUAL original compact central torus action, metric continuity and native probability preservation, compact orbital families, continuous contractive vertical Fourier projections/eigenrelations/nonzero Haar mean zero/orthogonality remain retained. ACTUAL finite vertical reconstruction uniformly for ALL ORIGINAL unit observables and actual fixed finite central-frequency discrepancy detection are NOW genuinely proved. Zero central frequency is allowed; its ACTUAL lower-dimensional original center quotient descent and compatible quotient measure must be constructed next. Projected observable families are compact in uniform norm, not asserted spatially unit Lipschitz under arbitrary compatible metric. Next identify actual quotient/fiber probability measures, descend zero-frequency observables, prove original finite-difference/product-group polynomial compatibility and NONABELIAN derivative/quantitative Leibman induction with fixed-data existence bounds, not unproved power laws. Canonical-measure abelian inverse/root assembly, generic finite-index rough API transport, original bad-index residue/full Haar dichotomy to affine t*v+b and scales Z/t, actual finite obstruction density/descent, full rough-step comparison, dimension/length/cofinal-scale assembly remain open. HasNativePeriodicIntervalInverse is a SEPARATE interval Gowers-to-finite-list nilsequence CORRELATION inverse, not orbit quantitative Leibman; it remains unproved. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment and HasAlignmentMonomialRecurrence remain unproved. Final original ordered positive rapidly separated monochromatic FS/FP extraction remains open. Retain actual disproved unrestricted short-box O(eps) small-value counterexample; corrected route uses a large-N threshold and coarse all-N bounds, so this is no unavoidable full-goal blocker. Author-side verification only: full builds, strict source/census/hash and standard-axiom audits are not independent kernel replay or external peer review. No public repository, PR or prize application has been created/submitted; do so only at actual completion or genuine unavoidable obstruction with honest scope.'

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
    review = dict(date='2026-10-12', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: ACTUAL finite original vertical Fourier reconstruction and fixed finite central-frequency native discrepancy detection; zero-frequency descent/nonabelian quantitative Leibman/full prize theorem open')
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
