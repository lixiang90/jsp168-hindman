"""Audit actual child-metric compact zero-mode regularity and fixed finite unit-family discrepancy detection.

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

PREFIX = 'round-native-child-regularity'
OLD = 'round-native-probability-uniqueness'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeCentralChildZeroObservable.lean', 'Hindman168/CompactLipschitzAlgebra.lean', 'Hindman168/CompactLipschitzApproximation.lean', 'Hindman168/NativeCentralChildRegularFamily.lean', 'Hindman168/NativeCentralChildDiscrepancy.lean', 'Hindman168/LinearDiscrepancyStability.lean', 'Hindman168/NativeCentralChildRegularDetection.lean', 'Hindman168/BoundedLipschitzNormalization.lean', 'Hindman168/NativeCentralChildUnitDetection.lean']
COMPONENTS = ['The SAME original descended zero observable is represented as a continuous function in the ACTUAL child specified metric, using its proved quotient topology equality. Pointwise values at the ACTUAL factor projection, subtraction and original uniform norm contraction are proved; no spatial Lipschitz bound is inferred from topology equality.', 'Actual spatial Lipschitz complex functions form a star subalgebra on ANY compact metric space. Genuine bounded product estimates and complex conjugation prove closure; actual distance functions separate distinct points.', 'Genuine Stone-Weierstrass gives uniform density of actual spatial Lipschitz functions on ANY compact metric space. A compact family admits ONE FIXED finite approximant list before all its members, with genuine shared positive amplitude and spatial Lipschitz bounds obtained from finite sums.', 'The actual child zero-observable map is Lipschitz ONE in uniform FUNCTIONSPACE norms, not asserted spatially Lipschitz on child points. Its actual image of the original unit-observable family is compact in the child specified metric function space. All generic finite regular approximation hypotheses are discharged from this actual family.', 'The actual original zero-projection finite discrepancy equals actual child-metric finite discrepancy with genuine child canonical Haar, SAME original sample set and ACTUAL factor images. No replacement samples, measure agreement assumption or unit spatial regularity premise.', 'Actual complex linear discrepancies of norm at most TWO have uniform approximation error less than twice the uniform function error. Genuine triangle inequalities give positive approximant discrepancy detection.', 'ONE FIXED finite bounded spatial-Lipschitz child family detects EVERY original unit-observable zero-mode discrepancy at least eta, retaining discrepancy greater than eta/2 on the SAME projected samples and actual child canonical Haar. Family and all bounds are fixed BEFORE original observables and arbitrary finite samples.', 'Actual common positive scaling sends bounded spatial-Lipschitz continuous functions into the actual unit Lipschitz observable family. Exact linear discrepancy scaling and norm identity are proved; no original descended unit regularity is assumed.', 'ONE FIXED finite ACTUAL UNIT child family and a FIXED POSITIVE threshold detect all original zero-mode discrepancies uniformly before arbitrary original samples and observables. All compactness, approximation, normalization and canonical Haar hypotheses are now discharged. The child orbit inverse itself and nonzero-frequency induction are still unproved.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic FS/FP remains prize target. ALL retained scalar/standard-torus/native ABELIAN inverse/obstructions, original group/quotient Haar, central Fourier reconstruction/finite frequency detection, original zero-mode descent and actual low-step child native data/metric/exp-log projection, actual relatively compact measurable section/counting lift and compact finite Haar scalar classification remain proved. ACTUAL transversal restriction/counting recovery now EXACTLY recovers original arbitrary base nu with probability mass ONE. GENERAL ORIGINAL NONNORMAL invariant coset probability uniqueness is NOW genuinely proved by actual group Haar scalar normalization and actual original fundamental-domain independence. ACTUAL original center-factor pushforward probability NOW equals genuine child NativeData(s-1) canonical Haar, under actual PROVED Borel sigma-algebra compatibility; true zero-mode child canonical integral/discrepancy identities retain SAME original samples/observables. No normal-lattice converse or homogeneous uniqueness/measure agreement input remains in this compatibility step. The actual child-metric zero-mode family now has genuine uniform compactness and spatial Lipschitz approximation, with one fixed finite ACTUAL UNIT child family and positive fixed discrepancy threshold before all original observables and finite sample sets. SAME actual projected samples and child canonical Haar are retained. No topology-to-Lipschitz inference or assumed descended spatial regularity remains in this step. NEXT prove actual child horizontal character/coefficient/operator bounds pullback through original model projection, and assemble child orbit inverse induction; the child orbit inverse is still unproved. Then genuine original nonzero central-frequency derivative/product-group polynomial compatibility and NONABELIAN quantitative Leibman induction, fixed-data existence bounds only and no unsupported power laws. Projected/descended families are actual uniform-norm compact, not asserted spatially unit Lipschitz. Canonical-measure abelian root assembly, generic finite-index rough API, actual original residue affine/scales finite obstruction density/descent, full rough-step/dimension/length/cofinal-scale comparison remain open. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence input remains unproved; it is distinct from orbit quantitative Leibman. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final original positive ordered separated FS/FP extraction remain unproved. Retain corrected large-N scope/actual unrestricted short-box O(eps) counterexample; no unavoidable full-goal blocker. Author build/hash/source/standard-axiom audits are not independent kernel replay or external peer review. No public repository, PR or prize submission yet; do so at actual completion or genuine unavoidable obstruction with honest scope.'

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
        reference_scope='06_rough_progressions: ACTUAL compatible-metric child zero-mode compact regularity, finite spatial Lipschitz approximation and genuine fixed unit-family discrepancy detection; child orbit inverse/nonzero-frequency quantitative Leibman/full prize theorem open')
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
