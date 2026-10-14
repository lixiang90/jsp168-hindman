"""Audit actual low-step native center quotient data and nonnormal coset lattice-counting lifts.

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

PREFIX = 'round-native-quotient-counting'
OLD = 'round-native-central-descent'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeCentralFactorMetric.lean', 'Hindman168/NativeCentralQuotientData.lean', 'Hindman168/NativeCentralQuotientProjection.lean', 'Hindman168/MeasurableTransversalEquivalence.lean', 'Hindman168/NativeNilmanifoldMeasurableSection.lean', 'Hindman168/CosetSectionCoordinates.lean', 'Hindman168/CosetSectionCountingLift.lean', 'Hindman168/CosetSectionCountingInvariance.lean', 'Hindman168/NativeNilmanifoldCountingLift.lean']
COMPONENTS = ['ACTUAL ORIGINAL central factor/image lattice receives a compatible metric from genuine original center quotient second countability and true original image lattice discreteness/cocompactness. Exact metric topology equality and original quotient OPEN map are proved. No metric invariance or spatial Lipschitz distortion assumed.', 'ACTUAL ORIGINAL center quotient native data of step s-1 is CONSTRUCTED with original separated model quotient, original quotient group, ACTUAL proved original quotient smooth Lie chart/operations, actual simple connectedness, original image lattice and actual compatible metric. True ORIGINAL quotient class bound is proved and nontrivial original G gives STRICT model dimension decrease. No child native-data existence hypothesis.', 'ACTUAL original exponential/logarithm commute with actual original quotient homomorphism/model projection in the CONSTRUCTED child NativeNilmanifoldData. The exact constructed group/chart/model/Lie instances are retained; no replacement polynomial representation or logarithm assumption.', 'ACTUAL continuous injective restriction to a MEASURABLE transversal in a Polish original space gives a genuinely MEASURABLE EQUIVALENCE onto actual cosets. True actual coverage gives surjectivity, Lusin-Souslin gives actual measurable inverse. No continuous selector is assumed.', 'ACTUAL relatively compact original native measurable transversal is constructed with POINTWISE original coset injectivity/coverage retained in spec, from retained finite-patch construction. True measurable equivalence gives an ACTUAL measurable section for ORIGINAL nonnormal cosets, with genuine RIGHT inverse and ACTUAL COMPACT value-range bound. No section existence/compactness/measurability assumption at native root.', 'ACTUAL original section decomposes original G bijectively as ORIGINAL cosets times ORIGINAL lattice elements by (q,gamma) maps to tau(q)*gamma. Explicit inverse is actual pi(g) and tau(pi(g))^-1*g in ORIGINAL Gamma. Both directions are genuinely MEASURABLE under original Borel group operations. No original Gamma normality or quotient-group structure on G/Gamma.', 'ACTUAL coset counting lift is defined as map(actual measurable sheet equivalence,nu times ORIGINAL lattice COUNT measure). Genuine sigma-finiteness for sigma-finite original nu and original countable Gamma, actual measurable-set counting-fiber formula and ACTUAL Tonelli/sheet-tsum integral formula are proved. Haar/local finiteness or homogeneous probability uniqueness is NOT assumed or yet claimed.', 'ACTUAL original left group action permutes actual original lattice sheets by genuine gamma cocycle; true equivalence reindexing proves actual nonnegative periodization translation identity. Actual original base-measure group translate invariance then proves counting lift is LEFT-INVARIANT using actual Tonelli formula and actual measurable periodization, without normality or hidden Haar uniqueness input.', 'ACTUAL original native measurable section supplies ALL measurable decomposition/counting lift inputs for EVERY NativeNilmanifoldData(s). True sigma-finite counting lift of any actual original coset probability and genuine left-invariant counting lift of any actual original group-invariant base measure are proved. STILL must prove local compact finiteness/nonzero/open positivity, apply genuine group Haar uniqueness and normalize to identify arbitrary invariant coset probability with original canonical Haar; general compatibility/full target open.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic FS/FP remains prize target. ALL retained scalar/standard target-torus/native ABELIAN inverse/real-box obstructions, original filtered lattice/horizontal/grid/operator data, original group and nonnormal quotient Haar, genuine central torus/Fourier reconstruction/frequency detection/zero-mode factor descent and original invariant factor pushforward probability remain proved. ACTUAL compatible central factor metric and GENUINE step s-1 child native data, strict dimension decrease for nontrivial G and exact original exp/log projection compatibility are NOW constructed/proved. ACTUAL relatively compact measurable original coset section, actual measurable original coset-times-lattice decomposition and genuine sigma-finite left-invariant lattice-counting lift are NOW proved. Counting lift is not yet proved Haar: NEXT prove actual local compact finiteness from actual compact section-range bound and original discrete-lattice compact intersections, actual nonzero/full-support/open positivity, then genuine GROUP Haar uniqueness and normalization. Use this actual lift to prove GENERAL NONNORMAL homogeneous invariant probability uniqueness and identify original central factor pushforward probability with separately constructed child canonical quotient Haar, including actual Borel sigma-algebra compatibility. Mathlib normal-lattice converse cannot be substituted for this work. Compact descended/projected observable families are not asserted spatially Lipschitz; true regularity approximation and actual nonabelian finite-difference/product-group polynomial compatibility/quantitative Leibman induction remain. Fixed-data existence bounds only, no unsupported power laws. Canonical-measure abelian root assembly, arbitrary finite-index rough API, original residue affine/scales finite obstruction density/descent, full rough-step comparison/dimension/length/cofinal scales remain open. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence input remains unproved; it is not orbit quantitative Leibman. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final original ordered positive separated FS/FP remain open. Retain corrected large-N scope and actual unrestricted short-box O(eps) counterexample; no unavoidable full-goal obstruction. Author build/hash/source/standard-axiom audits are not independent kernel replay or external peer review. No public repo/PR/prize submission yet; do so at actual completion or genuine unavoidable obstruction with honest scope.'

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
        reference_scope='06_rough_progressions: ACTUAL lower-step native original center quotient and actual nonnormal measurable coset/lattice counting lift; lifted Haar/local finiteness and canonical factor measure compatibility/nonabelian quantitative Leibman/full prize theorem open')
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
