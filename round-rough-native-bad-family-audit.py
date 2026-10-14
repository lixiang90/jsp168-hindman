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

PREFIX = 'round-rough-native-bad-family'
OLD = 'round-rough-native-piece-descent'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughNativeBadIndex.lean', 'Hindman168/RoughNativeModelBadIndex.lean', 'Hindman168/RoughNativeBadProgressionThinning.lean', 'Hindman168/RoughCofinalSubsequences.lean', 'Hindman168/RoughNativeBadFamily.lean', 'Hindman168/RoughNativeSmallerBadFamily.lean', 'Hindman168/RoughNativeModelBadFamily.lean', 'Hindman168/RoughNativeZeroDimension.lean']
COMPONENTS = ['RoughNativeBadIndex defines an actual discrepant pair of nonempty finite box samples on the specified native quotient, with uniformly bounded Lipschitz real observable and both endpoint bounds. Upper-bound relaxation and exact progression reparametrization are proved.', 'RoughNativeModelBadIndex constructs these actual bad-index witnesses from the original coefficient models, native map and original discrepancy, using the previous actual freezing, approximation and rescaled sampling construction. It retains strict dimension decrease and all-real joint native logarithm polynomiality.', 'RoughNativeBadProgressionThinning fixes a common residue vector and native quotient on a long progression, constructs its exact jointly polynomial map, and retains actual discrepancy at every index, the original dyadic interval, roughness and smoothness of the new positive difference.', 'RoughCofinalSubsequences upgrades finite simultaneous length/scale cofinal choice to a genuine strictly increasing scale subsequence at each prescribed length when witnesses restrict to shorter lengths. Fixed rescaling and subsequence extraction preserve power domination.', 'RoughNativeBadFamily defines the full finite actual native bad progression data, with one joint logarithmic polynomial, positive smooth difference, rough dyadic progression and varying boxes/tests. Restriction to shorter lengths is proved. One fixed smaller quotient works at every length along strictly increasing scale subsequences, preserving scale divergence and power domination.', 'RoughNativeSmallerBadFamily packages the actual fixed-label thinning conclusion as a finite bad progression family in the strictly smaller native group. The per-index hypotheses are actual quotient sampling discrepancies, rather than an abstract predicate.', 'RoughNativeModelBadFamily assembles original per-index coefficient models, varying original boxes and observables, actual original discrepancies and common native polynomial into one complete finite smaller-dimensional bad progression family. Partition count and new Lipschitz bound precede the desired length; the required source length precedes varying polynomial data. Generated splitting degrees are derived, and discrepancy is not divided by piece count.', 'RoughNativeZeroDimension proves the dimension-zero induction base: the actual native group and quotient are singletons, both nonempty uniform laws have total one, so no positive bad-index discrepancy or nonempty bad progression family is possible.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual finite smaller-dimensional bad progression families are now assembled from original coefficient models and actual per-index discrepancies, with a common native logarithmic polynomial, uniform degree/box/test/discrepancy bounds, and rough smooth-step progression. Finite quotient selection now gives genuine lengthwise strictly increasing scale subsequences, preserving scale divergence and power domination; the zero-dimensional induction base is proved. The quantitative Leibman obstruction and its fixed finite nonzero character list must still supply the original coefficient obstructions, including corrected arbitrary-box comparison and stretched-filtration applicability. Apply the already proved actual affine obstruction interpolation and constant-term fractional thinning uniformly to entire bad families, connect the arithmetic large-scale thresholds and positive fixed discrepancy budgets to the new native model bad-family constructor, and finish dimension induction. Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
    review = dict(date='2026-10-11',classification='PROGRESS',full_target_proved=False,
        application_review=COMPONENTS+['The Prop definitions record actual native group maps, finite sampling supports and real observables. They are not axioms, external truth assumptions or assertions that bad families exist.', 'The model bad-family theorem constructs every selected discrepancy through the previous proved single-index descent and then finite van der Waerden thinning. It does not assume the desired smaller bad family as a premise.', 'Source progression length may depend on requested length and fixed finite labels. Partition count, finite quotient family, Lipschitz bound, discrepancy budget and degree transformation do not depend on requested length.', 'The chosen residue vector is common only on the selected finite progression; it may vary with scale or length. It enters the polynomial coefficients, not the chosen quotient lattice. Only the finite coset index must be fixed for the dimension induction.', 'The same group-valued map handles every retained progression index. Its native logarithm is an actual vector polynomial at all real simultaneous progression and spatial parameters. Arbitrary changing boxes and observables remain permitted.', 'Length downward closure is proved for actual native bad-family witnesses. Joint cofinal length/scale choice without this closure would not by itself imply infinitely many scales at a fixed prescribed length; the new proof explicitly uses closure before extracting strictly increasing subsequences.', 'Scale divergence is retained separately from power domination. Finite choice and increasing subsequences do not silently replace the original asymptotic growth hypotheses.', 'Dimension-zero discrepancies vanish using both positive-cardinality hypotheses. Uniform masses on an empty set have zero total, and are not falsely treated as probabilities.', 'The original nonzero character, rational direction period, coefficient models and initial bad-family data remain explicit prerequisites. The theorem does not provide the missing quantitative Leibman input or assert a completed rough-step theorem.', 'The new native families currently use real observables. The complex-observable formulation in the paper still needs an explicit real-component reduction when the full proposition is assembled.', 'Paper comparison covers pinned 06_rough_progressions lines 314-359 and 553-584: fixed lengthwise subsequences, finite group choice, zero-dimensional base, varying tests and boxes, and smaller-dimensional family construction.', 'All retained proof sources and transitive axiom sets are unchanged; fresh focused checks, full build, axiom reports and pinned paper checks are author-side verification.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual smaller native bad families, lengthwise scale subsequences and zero-dimensional base')
    manifest=dict(baseline)
    manifest.update(date='2026-10-11',files=files,hindman_module_count=summary['project_modules'],
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
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-11 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
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
