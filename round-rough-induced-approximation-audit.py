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

PREFIX = 'round-rough-induced-approximation'
OLD = 'round-rough-slow-freezing'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughUniformLipschitzApproximation.lean', 'Hindman168/RoughCompactFamilyApproximation.lean', 'Hindman168/RoughScalarFamilyApproximation.lean', 'Hindman168/RoughNativeOrbitSourceMetric.lean', 'Hindman168/RoughNativeOrbitApproximation.lean', 'Hindman168/RoughFiniteFamilyApproximation.lean', 'Hindman168/RoughNativeKernelApproximation.lean', 'Hindman168/RoughNativeFiniteResidueApproximation.lean', 'Hindman168/RoughFamilyApproximateDiscrepancy.lean', 'Hindman168/RoughFrozenApproximateDiscrepancy.lean']
COMPONENTS = ['RoughUniformLipschitzApproximation constructs actual bounded real Lipschitz approximants by infima of distance cones. One K=2B/delta precedes every function with the specified common bound and modulus. Uniform approximation error is at most epsilon and the same supremum bound B is preserved.', 'RoughCompactFamilyApproximation derives the common modulus from a jointly continuous map on an actual compact product. One approximant Lipschitz constant precedes every left parameter and every original Lip-Lipschitz test bounded by B. No smooth metric or Lipschitz regularity of the map is assumed.', 'RoughScalarFamilyApproximation restricts the actual left scalar parameter to the compact interval [-R,R], retaining one constant before every scalar and original test.', 'RoughNativeOrbitSourceMetric defines the metric on the actual conjugate subgroup quotient by pulling back the original specified nilmanifold metric through the proved injective orbit map at left identity. For a compact source it proves equality with the natural quotient topology and compactness in the pulled-back metric. No normality or replacement of the original quotient is assumed.', 'RoughNativeOrbitApproximation proves joint scalar orbit continuity in these actual metrics by composing the original native scalar action with the isometric orbit inclusion. On any actual compact conjugate subgroup quotient it obtains uniformly bounded Lipschitz approximants for the induced original tests.', 'RoughFiniteFamilyApproximation combines a finite dependent family of actual compact source spaces with one shared approximant constant, the sum of the individual constants. The constant precedes the residue index, scalar parameter, original observable and approximation function.', 'RoughNativeKernelApproximation applies the actual rational character-kernel conjugated lattice compactness theorem, discharging source compactness rather than assuming it, and obtains the induced-test approximants on each actual residue kernel quotient.', 'RoughNativeFiniteResidueApproximation applies the finite family theorem to all actual residue character-kernel quotients, each with its proved compact pulled-back metric. A single constant works for the finite family before its residue index, bounded left scalar and original test are chosen.', 'RoughFamilyApproximateDiscrepancy proves that a uniformly chosen bounded Lipschitz approximant retains finite probability discrepancy at least eta-2epsilon on every member of the dependent compact family.', 'RoughFrozenApproximateDiscrepancy accounts for BOTH actual freezing error and approximation error under both original finite probability laws. Retained discrepancy is at least eta-2(epsilon_freeze+epsilon_approx), with estimates needed only on the original supports.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Uniform prescribed-error Lipschitz approximation for induced tests on actual compact conjugate kernel quotients is now proved, including a single constant for all members of a fixed finite residue family and compact left scalar parameters. The pulled-back source metrics have their actual natural quotient topology and compactness proved; the original metric is retained. The induced tests themselves have not been claimed Lipschitz in arbitrary compatible metrics. Their bounded approximants preserve discrepancy with an explicit two-law error loss, combined with the proved freezing loss. Exact original residue sampling weights, mixture disintegration, subbox partition geometry and assembly with convex selection remain open. The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Section 06 passes from frozen original tests to compact smaller character-kernel quotients. The paper specifies a smooth metric, while NativeNilmanifoldData specifies only a compatible metric. The new proof supplies the prescribed-error conclusion needed for induction via Lipschitz approximation, not an unsupported assertion that smooth induced tests are Lipschitz in every compatible metric.', 'The exact source quotient is L/(conjugate(Gamma,sigma).comap L.subtype). Its metric is pulled back via hDelta -> h*sigma Gamma, whose injectivity and closed embedding were previously proved without normality. Both its natural quotient topology equality and compactness in the metric are established. It is not an abstract surrogate space.', 'Scalar orbit continuity is established in the original specified target metric and actual pulled-back source metric. It uses the original continuous action exp(tV) on the original quotient, with exp(tV)*h*sigma in exactly that multiplication order.', 'The infimum cone approximant is bounded below by -B and above by f(x), so its infimum is legitimate and the same absolute bound B holds. The near-distance modulus and far-distance 2B bound give f-epsilon <= g <= f. The common constant depends on B and the fixed positive modulus scale, not on a later test.', 'For a fixed finite family of residues and fixed original V and rational kernel, the common constant precedes every residue index, bounded scalar left factor, original Lip-Lipschitz bounded test and original finite probability mass. It can depend on fixed native data, the finite residue family, R,B,Lip and epsilon. No uniformity in a later-changing residue family or epsilon tending to zero is claimed.', 'The actual kernel wrapper retains all rationality hypotheses on S, the character and V, and discharges quotient compactness from the previously proved rational conjugated lattice theorem. Nonempty quotient instances follow from their actual group quotient, not an extra existence assumption.', 'Both finite probability laws pay their own approximation error. Combined freezing and approximation retain eta-2(epsilon_freeze+epsilon_approx). Applying an approximant without this loss would be invalid and is not done here.', 'These results supply the regularity supporting step. They do not prove smaller-dimensional uniform equidistribution, native-data packaging of the smaller nilmanifold, the quantitative obstruction, original residue sampling weights or the final StrongConjecture.', 'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions compact induced tests and finite-residue Lipschitz approximation with explicit discrepancy loss')
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
