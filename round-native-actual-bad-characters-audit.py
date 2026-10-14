"""Audit actual complex freezing, genuine short progression and smaller-filtration UNIT child signal.

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

PREFIX = 'round-native-actual-bad-characters'
OLD = 'round-native-original-real-box'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughSpatialAffineSubstitution.lean', 'Hindman168/RoughResidueBoxNormalization.lean', 'Hindman168/NativeOriginalResidueBoxObstruction.lean', 'Hindman168/NativeOriginalBadPairCharacters.lean', 'Hindman168/RoughNativeRealBadIndexComplex.lean', 'Hindman168/NativeOriginalRealBadPairCharacters.lean', 'Hindman168/RoughOriginalBadPairScaleThresholds.lean', 'Hindman168/NativeOriginalAsymptoticBadPairCharacters.lean']
COMPONENTS = ['ACTUAL original residue classes reduce modulo the positive step and have EXACT normalized complex mean on the genuine quotient integer box. TRUE quotient-box length/location geometry and LITERAL Option-parameter-preserving spatial affine source/evaluation/scalar-projection identities are proved. No equality of vector/source polynomials is inferred from sampled quotient equality.', 'ACTUAL original residue-box Haar discrepancy now PRODUCES one TRUE nonzero original horizontal lattice character in a fixed finite ORIGINAL list, plus ALL positive original spatial affine coefficient rows. It is instantiated by the UNCONDITIONAL general corrected native box theorem. The list, accuracy constant and quotient-scale threshold precede every original step/residue/source/box/parameter/observable. Exact reduced residues are retained as natural basepoints less than the original step.', 'Both ACTUAL original full-box and residue-box Haar branches of a complex bad pair are now closed to one fixed finite ORIGINAL character list and ONE coefficient constant. The SAME character controls ALL positive affine rows; output step is literally 1 OR original t, and all natural affine basepoints are bounded by that step. Real bad pairs embed into the complex statement with EXACT discrepancy and unchanged Lipschitz/norm/geometry/sampling data. No inverse or character-production premise remains.', 'TRUE PowerDominates and actual eventually-positive scales supply ONE source-independent asymptotic threshold for ALL original dyadic steps at once. Original finite character list and coefficient budget are fixed BEFORE ALL scale indices/raw Q/p/steps/boxes/observables. native_original_asymptotic_bad_pair_characters derives ALL positive original affine coefficient rows from ACTUAL RoughNativeBadIndex, with no analytic production premise. Common-character parameter thinning and full native dimension-descent comparison remain to be assembled.']
REMAINING = 'StrongConjecture remains UNPROVED; goal ACTIVE; no unavoidable obstruction established. Complete unconditional native rational-filtration inverse, general original ordinary-degree inverse, corrected native real-box finite-family obstruction, and ACTUAL original full/residue bad-pair character production with ONE fixed original finite character list and ALL positive affine coefficient rows are now proved. True original residue mean/geometry/source identities, exact real-to-complex discrepancy and genuine PowerDominates uniform dyadic threshold are supplied. Remaining: common original character on a smooth parameter subprogression with literal reparametrized source/full rows, simultaneous finite kernel geometry/budgets, true all-native dimension induction and rough progression comparison, distinct interval Gowers correlation inverse, cube/Alignment and final positive distinct rapidly separated monochromatic FS/FP StrongConjecture. Fixed-data constants do not certify explicit delta-power laws. Author checking is not independent replay/external peer review. Repaired source slab estimate is not an unavoidable obstruction. Public repository/PR/prize milestone not reached.'

def declarations():
    result = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}
    return result


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
    write(PREFIX+'-slab-certificate-result.json',run(['python','bracket-slab-volume-counterexample.py'],PREFIX+'-slab-certificate.txt'))
    Path(PREFIX+'-slab-review.json').write_bytes(Path('round-native-rational-fractional-bracket-input-slab-review.json').read_bytes())
    results = []
    saved = obj(PREFIX+'-focused-results.json') if Path(PREFIX+'-focused-results.json').exists() else []
    for p in MODULES:
        prior = next((r for r in saved if r['module']==p), None)
        if (prior and prior['terminal'] and prior['exit_code']==0
            and prior['command']==['lake','env','lean','-DautoImplicit=false',p]
            and prior['source_sha256']==digest(p)
            and prior['log_sha256']==digest(prior['log']) and not read(prior['log']).strip()):
            results.append(prior)
            print('Retained exact explicit check '+p, flush=True)
            continue
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
        code = re.sub(r'\[local instance(?: \d+)?\]', '', helpers.lean_code(read(p)))
        assert not re.search(r'\b(?:set_option|setOptions|instance)\b', code)
        structures = re.findall(r'^\s*structure\s+(\w+)', code, re.M)
        assert structures == (['NativeRationalLieFiltration'] if p.endswith('/NativeRationalLieFiltration.lean') else [])
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
        new_structures=sum(k=='structure' for vs in ds.values() for k,_ in vs),
        new_structure_generated_reports=sum(k=='structure_generated' for vs in ds.values() for k,_ in vs),
        retained_proof_sources_unchanged=True,retained_axiom_sets_unchanged=True,
        standard_axioms_only=True,full_target_proved=False,independent_kernel_replay=False)
    certificate = obj(PREFIX+'-slab-review.json')
    cr = obj(PREFIX+'-slab-certificate-result.json')
    assert cr['terminal'] and cr['exit_code']==0 and cr['log_sha256']==digest(cr['log'])
    assert cr['command']==['python','bracket-slab-volume-counterexample.py']
    assert certificate['violates_displayed_volume_bound'] and not certificate['refutes_proposition_itself'] and not certificate['unavoidable_obstruction']
    from fractions import Fraction as F
    xs = [(F(i['left']),F(i['right']),i['nearby_integer']) for i in certificate['intervals']]
    assert len(xs)==101 and sum((b-a for a,b,k in xs),F(0))==F(1,5)>F(1,200)
    assert all(xs[j][1]<xs[j+1][0] for j in range(100))
    assert all(abs(100*a-k)<=F(1,10) and abs(100*b-k)<=F(1,10) for a,b,k in xs)
    assert certificate['exact_slab_volume']=='1/5' and certificate['displayed_upper_bound']=='1/200'
    return baseline,files,summary,fixed


def record():
    baseline,files,summary,fixed = check()
    review = dict(date='2026-10-13', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='OpenAI quantitative Leibman route; actual original full/residue bad-pair character production and complete affine coefficient rows under one fixed finite list and uniform dyadic threshold; full rough comparison and final target remain open')
    manifest=dict(baseline)
    manifest.update(date='2026-10-13',files=files,hindman_module_count=summary['project_modules'],
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
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-13 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n'+Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    review.update(mathematical_review_file=PREFIX+'-mathematical-review.txt', mathematical_review_sha256=digest(PREFIX+'-mathematical-review.txt'))
    review.update(source_slab_certificate=PREFIX+'-slab-review.json',source_slab_certificate_sha256=digest(PREFIX+'-slab-review.json'),source_slab_script_sha256=digest('bracket-slab-volume-counterexample.py'))
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
