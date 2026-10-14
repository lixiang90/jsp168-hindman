"""Audit actual original central factor descent, invariant factor probability and exact discrepancy transfer.

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

PREFIX = 'round-native-central-descent'
OLD = 'round-native-central-reconstruction'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/CentralFactorCosetMap.lean', 'Hindman168/CentralFactorCosetFibers.lean', 'Hindman168/CentralFactorObservableDescent.lean', 'Hindman168/NativeCentralFactorTopology.lean', 'Hindman168/NativeCentralZeroObservable.lean', 'Hindman168/NativeCentralZeroCompactFamilies.lean', 'Hindman168/NativeCentralFactorProbability.lean', 'Hindman168/NativeCentralZeroIntegral.lean', 'Hindman168/NativeCentralZeroDiscrepancy.lean']
COMPONENTS = ['ACTUAL ORIGINAL nonnormal G/Gamma maps to ORIGINAL (G/center G)/image(Gamma) under actual original quotient homomorphism. Actual representative formula, surjectivity, ORIGINAL G-action equivariance and true central-action invariance are proved. The map is ACTUALLY an OPEN QUOTIENT MAP, from composition of actual quotient maps; no original Gamma normality or substitute quotient group.', 'ACTUAL factor fibers are EXACTLY ORIGINAL central-action orbits for ANY original group/subgroup. Actual central quotient coset equality provides original gamma in Gamma; actual z=g^-1*h*gamma^-1 is genuinely CENTRAL and satisfies hGamma=z*gGamma by central commutation. Reverse fiber equality uses actual center quotient kernel and ORIGINAL action. No supplied orbit/fiber equivalence.', 'ACTUAL continuous ORIGINAL central-invariant observables genuinely descend through the actual open quotient map to ORIGINAL central factor. Actual fiber-orbit theorem supplies all FactorsThrough equations. True pullback identity, UNIQUE descent and inherited pointwise bound are proved. Explicit continuous factor map is passed to IsQuotientMap.lift; no assumed selector continuity.', 'ACTUAL original native central factor topology is compact and Hausdorff from genuine retained original image lattice discreteness/cocompactness and closed center. ORIGINAL specified compatible metric preserves actual OPEN quotient property. ACTUAL native factor fibers are EXACTLY ORIGINAL STANDARD CENTRAL TORUS action orbits, using actual original center torus representative surjectivity, for EVERY native step and original nonnormal lattice.', 'ACTUAL native ZERO vertical Fourier projection genuinely descends to a continuous observable on ORIGINAL center quotient with ORIGINAL image lattice for EVERY native step. Genuine actual zero-frequency central invariance supplies fiber constancy; actual original compatible-metric open quotient supplies continuity. True original pullback identity, uniqueness and UNIFORM NORM contraction are proved. No spatial Lipschitz regularity or lower-dimensional native inverse assumed.', 'ACTUAL descended zero-mode observables respect subtraction and give a norm-one Lipschitz map BETWEEN uniform-norm CONTINUOUS FUNCTION SPACES. Their image of ALL ORIGINAL unit Lipschitz observables is ACTUALLY COMPACT. This is not a spatial Lipschitz estimate on central factor points; original compatible metric distortion is not assumed bounded.', 'ACTUAL original central factor probability is CONSTRUCTED as EXACT pushforward of CONSTRUCTED original nonnormal quotient probability by ACTUAL factor map, with explicit ORIGINAL factor Borel sigma-algebra. Genuine probability, exact continuous-observable integral formula, exact zero-mode integral pullback and true ORIGINAL CENTER-QUOTIENT GROUP translation invariance are proved. Equality to separately constructed lower-dimensional native quotient Haar is NOT assumed or claimed.', 'ACTUAL product of ORIGINAL quotient probability and EXPLICIT Pi(circle Haar) admits integrable original central orbital evaluation by TRUE joint continuity/compactness. Genuine FUBINI and ACTUAL original central action integral invariance prove ZERO-MODE averaging preserves ORIGINAL Haar mean. Actual descended zero observable factor integral therefore equals ORIGINAL observable Haar mean. No disintegration, conditional fiber law or uniqueness of all homogeneous probabilities is assumed.', 'ACTUAL ORIGINAL zero-mode finite-sample Haar discrepancy EXACTLY equals ORIGINAL central-factor sample discrepancy, using SAME original sample set, ACTUAL factor images of SAME original samples, ACTUAL descended zero observable and ACTUAL factor pushforward probability. Genuine original bounded Fourier alternative is transferred to FACTOR discrepancy OR NONZERO-frequency ORIGINAL finite mean, preserving SAME fixed threshold, finite frequency list and natural l1 bound before all original samples/F. General nonabelian quantitative Leibman remains open.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. All prior actual scalar/standard torus inverses, native ABELIAN monomial/binomial/equal-cube/real-box obstructions, original filtered lattice/horizontal character/grid/operator budgets, original group bi-invariant Haar and original nonnormal normalized quotient probability remain retained. Actual original central torus action, probability invariance, compact orbital families, vertical Fourier projections and finite uniform vertical reconstruction/fixed finite bounded frequency detection remain proved. ACTUAL zero frequency now genuinely descends continuously and uniquely to ORIGINAL (G/center)/original image lattice. Actual original factor topology and metric open quotient, fiber-orbit equivalence, compact descended families, ACTUAL original factor pushforward invariant probability, exact mean preservation by genuine Fubini and genuine original factor/nonzero discrepancy alternative are NOW proved. Factor probability is ACTUAL pushforward, NOT yet identified with separately constructed lower-dimensional native canonical Haar. Next construct actual lower-dimensional NativeNilmanifoldData from retained original center quotient Lie/exp/log/rational/model dimension/image lattice data and compatible factor metric, prove genuine invariant probability compatibility (or supply an actual independently proved homogeneous probability uniqueness theorem), and establish true compact-family regularity approximation. Descended/projected families are uniform-norm compact, not asserted spatially unit Lipschitz. Then actual nonabelian finite-difference/product-group polynomial compatibility and quantitative Leibman induction, with fixed-data existence bounds and no unsupported power laws. Canonical-measure abelian root assembly, generic finite-index rough API, original bad-index residue/full Haar dichotomy to affine t*v+b and scales Z/t, actual finite obstruction density/descent, full rough-step, dimension/length/cofinal scales remain open. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence input remains unproved; do not confuse it with orbit quantitative Leibman. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment and HasAlignmentMonomialRecurrence remain unproved. Final original ordered positive rapidly separated monochromatic FS/FP extraction remains open. Retain actual unrestricted short-box O(eps) counterexample; corrected route has large-N threshold/coarse all-N bounds, so no unavoidable full-goal blocker. Author full builds/hash/source/standard-axiom audits are not independent kernel replay or external peer review. No public repository, PR or prize application created/submitted; do so at actual completion or genuine unavoidable obstruction with honest scope.'

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
        reference_scope='06_rough_progressions: ACTUAL original zero-mode central factor descent, invariant pushforward probability, genuine Fubini mean preservation and original factor/nonzero discrepancy alternative; canonical factor Haar compatibility/nonabelian quantitative Leibman/full prize theorem open')
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
