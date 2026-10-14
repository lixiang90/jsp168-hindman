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

PREFIX = 'round-rough-character-grid-uniform-degree'
OLD = 'round-rough-native-filtered-polynomial'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughNativeStretchedLieTerminal.lean', 'Hindman168/RoughVectorZeroTrim.lean', 'Hindman168/RoughNativeUniformDifferenceDegree.lean', 'Hindman168/RoughFiniteFunctionalGrid.lean', 'Hindman168/RoughNativeCharacterBasisMultipliers.lean', 'Hindman168/RoughNativeFiniteFunctionalGrid.lean', 'Hindman168/RoughNativeFunctionalGridBudget.lean', 'Hindman168/RoughNativeHorizontalCharacterGrid.lean', 'Hindman168/RoughNativeHorizontalGridNormalization.lean', 'Hindman168/RoughNativeRealBoxHorizontalTransfer.lean']
COMPONENTS = ['Actual stretched native Lie layers terminate at s*D+1 and thereafter for original group step at most s. Removing zero vector terms preserves exact evaluation and weighted membership and bounds remaining ordinary degree by s*D-k.', 'Every actual k-fold native group difference has an actual logarithm vector polynomial representation with degree at most s*D-k, uniformly over all shift lists and coefficients. For k>s*D the original group difference is exactly one.', 'A constructive finite grid of real linear functionals on a fixed finite basis is enumerated by bounded integer values on prescribed positive multiples of the basis vectors. Every integral bounded evaluation functional belongs to this grid, with a cardinality bound by the actual finite integer box.', 'Actual original lattice rational basis vectors have fixed positive integer multiples whose original exponentials lie in Gamma. These actual lattice sampling vectors are selected from proved positive powers in the original rational log span, not from an assumed additive Log Gamma lattice.', 'A fixed positive norm budget for the actual lattice sampling vectors turns a fixed operator norm bound on a Gamma-integral functional into membership in a fixed finite grid. The grid and ceiling budget are selected before every varying functional or polynomial.', 'The finite grid is filtered to actual nonzero horizontal Gamma-integral functionals. Every remaining entry defines an actual continuous additive and surjective real character on the original group. Original native bracket annihilation and integrality suffice for norm-bounded input membership.', 'Every candidate in the fixed finite horizontal grid has a rational normalized direction with character value one and a positive original lattice period. Direction and period functions for the entire finite subtype are chosen before varying source data.', 'The actual corrected half-open real-box coefficient transfer now constructs its own fixed finite horizontal candidate grid from a norm budget and an existential equal-cube obstruction premise. It retains actual character membership and all positive original multiplied scalar coefficient bounds, with uniform constants before source variables.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact binomial obstruction existence and its modular coefficient bounds. Prove the actual equal-side quantitative Leibman input and adapted rational basis; in particular prove character existence and the uniform size bound and connect the paper Malcev-coordinate size to the fixed functional norm budget. No quantitative equidistribution theorem is asserted by the finite grid construction. Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The vector trim deletes exactly zero vector coefficients, rather than zero scalar polynomials. Exact evaluation and weighted membership are preserved. Beyond-terminal weighted membership forces a nonzero vector term to have totalDegree+k <= s*D, even for k greater than s*D.', 'The uniform degree is s*D-k with natural subtraction. For k>s*D all actual group differences are one; no assertion that natural degree of a zero polynomial is negative is made.', 'The finite functional grid enumerates integer evaluations divided by fixed positive basis multipliers. Basis extensionality proves full functional equality, not merely agreement on the finitely many tested points.', 'Original lattice basis vectors lie in the actual rational log span. The original positive-power theorem and genuine exponential natural-scaling law supply lattice points. Log Gamma is never assumed to be an additive lattice.', 'The norm budget is one plus the finite sum of actual sampling-vector norms and is positive even when the model is zero-dimensional. Ceiling conversion is valid for every nonnegative operator norm budget. Empty candidate grids do not imply existence of a nonzero character.', 'The horizontal filter requires nonzero differential, annihilation of the original actual commutator layer and Gamma-integral original logarithm values. Actual character continuity, additivity, surjectivity and lattice integrality are proved for every selected entry.', 'Normalization uses a rational basis value where the nonzero functional does not vanish, scales in the original rational log span and uses the original positive-power criterion. All finite-subtype direction and period choices are independent of varying source variables.', 'The real-box theorem keeps the equal-cube existence premise explicit, including exact translated binomial polynomial equality and modular coefficients. It replaces a supplied finite index list by a proved candidate grid; it does not discharge quantitative Leibman.', 'Operator norm bounds are not silently identified with the paper integer coefficient-vector size in an adapted Malcev basis. That basis construction, size conversion and the actual quantitative existence theorem remain open.', 'Focused autoImplicit=false checks, full build, retained proof hashes and standard-only selected axiom reports are author-side verification. All six pinned primary sections are compared; no independent replay, full target or prize eligibility is claimed.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions uniform group-difference degree and actual finite horizontal character grids, directions and lattice periods; quantitative existence remains open')
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
