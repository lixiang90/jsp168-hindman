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

PREFIX = 'round-rough-native-piece-descent'
OLD = 'round-rough-labelled-native-tests'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/UniformFiniteExpectationCongruence.lean', 'Hindman168/RoughDependentRescaledSelection.lean', 'Hindman168/RoughNativeRescaledPieceSelection.lean', 'Hindman168/RoughBalancedRescaledGeometry.lean', 'Hindman168/RoughNativeDescentPolynomial.lean', 'Hindman168/RoughNativeModelDescentPolynomial.lean', 'Hindman168/RoughRescaledPieceGeometry.lean', 'Hindman168/RoughNativePieceDescent.lean', 'Hindman168/RoughFiniteLabelThinning.lean', 'Hindman168/RoughJointProgressionPolynomial.lean', 'Hindman168/RoughPieceDescentThresholds.lean', 'Hindman168/RoughNativeKernelLabelThinning.lean', 'Hindman168/RoughNativeModelPieceDescent.lean']
COMPONENTS = ['UniformFiniteExpectationCongruence proves actual finite uniform expectation congruence on the support, retaining the empty-support convention.', 'RoughDependentRescaledSelection constructs a genuinely label-dependent quotient-test discrepancy on an exact rescaled piece, preserving both positive-cardinality supports. It combines original error control with convex piece selection and actual expectation congruence.', 'RoughNativeRescaledPieceSelection supplies actual uniformly Lipschitz native quotient tests to that selection. Partition count and Lipschitz bound are fixed before all progression, coefficient, box, map and observable data; the discrepancy is not divided by the piece count.', 'RoughBalancedRescaledGeometry proves balanced-piece lower sides after residue division, comparable sides at scale Z/K and original sample position bounds.', 'RoughNativeDescentPolynomial combines actual subgroup native logarithm polynomial transfer, spatial affine substitution, strict finrank decrease and a degree bound depending only on original degree and nilpotence step.', 'RoughNativeModelDescentPolynomial derives the horizontal splitting degrees from actual coefficient models and original scalar polynomial degrees, rather than assuming the generated rational model degree independently.', 'RoughRescaledPieceGeometry bounds both actual signed transformed endpoints by (C+1)*Z/K, proves side lower bound c*Z/(4*N*K) and upper bound 4*C*Z/(N*K), and retains arbitrary original signed boxes.', 'RoughNativePieceDescent constructs in one theorem the actual smaller native quotient, its all-real joint logarithmic polynomial with original-step degree bound, comparable rescaled boxes, positive-cardinality supports and retained discrepancy. It uses the actual previous freezing and induced-test constructions.', 'RoughFiniteLabelThinning uses proved finite van der Waerden to make one finite label common along a long progression. Its smooth progression reparametrization preserves original roughness, the original dyadic interval and smoothness of the new positive difference.', 'RoughJointProgressionPolynomial preserves the actual all-real joint logarithmic polynomial and total-degree bound under affine progression reparametrization, leaving spatial parameters unchanged.', 'RoughPieceDescentThresholds derives one eventual threshold from actual power domination before every varying positive t<=2*S, simultaneously supplying all side and denominator bounds, Z/K>=1 and a fixed eta/2 discrepancy budget with freezing and approximation each eta/32.', 'RoughNativeKernelLabelThinning fixes the actual residue vector and native quotient index on a long progression, then constructs its single all-real reparametrized native logarithm polynomial with strict finrank decrease and degree bound depending only on the original step and degree. The input predicate remains explicit; actual full bad-family construction is not asserted.', 'RoughNativeModelPieceDescent specializes actual native piece descent to the generated rational coefficient models, deriving horizontal splitting and degree bounds from the original scalar polynomials. It retains the actual nonempty samples, smaller quotient, geometric bounds and discrepancy.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual single-index native discrepancy descent is now assembled, including model-derived degree bounds, all-real native logarithms, strict finrank decrease, exact nonempty rescaled samples, endpoint and side bounds, and a uniform fixed discrepancy budget from power domination. Finite label thinning and actual kernel joint polynomial reparametrization now make residue vectors and quotient indices common along long progressions; smoothness and roughness preservation are proved. Assemble all per-index witnesses into the full smaller-dimensional bad progression family, retaining a common group map and a genuine scale subsequence for each length. The full quantitative Leibman obstruction and uniform finite nonzero character list, corrected arbitrary-box comparison, stretched-filtration prerequisites, finite density extraction, complete dimension induction and uniform rough-step theorem remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['This batch also completes and registers six drafts found outside the last recorded manifest. Every new source receives a fresh focused Lean check; no prior scratch run is counted as recorded verification.', 'The actual new quotient is the original horizontal character kernel with its particular rational conjugate lattice intersection and original native metric. Distinct finite indices are not identified as the same quotient space.', 'Finite mixture selection retains a fixed discrepancy theta when the total actual weight error and twice the original approximation error fit below the original discrepancy. No division by N^dimension*K^dimension is introduced.', 'Both supports have positive cardinality, so the two actual selected uniform finite laws are probabilities. Original and rescaled test functions agree exactly on the respective supports.', 'Both transformed endpoints are bounded, not just integer samples. The c/(4*N) lower-side constant spends one factor two on balanced integer partition and one on residue-coordinate rounding.', 'The generated splitting degree bound is derived from actual rational coefficient models and the original joint scalar degree bound; the subgroup degree constant depends on the original nilpotence step only.', 'At all real joint parameters the transformed polynomial evaluates to the genuine native logarithm in the selected subgroup model. The actual original progression parameter remains polynomial after both spatial and progression substitutions.', 'The finite labels used to thin are the residue vector and quotient coset index, not all geometric interval labels. Varying boxes, frozen observables and tests remain permitted at each retained progression index.', 'The kernel-label theorem quantifies an explicit predicate of per-index selected witnesses. It proves common labels and actual joint polynomiality, but does not itself construct the entire bad progression family, quantify a common asymptotic subsequence or prove the missing Leibman theorem.', 'The uniform loss threshold precedes every varying positive t<=2*S and all endpoints, residues and tests. The fixed partition count, rational period and discrepancy constants cannot depend on the progression length.', 'Paper review covers pinned 06_rough_progressions lines 497-584: native quotient tests, two sampling weights, convex piece selection, fixed residue/coset thinning, exact x=u+Ky sampling and unchanged joint degree/scale growth. The preceding quantitative Leibman input is still unproved.', 'All retained proof sources and previous transitive axiom sets remain unchanged. Checks are author-side and do not constitute independent kernel replay or a complete proof of the prize target.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual native discrepancy descent, uniform geometric thresholds and fixed-label joint polynomial reparametrization')
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
