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

PREFIX = 'round-rough-sampling-weights'
OLD = 'round-rough-induced-approximation'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughCoprimeResidueIntersection.lean', 'Hindman168/RoughNormalizedCountError.lean', 'Hindman168/RoughNormalizedPieceWeights.lean', 'Hindman168/RoughIntervalPieceComparison.lean', 'Hindman168/RoughProbabilityProductError.lean', 'Hindman168/RoughBoxPieceWeights.lean', 'Hindman168/RoughFiniteBoxWeightComparison.lean', 'Hindman168/RoughUniformFiberMixture.lean', 'Hindman168/RoughResiduePieceNonempty.lean', 'Hindman168/RoughUniformFiberSelection.lean']
COMPONENTS = ['RoughCoprimeResidueIntersection constructs an actual simultaneous integer residue from the proved modular inverse of t modulo K. When t and K are coprime, the exact original intersection of interval classes modulo t and K equals one class modulo tK. Its location-independent count differs from length/(tK) by at most one.', 'RoughNormalizedCountError proves positivity of the actual step-class denominator and a quantitative normalized residue error at most 4t/length when length is at least 2t. It retains the actual numerator and denominator counts and does not substitute the expected denominator into a ratio.', 'RoughNormalizedPieceWeights proves the general normalized partial-count bound and applies it to the actual step-t/K intersection in any integer subinterval of the original interval. Its weight differs from the geometric proportion sublength/(length*K) by at most 4t/length.', 'RoughIntervalPieceComparison compares actual original step-t and unrestricted integer weights of a subinterval with a prescribed K residue. Their absolute weight difference is at most 5t/length, uniformly in every signed endpoint and residue.', 'RoughProbabilityProductError proves an elementary telescoping bound for finite products of factors of absolute value at most one. The product difference is at most the sum of the individual absolute differences, without a factor exponential in the dimension.', 'RoughBoxPieceWeights proves the actual coordinate intersection cardinality product and rewrites the actual box count ratios as products of coordinate count ratios. It bounds the weight difference of one rectangular subbox and residue vector by the sum of 5t/side_length over the fixed coordinates.', 'RoughFiniteBoxWeightComparison sums the actual rectangular piece-weight differences. If original sides are at least cZ and 2t is at most cZ, the sum is at most card(pieces)*dimension*5t/(cZ). All endpoints, sample residues and piece choices remain arbitrary subject to the actual containment hypotheses.', 'RoughUniformFiberMixture proves the exact original uniform finite sampling law is a mixture of its actual label fibers, weighted by their actual cardinalities divided by the original cardinality. It proves weight sum one for a nonempty parent and exact expectation disintegration for signed tests, including empty fibers of zero weight.', 'RoughResiduePieceNonempty proves positivity of every actual interval and box intersection piece when each subbox side is at least 2tK, using the actual coprime intersection and count theorem. This supports conditioning on the later geometric pieces.', 'RoughUniformFiberSelection bounds actual uniform fiber test expectations from support-wise bounds, including empty fibers. It combines exact original expectation disintegration and reweighted convex selection to select a positive-cardinality original fiber retaining the prescribed discrepancy threshold. The discrepancy threshold is not divided by the number of pieces.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual coprime interval/box residue weights, quantitative O(t/Z) finite-piece weight comparison, positive piece sizes under explicit side thresholds, and exact original uniform finite fiber mixtures and convex selection are now proved. Construct the bounded rectangular subbox partition with the required upper and lower side bounds and prove its label fibers are exactly these box/residue pieces. Assemble the geometric label, actual weight comparison, freezing and uniform induced-test Lipschitz approximation into the original chosen-piece descent, with all error losses explicit; connect uniform rough-step asymptotics to the side thresholds and total weight error. Package the smaller rational character kernel as native nilmanifold data with the proved compatible source metric and strict dimension decrease. The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Section 06 splits both original sampling laws into subboxes and residue vectors. The new count and weight bounds use the actual original finite interval/box classes. Negative integer endpoints and arbitrary residues remain permitted. Coprimality is explicit and used to prove the intersection is a single class modulo tK.', 'The normalized denominator is the actual original step-t class cardinality. From count error <=1 and length/t>=2 it is at least half the expected count and is positive. The resulting 4t/length bound accounts for both numerator and denominator errors.', 'The unrestricted piece weight uses its actual original full integer interval/box cardinality. Its own numerator error is at most 1/length. Combining the two gives 5t/length. The common expected piece proportion is sublength/(length*K), not a replacement sampling law.', 'Actual coordinate product classes and their intersections are used. Each normalized factor is in [0,1] by actual finite set containment. Telescoping products therefore gives a sum of coordinate errors. Empty coordinate types yield singleton boxes and zero error, as required.', 'The finite-piece bound is valid even for overlapping listed subboxes; it is only a numerical bound on the listed weights. To identify them as a convex partition one must still construct a geometric label and prove its fibers equal those pieces. This obligation remains explicit.', 'The constant card(pieces)*dimension*5/c is fixed only if the number of pieces, dimension and c are fixed before varying samples and endpoints. No uniformity over unbounded numbers of pieces is claimed. The independent convex selection threshold does not divide discrepancy by card(pieces).', 'Exact uniform label-fiber disintegration is proved as an equality of actual finite masses, not just events or approximate averages. Empty fibers are zero-weight zero-mass components. Nonempty parent mass normalization follows from actual fiber weights; selected source fiber has positive cardinality.', 'The actual uniform-fiber selection theorem allows an empty comparison support algebraically, while the intended two-probability application requires a nonempty comparison parent. Nonempty residue pieces have a separate proved threshold of side >=2tK. Their geometric and asymptotic application remains to be assembled.', 'These supporting results do not establish the full geometric partition, descent assembly, smaller native-data packaging, uniform dimension induction or StrongConjecture. The old unproved inverse and recurrence existence inputs remain unchanged.', 'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual coprime residue sampling weights and exact original convex fiber disintegration')
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
