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

PREFIX = 'round-rough-geometric-descent'
OLD = 'round-rough-sampling-weights'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughBalancedCuts.lean', 'Hindman168/RoughIntervalPartition.lean', 'Hindman168/RoughBoxPartition.lean', 'Hindman168/RoughBalancedBoxGeometry.lean', 'Hindman168/RoughPartitionWeightComparison.lean', 'Hindman168/RoughPartitionPieceSelection.lean', 'Hindman168/RoughPartitionScaleThresholds.lean', 'Hindman168/RoughFrozenPartitionSelection.lean', 'Hindman168/RoughNativeSubgroupNilmanifold.lean', 'Hindman168/RoughNativeKernelNilmanifold.lean']
COMPONENTS = ['RoughBalancedCuts constructs actual balanced integer cuts by distributing the quotient and remainder of each original side length. Every consecutive length is between floor(length/N) and floor(length/N)+1. The endpoints and monotonicity are proved. For length at least 2N each side lies between length/(2N) and 2length/N, including the final piece.', 'RoughIntervalPartition proves coverage and uniqueness for finite interval cuts, constructs an actual finite interval label, and proves its original step-class fibers equal the exact cut subintervals. The label is defined for every integer; fiber specifications are restricted to the original interval.', 'RoughBoxPartition constructs finite labels consisting of the interval index vector and the actual K-residue vector. For every signed endpoint and original residue, its original step-t sample fibers are exactly the subbox step-t/K intersections and its unrestricted fibers are exactly the subbox K classes.', 'RoughBalancedBoxGeometry proves containment, the paper-form subbox upper and lower side bounds, pointwise coordinate oscillation bounds inside each piece, and nonempty coprime residue intersections under the actual original side threshold 2NtK.', 'RoughPartitionWeightComparison applies the previously proved original count comparison to the actual geometric label fibers. There are exactly N^dimension*K^dimension labels. Total absolute weight difference is at most this fixed number times dimension times 5t/(cZ), uniformly in endpoints, original residues and piece choices.', 'RoughPartitionPieceSelection combines actual uniform fiber expectation disintegration with the geometric weight comparison. A positive-cardinality original subbox/residue intersection retains any discrepancy threshold below the original discrepancy minus M times the total weight bound. The discrepancy is not divided by the number of pieces.', 'RoughPartitionScaleThresholds derives one eventual threshold from PowerDominates before every varying natural t with t<=2S. It gives positive Z, original side size at least 2N, piece nonempty threshold 2NtK, original denominator threshold 2t, and any prescribed supremum-weight loss. N,K,dimension,c,M and error tolerance remain fixed before varying data.', 'RoughFrozenPartitionSelection assembles original two-probability freezing and approximation errors with geometric piece selection. The retained discrepancy exceeds theta provided theta plus the actual weight majorant plus 2*(freeze_error+approximation_error) is below the original discrepancy. Both original parent laws are proved nonempty; errors need only hold on the original box.', 'RoughNativeSubgroupNilmanifold packages the actual connected simply connected rational Lie subgroup and its actual conjugate lattice intersection as NativeNilmanifoldData at the original nilpotence step. It retains the original subgroup topology, proved compact quotient, discrete intersection, genuine subgroup Lie structure, and the original orbit-pullback metric with its proved open quotient map.', 'RoughNativeKernelNilmanifold specializes this construction to the actual rational horizontal character kernel for every integer coset index. The resulting group and lattice are proved to be the original kernel and conjugate intersection. A nonzero restricted character gives strict model finrank decrease relative to the original native nilmanifold.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The actual bounded geometric subbox/residue partition, uniform side thresholds, original finite-piece weight comparison, freezing/approximation loss assembly, and smaller native character-kernel nilmanifold packaging with strict dimension decrease are now proved. Apply native freezing and the uniform finite-residue induced-test approximants to the constructed piece labels; connect their maps and polynomial coordinates to the packaged kernel data. Prove the actual x=u+Ky conditional sampling transport and comparable transformed-box bounds, preserving uniform constants and logarithmic joint polynomiality in the new native model. The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The partition uses fixed N balanced cuts with no clipped final remainder. Exact original signed integer interval endpoints and actual label fibers are proved; a list of numerical piece weights is no longer treated as an assumed geometric partition.', 'The lower and upper side bounds have precisely the paper form with lambda=1/N. Coordinate diameter at most 2CZ/N suffices for the existing scalar-action freezing modulus after choosing N sufficiently large. Choosing N before varying endpoints is essential; the present geometry theorem does not itself select N from the native modulus.', 'The actual finite label set has N^d*K^d elements, including potential empty pieces outside the large-scale regime. Original uniform mixture and selection handle zero weights, and the separate 2NtK threshold ensures every intended coprime conditional piece is nonempty.', 'At the original growth threshold, original side cZ exceeds 2N, 2NtK and 2t uniformly for ALL t<=2S. The total supremum-weight error is below any fixed epsilon. This gives uniform endpoint and residue control, not merely convergence for one fixed box.', 'The selection wrapper requires the actual original discrepancy and bounded comparison test. The frozen wrapper additionally requires support-wise errors for actual frozen and approximate tests. It proves all losses, but does not silently supply native test maps as hypotheses already discharged.', 'The kernel data constructor proves every native nilmanifold structural field using the genuine subgroup chart, original conjugated lattice intersection, proved rational compactness and original orbit-pullback metric. No new lattice, normality assumption or smooth compatible metric is introduced.', 'Strict dimension decrease uses a character nonzero on the specified original Lie subalgebra, whose finrank is at most the original model finrank. The data constructor accepts an arbitrary rational original Lie subalgebra; the ambient top rationality and concrete quantitative-Leibman character choice must still be connected in the full application.', 'The source-model rational scalar action is constructed by restriction of the real scalar action. Native joint kernel logarithmic polynomiality was previously proved in original ambient coordinates; transfer to the newly packaged subgroup native logarithm remains an explicit obligation.', 'A decidable predicate mismatch between generic finite labels and concrete product/function labels was repaired using extensional equality of the actual finite filters. No heartbeat limit increase or logical axiom was used.', 'All retained proof sources and transitive axiom sets are checked against the previous checkpoint. Author-side checks are not independent kernel replay; unproved existence inputs and the final target remain unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual bounded geometric sampling partition and rational character-kernel dimension descent data')
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
