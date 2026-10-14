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

PREFIX = 'round-filtered-horizontal'
OLD = 'round-filtered-smooth-basis'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeFilteredSmoothBasisCharacterIntegrality.lean', 'Hindman168/NativeFilteredSmoothBasisIntegerCharacters.lean', 'Hindman168/NativeFilteredSmoothBasisIntegerCharacterGrid.lean', 'Hindman168/NativeFilteredSmoothIntegerCharacterNormalization.lean', 'Hindman168/NativeFilteredHorizontalTail.lean', 'Hindman168/NativeFilteredHorizontalSize.lean', 'Hindman168/NativeFilteredHorizontalGrid.lean', 'Hindman168/RoughFilteredSmoothBasis.lean', 'Hindman168/NativeFilteredLogLayerCoordinates.lean', 'Hindman168/NativeFilteredHorizontalCoordinates.lean', 'Hindman168/NativeFilteredHorizontalLatticeImage.lean', 'Hindman168/NativeFilteredHorizontalCharacterCoordinates.lean', 'Hindman168/RoughFilteredRealBoxHorizontalTransfer.lean', 'Hindman168/NativeContinuousCharacterCommutator.lean', 'Hindman168/NativeContinuousCharacterLinearization.lean', 'Hindman168/NativeContinuousHorizontalCharacter.lean', 'Hindman168/NativeContinuousCharacterFilteredGrid.lean']
COMPONENTS = ['In the exact retained original full filtered smooth lattice basis, original logarithmic horizontal characters have actual ordered-coordinate evaluation and Gamma integrality iff integer basis coefficients. Their unique integer representations have zero tail at the actual commutator suffix start.', 'The actual horizontal head indices have cardinality equal to the actual commutator codimension. Their Euclidean coefficient norm equals the full integer coefficient norm because the true commutator tail vanishes. A fixed finite original integral character grid contains every bounded horizontal character and has the explicit ambient integer-box cardinality bound.', 'Every nonzero character in this actual grid has a rational original vector V with differential value one and an actual original Gamma exponential period K, positive and bounded by the coefficient ceiling. Fixed grid choices preserve these exact properties.', 'The same original full filtered smooth basis is adapted to the paper prescribed stretched lower-central filtration with the actual ceiling-division minus one index, including endpoints. Original Lie layer and original group layer membership are equivalent to prefix vanishing of the actual linear Log coordinates.', 'The original group horizontal projection is continuous and surjective, equals the head of the actual ordered smooth coordinates, is additive on original group multiplication, has kernel exactly the original group commutator layer, and maps original Gamma onto the full integer head lattice. Actual logarithmic character evaluation is its coefficient dot product.', 'Every actual continuous real-valued additive group homomorphism has a unique continuous real-linear original logarithmic representation. Actual nonzero Gamma-integral continuous characters correspond to genuine RoughNativeHorizontalFunctional inputs, so bounded actual continuous characters enter the same finite filtered grid and have bounded actual Gamma periods.', 'Actual real-box binomial coefficient transfer is proved for the same filtered horizontal coefficient norm and finite grid. The corrected equal-cube nonzero character existence and uniform modular binomial bounds remain explicit premises.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The full original filtered smooth lattice basis and its identical-column rational basis, actual bracket constants and all natural lower-central suffixes are retained. Its adaptation to the paper prescribed stretched filtration is now proved by the actual index ((i ceilingDiv D)-1). This does not assert adaptation to an arbitrary supplied filtration or literal equality with earlier separately chosen bases. Actual linear Log prefix criteria for every layer and actual ordered horizontal head coordinates are proved. Full nonlinear ordered-coordinate prefix criteria for every deeper group layer are not yet claimed. The paper horizontal torus is now realized by a continuous surjective original head projection with actual commutator kernel and exact Gamma integer lattice image. Every actual continuous Gamma-integral nonzero group character is uniquely an actual real-linear Log character. Its filtered horizontal Euclidean coefficient norm, actual integral grid and bounded rational normalization/actual Gamma exponential periods are proved; any additional uniform rational-height bounds remain to be derived as needed. The corrected equal-side quantitative Leibman actual character existence and uniform modular binomial coefficient bounds remain open. Finite character grids and conditional real-box coefficient transfer do not prove that analytic existence/bound input. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The four new same-basis character modules reprove the old generic character arguments using the actual retained filtered smooth basis specification. They do not assert equality of independent basis choices. All retained proof sources remain hash-identical.', 'Commutator suffix spanning gives exactly zero tail, in both directions. Integral character coefficients are uniquely recovered on the same actual basis. The Euclidean norm is on the actual horizontal head, not an arbitrary operator norm. Tail vanishing proves its equality with the full integer vector norm before any previous integer-grid size estimate is applied.', 'Original group layer criteria use the previously proved equality of actual original group lower-central layers and actual exponentiated Lie layers, then actual linear basis coordinates of original Log. They are not claimed to describe all nonlinear ordered coordinates. The stretched-filtration membership is the literal retained ceiling-division index, not a new filtration or an assumed adapted basis.', 'For each horizontal head index, its actual coordinate functional kills the actual commutator suffix. Actual original logarithmic character additivity proves projection additivity; actual ordered-product evaluation proves that its head equals the same Diffeomorph coordinates. Kernel equality follows from true group/Log layer criteria. Surjectivity and exact original Gamma image extend specified head coordinates by zero to full ordered coordinates, then use the exact retained original Diffeomorph and original Gamma integer criterion.', 'An arbitrary original real additive homomorphism is encoded as a MonoidHom to Multiplicative real numbers. Actual group commutator generators map to one. Equality of actual horizontal projections then implies equality of actual character values. This proves additivity of character composed with original Exp, without falsely assuming Exp is globally additive. Original Exp continuity and the real-linearization theorem produce the genuine unique continuous real-linear functional. True Exp/Log inverses prove the representation and uniqueness.', 'Actual equality between group commutator layers and exponentiated original Lie layers proves annihilation of the real commutator layer for this arbitrary-character linearization. Nonzero original character implies nonzero original functional through true representation. Original Gamma integrality is transported verbatim, yielding precisely the existing horizontal functional predicate, rather than a strengthened assumed character definition.', 'The continuous-character norm is literally the Euclidean vector of actual original character values at the retained horizontal basis exponentials. The exact Exp/Log inverse identifies it with the actual functional coefficient norm. Only after this equality are the finite grid and bounded-period conclusions transferred to every original continuous character. These are candidate-list and normalization conclusions, not quantitative equidistribution.', 'The real-box theorem still accepts actual equal-cube character existence and uniform modular binomial estimates as stated hypotheses. The new norm and actual grid conclude the desired fixed list but do not discharge those analytic hypotheses. The full original theorem, independent replay and external/public submission remain open.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual filtered horizontal torus, complete continuous-character representation, true coefficient norm, finite grid and bounded original lattice periods; prescribed stretched filtration; analytic input remains open')
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
