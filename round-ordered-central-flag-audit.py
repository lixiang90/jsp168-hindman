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

PREFIX = 'round-ordered-central-flag'
OLD = 'round-central-flag-basis'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/FiniteFlagOrder.lean', 'Hindman168/OrderedFlagBasis.lean', 'Hindman168/NativeCenterOrderedFlagBasis.lean', 'Hindman168/OrderedFlagDimensions.lean', 'Hindman168/NativeCenterOrderedFlagCoordinates.lean', 'Hindman168/KernelContainedLayerLatticeLift.lean', 'Hindman168/IntegerLayerLiftCounterexample.lean']
COMPONENTS = ['Finite decreasing flags can be ordered by actual membership depth. The actual sorting permutation makes every layer an upper set of finite indices, whose actual complement cardinality is a proved suffix start. Reindexing an actual simultaneously adapted basis preserves its layer spans and gives actual consecutive suffix blocks.', 'The genuine original central integer lattice has a chosen ordered basis with actual consecutive suffix blocks for every original lower-central layer index. Its same-column real basis has the same actual layer spans. Suffix starts are monotone and equal the actual central layer codimensions, including zero-dimensional and terminal cases.', 'For the exact chosen ordered central basis, original Gamma exponential membership is equivalent to integer real coordinates, and original Lie lower-central membership is equivalent to zero coordinates on the actual prefix preceding the corresponding suffix start.', 'For an actual group homomorphism whose kernel lies in the specified layer, the image of the original lattice/layer intersection equals the intersection of the two images, and actual relative original lattice-layer lifts are constructed. No kernel containment is assumed for arbitrary full-center layers.', 'A concrete integer plane module, a specified rational real line x=2y and first-coordinate projection provide a kernel-checked failure of unconditional relative lattice-layer lifting: 1 belongs to both separate images but not the intersection image. This audits a missing construction hypothesis; it is not a counterexample or unavoidable obstruction to the original nilpotent-group prize theorem.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact binomial obstruction existence and its modular coefficient bounds. The actual rational real basis adapted to the commutator layer and the conversion from identified Euclidean horizontal integer coordinates to the fixed functional norm budget are now proved. This split basis is not yet a lattice-coordinate Malcev basis adapted to the whole filtration; integrality of its complement coordinates is not asserted. Prove the actual equal-side quantitative Leibman input, including character existence and uniform coefficient bounds, and finish the required Malcev basis and filtration adaptation. Global ordered exponential coordinates of the correct dimension, with bijectivity and exact original Gamma/integer-coordinate correspondence, are now proved by actual center induction. The chosen original ordered vector family is now proved linearly independent and upgraded to an actual real basis and an identical-column rational basis of the original logarithmic span, with rational original bracket structure constants and actual unique integral functional evaluations. A strengthened original center induction now constructs a fixed original ordered lattice real basis with a genuine global smooth two-sided inverse and packages its ordered exponential map as an actual Diffeomorph. That same smooth basis has an identical-column rational basis of the original logarithmic span and rational original adjoint differential structure constants. Integer quotients of the genuine original central logarithmic lattice by each original lower-central-layer intersection are now proved free with actual integer complements. This provides the arithmetic splitting for central flag adaptation. One genuine original central integer lattice basis and its same-column real basis now simultaneously generate every original lower-central intersection for all natural layer indices. These adapted central coordinates have exact original Gamma/integer-coordinate correspondence, exact original group-layer/zero-coordinate correspondence and actual smooth two-sided central recovery. A separately chosen ordered genuine original central integer basis and its same-column real basis now have consecutive suffix blocks for every original lower-central layer. Their starts are monotone and equal the actual layer codimensions, with exact original Gamma integer coordinates and prefix-zero layer coordinates. Insertion of this ordered basis into the full original smooth ordered extension and full prescribed filtration adaptation remain unproved. Relative lattice-layer images and lifts are proved when the actual quotient kernel is contained in the layer; a concrete integer-plane rational-line example disproves unconditional lifting. The actual full-center lift condition is not discharged for arbitrary original lower-central layers. Use a compatible rational central ideal or prove the actual relative lattice-image condition before claiming full adaptation. This strengthened smooth basis is chosen separately from the earlier basis-only choice; their literal equality is not asserted. For the same smooth original lattice-coordinate basis, exact character linear evaluation, the two-way Gamma-integrality/integer-evaluation criterion, unique integer differential representation, finite rational bracket equations and a direct bounded-integer horizontal grid are now proved. Every character in this direct grid has a normalized rational direction with an explicitly positive original lattice period at most the fixed integer grid budget. The Euclidean size here is the full integer vector in that smooth basis; it is still not identified with the paper filtration-adapted horizontal coefficient norm. No analytic character existence or modular binomial coefficient bound is discharged. No quantitative equidistribution theorem is asserted by the finite grid construction. Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Membership depth is the cardinality of the actual finite set of layers containing a given vector. Antitonicity proves membership in layer j iff j is smaller than that depth, by explicit inclusions of Fin Iic/Iio sets. The actual Tuple.sort permutation orders this natural depth. No order is inferred from a merely arbitrary Fin reindexing.', 'Every sorted membership predicate is upper. Its actual false-index cardinality is proved a threshold: membership iff threshold is at most the index. The proof uses Iio/Iic cardinalities and works also for empty, full and zero-size flags. Reindexing the actual basis by the inverse sorting permutation retains every layer span and makes it a literal suffix span.', 'The native construction applies the finite ordering theorem to the actual chosen central integer basis and actual integer lower-central intersections through nilpotencyClass(G)+1. Natural indices are reduced by min(j,class); after the class actual layers are bottom by the original nilpotency theorem and antitonicity. The same ordered basis and chosen starts handle all natural indices.', 'The same-column real basis comes from the actual chosen ordered integer lattice basis. The proved actual central integer intersection real-span equality transfers its suffix span to the actual real layer. Real coordinate integrality reconstructs original lattice membership. Actual basis-support coordinates prove the prefix-zero criterion; no equality with earlier basis choices or retained full ordered-group basis is asserted.', 'The suffix dimension theorem restricts the original independent basis to the actual suffix subtype, proves its image equals the original suffix image, and applies the actual independent-span cardinality theorem. Fin interval cardinalities give n-t, including t>=n. Native starts are within dimension; the actual suffix span then proves start equals actual layer codimension. Native antitonicity and a basis column at the later start prove start monotonicity.', 'Kernel-contained relative lifting uses actual group-image representatives a in Gamma and b in the layer. Their equal projections put a*b^-1 in the actual kernel; containment proves a in the layer. This proves the actual intersection-image equality and extracts an original Gamma/layer lift. The kernel containment hypothesis is explicit and is not silently discharged for full-center quotients.', 'The reviewed counterexample is the literal integer pair module and literal real linear-map kernel x-2y. First projection sends an integer vector to 1 and sends the actual line vector (1,1/2) to 1. Any common original vector with first projection 1 would have integer coordinates a,b satisfying a=1 and a=2b, contradicted by integer arithmetic. All projections and image memberships are actual maps. This does not exhibit a failure of the original native lower-central theorem, nor rule out compatible smaller central ideals.', 'The original complete prize theorem, analytic quantitative Leibman existence/bounds, full lattice filtration adaptation, independent kernel replay, public repository, PR and award application remain unproved/unperformed. Prior registered proof sources and selected axiom sets are hash-retained unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions original ordered central suffix flag and dimensions; actual relative lifting conditions and counterexample audit; full filtration adaptation and quantitative existence open')
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
