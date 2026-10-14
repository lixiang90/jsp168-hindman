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

PREFIX = 'round-central-flag-basis'
OLD = 'round-central-integer-splitting'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/IntegerComplementBasis.lean', 'Hindman168/IntegerFlagBasis.lean', 'Hindman168/IntegerSubspaceFlagBasis.lean', 'Hindman168/RationalSubspaceIntersectionSpan.lean', 'Hindman168/NativeCenterLayerRealSpan.lean', 'Hindman168/IntegerLatticeFlagBasis.lean', 'Hindman168/NativeCenterLayerFlagBasis.lean', 'Hindman168/IntegerLatticeChosenCoordinates.lean', 'Hindman168/NativeCenterLayerCoordinates.lean', 'Hindman168/BasisLayerCoordinates.lean', 'Hindman168/NativeCenterLayerMembership.lean', 'Hindman168/NativeCenterLayerSmoothRecovery.lean']
COMPONENTS = ['A basis formed from actual direct integer complements preserves every already adapted submodule below the first factor. Finite antitone flags of split submodules of finite free modules over a PID have one actual finite basis simultaneously generating every layer by its columns lying in that layer. Restricting an actual complement to the first layer supplies the recursive split, not independent unrelated complement choices.', 'Applied to the actual integer intersections of any finite integer module in a real vector space, primitive real-subspace quotients supply all actual splits. For a genuine full integer lattice and actual spanning intersections, one integer basis of exactly the real dimension and its same-column real basis simultaneously generate every specified layer.', 'Real extension of actual rational subspaces in a proved full rational form preserves intersections, by the existing compatible coordinate square and the proved finite rational coordinate intersection theorem. Actual original lattice-rational subspaces are closed under intersections. The genuine original center is lattice-rational, and its actual integer intersections with all original Lie lower-central layers real-span the corresponding central layers by actual positive-power denominator clearing.', 'One chosen genuine original central integer lattice basis and its identical-column real basis simultaneously generate all original lower-central intersections for every natural layer index. A finite flag through the actual group nilpotency class includes the terminal layer and supplies all later layers by antitonicity; zero class and zero-dimensional cases are included.', 'The same adapted central basis has exact original Gamma membership if and only if integer real coordinates, genuine global central exponential coordinates, integer lattice columns, original rational log-span columns, and an exact original ordered exponential product formula. Actual original group lower-central membership is equivalent to zero coordinates in every basis direction outside the layer, using the proved exact original group/Lie layer equality.', 'The adapted central exponential coordinate map into the original group is smooth. Its actual globally smooth coordinate recovery function uses the original global logarithm and the proved continuous linear center retraction. Two-sided recovery on all genuine original central elements is proved.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact binomial obstruction existence and its modular coefficient bounds. The actual rational real basis adapted to the commutator layer and the conversion from identified Euclidean horizontal integer coordinates to the fixed functional norm budget are now proved. This split basis is not yet a lattice-coordinate Malcev basis adapted to the whole filtration; integrality of its complement coordinates is not asserted. Prove the actual equal-side quantitative Leibman input, including character existence and uniform coefficient bounds, and finish the required Malcev basis and filtration adaptation. Global ordered exponential coordinates of the correct dimension, with bijectivity and exact original Gamma/integer-coordinate correspondence, are now proved by actual center induction. The chosen original ordered vector family is now proved linearly independent and upgraded to an actual real basis and an identical-column rational basis of the original logarithmic span, with rational original bracket structure constants and actual unique integral functional evaluations. A strengthened original center induction now constructs a fixed original ordered lattice real basis with a genuine global smooth two-sided inverse and packages its ordered exponential map as an actual Diffeomorph. That same smooth basis has an identical-column rational basis of the original logarithmic span and rational original adjoint differential structure constants. Integer quotients of the genuine original central logarithmic lattice by each original lower-central-layer intersection are now proved free with actual integer complements. This provides the arithmetic splitting for central flag adaptation. One genuine original central integer lattice basis and its same-column real basis now simultaneously generate every original lower-central intersection for all natural layer indices. These adapted central coordinates have exact original Gamma/integer-coordinate correspondence, exact original group-layer/zero-coordinate correspondence and actual smooth two-sided central recovery. Consecutive ordered index blocks for the flag, insertion of this basis into the full original smooth ordered extension, relative quotient lattice-layer lift compatibility and full prescribed filtration adaptation of the original ordered lattice basis remain unproved. This strengthened smooth basis is chosen separately from the earlier basis-only choice; their literal equality is not asserted. For the same smooth original lattice-coordinate basis, exact character linear evaluation, the two-way Gamma-integrality/integer-evaluation criterion, unique integer differential representation, finite rational bracket equations and a direct bounded-integer horizontal grid are now proved. Every character in this direct grid has a normalized rational direction with an explicitly positive original lattice period at most the fixed integer grid budget. The Euclidean size here is the full integer vector in that smooth basis; it is still not identified with the paper filtration-adapted horizontal coefficient norm. No analytic character existence or modular binomial coefficient bound is discharged. No quantitative equidistribution theorem is asserted by the finite grid construction. Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The finite-flag theorem is proved by induction on the number of layers. At each step the first original layer A and its actual complement Q form a product equivalence; the recursively adapted basis of A and the basis of Q are mapped through that equivalence. For every T below A, mapping the actual integer span in A proves that T is generated by the final basis vectors in T. The upper span inclusion follows from actual T membership. No compatibility is inferred merely from independent complements.', 'The recursive complements are the comaps of actual original complements to A. The modular-lattice IsCompl restriction lemma applies because antitonicity puts every later layer below A. Finite generation and freeness of submodules come from the finite free PID module. Reindexing the finite sum of basis indices proves the same layer spans. No total order on these finite indices, consecutive block property, adapted full-group basis, or paper horizontal norm identification is inferred.', 'Integer subspace flags are actual preimages under the original lattice inclusion, and the real-space torsion-free structure proves the original finite integer module free. The previous actual primitive-quotient/complement theorem discharges each split premise. For a full lattice, the proved integer rank equals the real dimension, so the final finite integer basis has exactly that dimension.', 'The rational intersection theorem transports actual real spans through an injective real coordinate equivalence and the existing identical-column rational basis. Actual injective map preservation of intersections and the proved rational-coordinate span intersection theorem discharge the equality. Ambient submodule intersections in span expressions are explicitly typed before coercion to sets.', 'Center lattice rationality follows from the actual original central Gamma intersection logarithms real-spanning the actual center and lying in the original rational log span. Rational intersection closure and actual positive-power clearing yield original exponential vectors spanning center intersect layer. The image under the actual center inclusion is proved exactly that set, and injectivity proves the actual central integer-layer span. No additive lattice of full nonabelian Log Gamma is assumed.', 'The all-natural-index central flag basis uses a finite flag of length nilpotencyClass(G)+1. At and after the actual nilpotency class the true Lie layers are bottom, by the registered original group nilpotency theorem and antitonicity. The subtype inclusion has zero kernel. Thus the same selected basis handles every later layer, including nilpotency class zero.', 'The real basis is made from that exact selected integer basis by ofZLatticeBasis. Chosen integer coordinates of actual lattice vectors equal their real coordinates, and the converse reconstructs the original vector by a finite integer sum. The central exponential homeomorphism is the true original one; original Gamma membership and ordered products are proved for this new basis, with no equality asserted to the earlier arbitrary center basis.', 'Layer membership uses the actual basis representation support theorem. Substituting the actual simultaneous layer-span identity gives zero coefficients outside the layer. The group result invokes the proved exact original algebraic group lower-central series equality, the actual logarithm membership theorem and the actual exponential/logarithm inverse.', 'The smooth recovery proof follows the prior retained arbitrary-center recovery argument with this new actual basis, and is checked anew. The continuous linear retraction is identity on the actual center; logarithm cancels the original exponential; the actual basis coordinate equivalence cancels synthesis. Smoothness uses the original smooth logarithm and actual continuous linear maps. The forward map is exactly the proved ordered exponential product in the new basis.', 'No StrongConjecture, quantitative analytic character existence, full Malcev flag ordering, relative layer lattice-image equality, unavoidable obstruction, independent kernel replay, external review, public repository, PR or prize submission is asserted. All prior registered proof sources and selected axiom sets are checked retained unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions original central lattice flag basis with exact layer membership and smooth central coordinates; full ordered filtration adaptation and quantitative existence remain open')
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
