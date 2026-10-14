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

PREFIX = 'round-central-subspace-quotient'
OLD = 'round-ordered-central-flag'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeCentralSubspaceSubgroup.lean', 'Hindman168/NativeCentralSubspaceCosetRelation.lean', 'Hindman168/NativeCentralSubspaceQuotientHomeomorph.lean', 'Hindman168/NativeCentralSubspaceQuotientCharted.lean', 'Hindman168/NativeCentralSubspaceQuotientSmoothProjection.lean', 'Hindman168/NativeCentralSubspaceQuotientSmoothLift.lean', 'Hindman168/NativeCentralSubspaceQuotientLieGroup.lean', 'Hindman168/NativeCentralSubspaceQuotientDifferential.lean', 'Hindman168/NativeCentralSubspaceQuotientTangent.lean', 'Hindman168/NativeCentralSubspaceQuotientNativeExponential.lean', 'Hindman168/NativeCentralSubspaceQuotientNativeLogarithm.lean', 'Hindman168/NativeCentralSubspaceLieIdeal.lean', 'Hindman168/NativeCentralSubspaceQuotientLattice.lean', 'Hindman168/NativeCentralLayerKernel.lean', 'Hindman168/NativeCentralSubspaceLowerCentralImage.lean', 'Hindman168/NativeCentralSubspaceLayerLatticeLift.lean', 'Hindman168/FiniteRealQuotientDimension.lean', 'Hindman168/NativeTerminalCentralSubspace.lean', 'Hindman168/NativeTerminalCentralQuotient.lean']
COMPONENTS = ['Every specified original central real subspace has an actual exponential subgroup proved normal and closed. Actual exponential coset equivalence constructs a homeomorphism between the original vector-space quotient and the original group quotient with its retained quotient topology.', 'The actual central-subspace quotient has a constructed smooth chart, smooth projection and right lift, genuine smooth original quotient multiplication/inversion and Lie group structure. Its actual identity differential is the actual real quotient projection, with its actual specified kernel.', 'Actual original and actual quotient native exponentials and logarithms commute with the actual projections. The quotient coordinate exponential/logarithm are identified with the actual native maps; contractibility and simple connectedness are proved.', 'The specified central subspace is an actual native Lie ideal. When rational for the actual original lattice, its actual quotient lattice image is proved discrete; original lattice cocompactness gives quotient-image cocompactness.', 'Actual original group and Lie lower-central layers have exactly the actual quotient lower-central images. If the specified central subspace lies in a layer, the actual quotient kernel lies in that original group layer, giving exact relative original lattice-layer images and actual exponential lattice-layer lifts. Closedness is discharged from finite dimension in the Lie image/lift applications.', 'A nontrivial original model has a last nonzero actual lower-central layer. This layer is a rational central subspace contained in every earlier layer and has a strictly smaller actual quotient dimension.', 'For an actual original discrete cocompact lattice and nontrivial model, an actual terminal central quotient is constructed with discrete cocompact quotient lattice, strictly reduced dimension, and exact original lattice-layer images for every prior layer. This supplies compatible quotient inputs; full adapted ordered basis induction remains open.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact binomial obstruction existence and its modular coefficient bounds. The actual rational real basis adapted to the commutator layer and the conversion from identified Euclidean horizontal integer coordinates to the fixed functional norm budget are now proved. This split basis is not yet a lattice-coordinate Malcev basis adapted to the whole filtration; integrality of its complement coordinates is not asserted. Prove the actual equal-side quantitative Leibman input, including character existence and uniform coefficient bounds, and finish the required Malcev basis and filtration adaptation. Global ordered exponential coordinates of the correct dimension, with bijectivity and exact original Gamma/integer-coordinate correspondence, are now proved by actual center induction. The chosen original ordered vector family is now proved linearly independent and upgraded to an actual real basis and an identical-column rational basis of the original logarithmic span, with rational original bracket structure constants and actual unique integral functional evaluations. A strengthened original center induction now constructs a fixed original ordered lattice real basis with a genuine global smooth two-sided inverse and packages its ordered exponential map as an actual Diffeomorph. That same smooth basis has an identical-column rational basis of the original logarithmic span and rational original adjoint differential structure constants. Integer quotients of the genuine original central logarithmic lattice by each original lower-central-layer intersection are now proved free with actual integer complements. This provides the arithmetic splitting for central flag adaptation. One genuine original central integer lattice basis and its same-column real basis now simultaneously generate every original lower-central intersection for all natural layer indices. These adapted central coordinates have exact original Gamma/integer-coordinate correspondence, exact original group-layer/zero-coordinate correspondence and actual smooth two-sided central recovery. A separately chosen ordered genuine original central integer basis and its same-column real basis now have consecutive suffix blocks for every original lower-central layer. Their starts are monotone and equal the actual layer codimensions, with exact original Gamma integer coordinates and prefix-zero layer coordinates. Insertion of this ordered basis into the full original smooth ordered extension and full prescribed filtration adaptation remain unproved. Relative lattice-layer images and lifts are proved when the actual quotient kernel is contained in the layer; a concrete integer-plane rational-line example disproves unconditional lifting. The actual full-center lift condition is not discharged for arbitrary original lower-central layers. A new actual central-subspace quotient construction now proves the retained quotient topology, smooth Lie operations, native exponential/logarithm projection, rational quotient lattice discreteness/cocompactness and exact original lower-central images. Kernel containment is discharged whenever the specified central subspace lies in the layer. A last nonzero original lower-central layer is proved rational and central, contained in every earlier layer, and strictly reduces actual quotient dimension. An actual terminal central quotient therefore has exact prior relative lattice-layer images and a discrete cocompact quotient lattice. Complete the actual ordered lattice basis extension and full filtration-adapted smooth dimension induction using these compatible quotients; that induction is still unproved. This strengthened smooth basis is chosen separately from the earlier basis-only choice; their literal equality is not asserted. For the same smooth original lattice-coordinate basis, exact character linear evaluation, the two-way Gamma-integrality/integer-evaluation criterion, unique integer differential representation, finite rational bracket equations and a direct bounded-integer horizontal grid are now proved. Every character in this direct grid has a normalized rational direction with an explicitly positive original lattice period at most the fixed integer grid budget. The Euclidean size here is the full integer vector in that smooth basis; it is still not identified with the paper filtration-adapted horizontal coefficient norm. No analytic character existence or modular binomial coefficient bound is discharged. No quantitative equidistribution theorem is asserted by the finite grid construction. Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The subgroup is the actual image of the original native exponential restricted to the specified subspace. Original central exponential addition and negation prove subgroup closure. Membership is exactly original logarithm membership, proving actual closedness from finite-dimensional subspace closedness. Its actual inclusion in the original group center proves normality; no normal subgroup is supplied as a premise.', 'The coset relation is the actual quotient relation for this subgroup: v-w in V iff exp(v)^-1*exp(w) in N. The reverse direction uses the actual central logarithm of that product, original exponential multiplication and actual injectivity. Homeomorph.Quotient.congr uses the original exponential homeomorphism and the proved actual relation; original quotient topology is retained.', 'A single chart is induced by the actual quotient homeomorphism. Projection smoothness follows from original global logarithm and the actual continuous linear quotient projection. The right lift uses an actual finite real quotient linear section, actual original exponential, and actual quotient logarithmic coordinates. Genuine quotient multiplication and inversion are proved smooth through this lift and the original operations. Every local quotient T2/chart/Lie instance is applied to the specified V and hV explicitly.', 'The projection/lift right inverse proves differential surjectivity. The actual tangent calculation identifies the projection identity differential with the actual finite real quotient projection. The original smooth-homomorphism native exponential theorem then proves original/quotient exponential compatibility; actual quotient global inverse proves logarithm compatibility and coordinate/native map equality. Quotient nilpotency is inherited from the original group, and simple connectedness is established by actual contractibility, not an existence premise.', 'The actual central native Lie ideal has precisely V as its real model and precisely the actual exponential subgroup as its group. Rational compact representatives give g=x*gamma with x in the actual subgroup. Since g and x lie there, gamma lies there too; this explicitly establishes the Gamma-intersection representative required by the actual normal quotient discreteness theorem. Quotient cocompactness uses the actual surjective quotient map.', 'The group lower-central image equality follows from the actual surjective quotient homomorphism and the actual lower-central image theorem. The Lie-layer equality uses exact original and quotient group/Lie lower-central equality and actual exponential projection/injectivity in both directions. The Lie equality and lift theorem construct IsClosed(V) from finite dimension within their statements and proofs; no new closedness assumption remains in these applications.', 'Relative lattice-layer lifting explicitly rewrites the actual quotient homomorphism kernel to N and proves N lies in the actual original group layer by the exact original Lie/group layer equality. The previously reviewed kernel-contained intersection image theorem then applies. Actual original exponential representatives and actual quotient native exponential injectivity produce a vector in the original Lie layer whose exponential is in original Gamma and whose actual projection is the requested quotient vector.', 'Nat.find selects the first actual zero lower-central layer, which is positive because the zero-index layer is top and the original model is nontrivial. The preceding layer is therefore actually nonzero with zero next layer. Its native bracket is zero by next-layer membership and alternating symmetry, so it lies in the actual center. Original lattice rationality of actual lower-central layers and actual antitonicity establish rationality and containment in every prior layer. Actual quotient rank-nullity and positive subspace dimension prove strict dimension decrease.', 'The terminal quotient existence theorem packages the actual terminal layer, its proved central inclusion, actual discrete cocompact quotient lattice, strict model dimension decrease and exact original lattice-layer images for every prior layer. The model nontriviality is explicit; the zero-dimensional induction case is not claimed here. Full ordered basis construction, smooth ordered inverse, consecutive blocks in the whole group, and the paper horizontal coefficient norm still require actual induction and extension proofs.', 'This is author-side proof and hypothesis review. The complete original prize theorem, analytic quantitative Leibman existence/modular bounds, independent kernel replay, external review, public repository, PR and award application remain unproved/unperformed. All retained registered proof sources and selected axiom sets must remain unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual compatible rational terminal central quotient and relative lattice lifts; full adapted smooth ordered basis induction and quantitative existence open')
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
