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

PREFIX = 'round-filtered-smooth-basis'
OLD = 'round-central-subspace-quotient'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeCentralSubspaceLogLattice.lean', 'Hindman168/NativeCentralSubspaceLogSpanning.lean', 'Hindman168/NativeCentralSubspaceExponentialHomeomorph.lean', 'Hindman168/NativeCentralSubspaceLatticeCoordinates.lean', 'Hindman168/NativeCentralSubspaceCoordinateRecovery.lean', 'Hindman168/NativeCentralSubspaceOrderedCoordinates.lean', 'Hindman168/NativeCentralSubspaceLatticeIndependent.lean', 'Hindman168/NativeCentralSubspaceOrderedProjection.lean', 'Hindman168/NativeCentralSubspacePairCoordinates.lean', 'Hindman168/NativeCentralSubspacePairSmoothInverse.lean', 'Hindman168/NativeCentralSubspaceOrderedSmoothExtension.lean', 'Hindman168/NativeCentralSubspaceFlagGeneratorLift.lean', 'Hindman168/ProjectionAppendLayerSpan.lean', 'Hindman168/NativeCentralSubspaceLatticeBasisSpan.lean', 'Hindman168/NativeLatticeFilteredSmoothBasisExist.lean', 'Hindman168/NativeLatticeFilteredSmoothBasisStep.lean', 'Hindman168/NativeLatticeFilteredSmoothBasis.lean', 'Hindman168/NativeLatticeFilteredDiffeomorph.lean', 'Hindman168/NativeLatticeFilteredSmoothRationalBasis.lean', 'Hindman168/NativeLatticeFilteredSmoothBasisCoordinates.lean', 'Hindman168/NativeLatticeFilteredLayerDimensions.lean']
COMPONENTS = ['Every actual original lattice-rational central subspace has a genuine logarithmic integer submodule, proved discrete and real spanning. Actual integer and same-column real bases, exact original Gamma coordinate integrality and actual original subgroup coordinate homeomorphism are constructed.', 'The chosen central-subspace coordinates have an actual original global smooth recovery function, actual ordered-product identity and independent columns. Ordered original exponential projection commutes with the actual central-subspace quotient.', 'For specified original Gamma lifts of an actual quotient coordinate family, the actual pair extension is bijective with exact original Gamma integer coordinates. If the quotient family has a smooth inverse, the exact appended original family has an actual global smooth inverse, independence and original rational logarithmic membership. The lifts remain specified inputs so their layer compatibility is retained.', 'When the actual central kernel subspace lies in every specified prior original layer, a single original Gamma lift of each quotient generator simultaneously preserves membership in all those actual layers. The actual deepest quotient layer is selected in a finite nonempty set; genuine relative lattice lifting there and actual layer antitonicity give every earlier equivalence.', 'An actual algebraic projection/append span theorem reconstructs the full original layer from actual quotient layer spanning, compatible original lifted columns, and an actual full kernel basis. No unconditional intersection-image lifting or arbitrary basis permutation is inferred.', 'Actual terminal central quotient dimension induction now constructs one full original ordered lattice vector family with a global smooth ordered-exponential inverse, exact original Gamma integer-coordinate correspondence, linear independence, and consecutive suffix spans for every natural original Lie lower-central layer. Original layer membership of the same columns has the same exact suffix thresholds, including terminal and zero-dimensional cases.', 'The exact family is upgraded to a fixed full original real basis and actual global Diffeomorph, with the same Gamma integer coordinates and all actual original lower-central suffix blocks. Its actual suffix starts are monotone and equal original layer codimensions, with zero and nilpotencyClass endpoint formulas.', 'For this exact filtered smooth original basis, an identical-column rational basis of the actual original logarithmic span is constructed. Rational/real coordinates commute and rational coordinates characterize the actual original logarithmic span. Actual original adjoint differential structure constants are rational in this same basis.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. A full original ordered lattice real basis with actual global smooth ordered-exponential inverse, exact original Gamma/integer-coordinate correspondence and consecutive suffix spans for every natural original lower-central Lie layer is now proved by compatible terminal central quotient dimension induction. The same fixed basis has an identical-column original rational logarithmic basis and rational actual bracket structure constants; its actual layer starts are monotone and equal actual codimensions. This basis is separately chosen from all retained earlier full smooth, split rational and central flag bases; literal equality is not asserted. Adaptation to an arbitrary supplied filtration is not claimed. Derive actual group-layer/prefix-zero coordinate criteria and the paper prescribed stretched filtration consequences as needed. Identify the paper filtration-adapted horizontal coefficient norm in this exact basis, construct its actual integral character grid and normalized lattice-period bounds, and establish any required uniform rational-height bounds. The retained horizontal grid uses the earlier separately chosen unadapted smooth basis and its full integer vector norm, so its conclusions cannot silently be transferred by basis-name substitution. The corrected equal-side quantitative Leibman actual character existence and uniform modular binomial coefficient bounds remain open. Retained real-box geometric/coefficient transfer, actual rational connected stretched filtration and native weighted Picard/BCH polynomiality/difference degree do not discharge that analytic input. No quantitative equidistribution is claimed by finite candidate-grid constructions. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish its density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['The new integer lattice is the literal original Exp membership set on the actual specified real subspace. Its addition and negation closure use actual original central Exp laws. Continuous injective original Exp into the specified original Gamma proves discreteness. Actual rational-subspace exponential spanning, pushed through the true subtype map, proves span_top. Only at this point are IsZLattice and integer/same-column real basis APIs used.', 'The actual subgroup coordinate homeomorphism uses original native Exp and Log restricted to the true subspace and true exponential subgroup. The original global smooth recovery uses original native Log and the actual finite real quotient retraction. The actual ordered product is identified with these same coordinates through original central Exp sum laws. No replacement abstract abelian group or alternative exponential is introduced.', 'The pair extension theorem accepts specified original Gamma lifts and their true quotient projections. Actual group_kernel_coordinates theorems provide original bijectivity and exact original lattice coordinates. The actual right inverse smoothness proof uses original quotient projection, original ordered Exp and actual kernel recovery. Appending the exact kernel basis through the actual coordinate split then preserves independence, bijectivity, integrality and smooth two-sided inverse. The output is the literal Fin.append family; no arbitrary permutation is used.', 'For each quotient vector, the finite set of actual containing layers through j contains zero because the original quotient zero layer is top. Its actual Finset.max member chooses the deepest layer. The proved actual kernel-contained lift theorem applies there because V is contained in every prior original layer. Original layer antitonicity proves all earlier forward memberships; actual quotient Lie-layer image equality proves the reverse membership direction. The same lift is used for every layer, not independently chosen layer witnesses.', 'The projection/append span theorem explicitly reconstructs every original layer element x: its quotient lies in the span of the compatible projected columns, hence has an actual representative a in the original selected-column span; x-a lies in the actual full kernel, itself spanned by the appended columns. Actual layer membership of all these columns proves the reverse inclusion. This is stronger evidence than merely matching dimensions or separate lattice image memberships.', 'The terminal step applies the actual simultaneous flag generator lifts to a quotient filtered smooth basis, and the exact appended smooth extension to those same lifts. For k<=j, actual original layer image equality, actual kernel span and actual lifted-column membership prove whole-original layer suffix spans. The appended kernel columns belong to every such layer, and quotient ordered starts remain literal original suffix starts. For k>j, actual next-layer bot and antitonicity make the original layer bot; actual full independence excludes zero columns and the full-size suffix is empty.', 'The induction is actual strong induction on finite real model dimension, universally quantified over models and original Lie groups. Nontriviality of the group implies model nontriviality through the actual native Exp Diffeomorph inverse. The proved last nonzero layer is central and Gamma-rational; its actual quotient dimension is strictly smaller. Actual quotient chart, T2, Lie group, simple connectedness, discrete Gamma image and cocompact image are constructed before invoking the induction hypothesis. Finite-dimensional subspace closedness is explicitly installed. The trivial group/zero-dimensional case is independently proved.', 'The fixed real basis is obtained from the exact full-dimensional independent family without reordering it. The actual Diffeomorph uses the actual global smooth inverse of that same family. Its separately chosen suffix starts are derived from the same basis specification. Actual restricted suffix span dimensions prove starts equal actual codimensions; an actual column at the later start and original layer antitonicity prove monotonicity, including empty/full cases.', 'The same-column rational basis uses the actual filtered smooth columns inside the actual original rational logarithmic span, actual real independence restricted to rational scalars, and the previously proved actual rational dimension equality. Coordinate compatibility reconstructs actual original vectors, yielding rational coordinate characterization. Actual original bracket-span closure then proves rational original adjoint differential coefficients in this exact basis.', 'The new filtered smooth basis is not claimed literally equal to any retained prior basis choice. Only the actual natural original lower-central flag is adapted here. Arbitrary prescribed filtrations, paper stretched filtration consequences, group-layer nonlinear coordinate prefix criteria, adapted horizontal norm/character bounds and quantitative analytic input still require their stated proofs. Complete StrongConjecture, independent replay, external review and public prize submission remain open. All prior registered proof source hashes and axiom sets must be retained unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual full original lower-central filtered smooth lattice basis via compatible terminal quotient induction; exact rational columns and original bracket constants; analytic existence and adapted horizontal norm open')
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
