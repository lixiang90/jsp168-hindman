"""Audit actual common-scale growth after retained tail factors.

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

PREFIX = 'round-retained-scale'
OLD = 'round-cube-intervals'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/AlignmentRetainedScaleBound.lean', 'Hindman168/AlignmentRetainedScaleGrowth.lean', 'Hindman168/AlignmentRawRetainedScale.lean']
COMPONENTS = ['A quantitative retained-scale inequality accounts simultaneously for the modulus, a fixed residue step and a variable retained tail product. Each is controlled by the actual pivot auxiliary scale, so microcell domination at exponent p+2 suffices to dominate the removed factor to power p after dividing the common cube scale by the retained step.', 'Actual master growth supplies one eventual threshold uniform over all sampled tails, all retained subsets and all choices of the removed tail factor. Binary dyadic lower endpoints and retained products are bounded through original cutoff geometry, without assuming independence or coprimality of the factors.', 'The uniform bound is packaged as actual PowerDominates for arbitrary admissible sample sequences and varying retained subsets/removed indices. Original global raw support discharges positivity and cutoff assumptions, yielding both the uniform raw-support estimate and the sequence-level growth statement.']
REMAINING = 'StrongConjecture and the original full finite monochromatic sums/products claim remain unproved. Finite-list native periodic interval inverse existence remains an explicit unproved hypothesis; its genuine existence proof and positive uniform correlation constants must be supplied. Conditional Prediction includes actual admissible parameters, positive finite scale-list closure, common native unit observables and complete fixed-ultrafilter calibration and count limits. Conditional Alignment includes the canonical finite-word schedule, actual execution, positive palette-scale budgets, common positive denominator and certified actual auxiliary visits. Integer realization now proves the actual master pair scale relation, exact natural numerator with its original rational value, canonical bounded full-modulus residues, all required divisibilities, uniform eventual fixed-integer divisibility, finite numerical slot bounds and the numerical own-target array-letter identity. The actual earlier-variable exposure fixes every residue and slot shift, full own-target numerators and array residues; exact affine tail dependence of each progression and the whole own-target progression sum is proved. Concrete integer-input polynomial array groups, their common nilpotence bound, input translations, pointwise lattice coset evaluation and exact affine model linear orbits are constructed. The genuine original native Lie polynomial-array coefficient algebra, bracket closure, high-degree cutoff and finite dimension are now proved; literal Lie evaluation homomorphisms and their lower-central compatibility are constructed. The same-step lower-central cutoff of the genuine array Lie algebra, injectivity of all integer evaluations and simultaneous coefficient recovery by one fixed finite integer evaluation set are now proved, including for the original native model. The actual binary product native Lie algebra, componentwise original exponential and global logarithm, and integration and inherited topology of every product Lie subalgebra are now proved. The complete native array coefficient algebra now embeds by one fixed finite family of integer inputs into the native Lie algebra of an actual finite original-group product. Its finite evaluation image integrates to a closed contractible simply connected subgroup, uniquely parameterized by coefficient exponentials. All-integer multiplication compatibility, the exact full exponential array subgroup, its group isomorphism and inherited-topology homeomorphism with the finite image, contractibility, simply connectedness, and discreteness of its pointwise Gamma-valued subgroup for discrete Gamma are now proved. Cocompactness of the exact all-integer pointwise lattice is now proved by actual lattice monomial spanning, rational-log intersection, positive-root character descent and continuous quotient transfer. The actual integrated subalgebra and full native array group now have constructed smooth manifold and Lie group structures on their inherited topologies, and all literal integer evaluations are smooth. The actual array group and exact lattice instantiate the existing NativeNilmanifoldData interface at the same original nilpotency step, with constructed compatible quotient metric. Integer input translations now preserve the actual graded coefficient Lie algebra, the full native exponential array group and its exact all-integer lattice; actual group and coset homeomorphisms and continuous coset evaluation with exact translation compatibility are proved. Array input translations are now proved smooth with smooth inverses in the existing original exponential charts. Original affine power-times-basepoint model arrays are proved to belong to the actual native array group; their exact evaluations, input translations and linear time orbit are proved both in the group and in its exact lattice coset space. Actual original and array discrete-lattice quotient manifolds are now constructed on the retained coset topologies; original quotient projections, all integer-input quotient evaluations and original quotient translations are smooth, with the latter having proved smooth inverses. The dependent product joint group, its exact product lattice, compact coset space, common nilpotency cutoff, original joint model orbit, component evaluations and input shifts are now constructed with exact formulas. The finite joint group now has its constructed finite-dimensional complete Lie model, global product exponential diffeomorphism and original smooth group operations, and instantiates NativeNilmanifoldData with the exact joint group, exact lattice and same common step. The original joint quotient is a smooth manifold with smooth component integer evaluations and smooth input-shift diffeomorphisms. Uniform quantitative smooth-observable bounds and model-reading calibration remain unproved. The finite short-bin pivot likelihood estimate and factor-three posterior domination relative to the original tail prior are now proved for the actual raw harmonic pivot law, with explicit full-cutoff containment, positive normalizer, unit residue and small-discretization hypotheses. The original dyadic-conditioned tail law is now proved equal to conditioning the original product law, and is dominated by 2^card(T) times product uniform. The actual short-bin posterior is now dominated by 3*2^card(T) times product uniform on prescribed dyadic residue bins, with explicit endpoint inequalities ensuring every pivot preimage lies in the cutoff. The original raw pivot probability of discarding short bins whose full preimages leave the buffered cutoff now has a uniform explicit bound and is proved to tend to zero for the actual master cutoffs and primorial roughness moduli. The proof covers any width bounded by the pivot gap, including modulus-aligned integer square-root widths, and any positive dyadic lower product. Actual product H-boundary probabilities now have a periodic cardinality estimate and exact original harmonic formula, without assuming coprimality of the tail product and H. Their averaged original joint probability tends to zero at actual master scales for margins bounded by a fixed multiple of K times the aligned integer square-root width, with K bounded by the auxiliary scale. The required square-root product-margin limit is proved from master growth. The literal numerical array arguments have a proved same-H-interval theorem under explicit whole-cell, slot and progression margins. The complete earlier-variable exposure disintegration, transfer through all prior good conditioning, connection of the now-proved negligible cutoff-clipped dyadic bins, transfer of the now-proved original-raw simultaneous array stability probability through the remaining exposure and good conditioning, and eventual satisfaction of the remaining scale inequalities are still to be connected. The exact real-floor microcell identification, all-power growth of both actual width and progression length, eventual width positivity, and uniform prescribed finite-slot bounds over every modulus-square-bounded residue family are now proved. Uniform polynomial bounds for the literal numerator and scaled array progression, their finite-table epsilon-width estimates, and deterministic whole-microcell interval stability with margin 3*aux*width are now proved. Exact pivot disintegration for original global raw event masses, the actual outside-law support geometry, simultaneous finite-target boundary probability decay, and probability-one-limit whole-microcell array stability under the original raw law are now proved. Exact finite exposure event disintegration, positive-event conditioning transfer and bad-fiber probability decay are now proved. A concrete short-exposure key records the original outside values, tail residues and binary dyadics, pivot residue and t_lo*R product bin, with proved coordinate and bin identities. Raw array stability transfers to the resulting conditioned exposure distribution in probability when the actual prior event has a fixed positive mass lower bound. The full short-exposure key now has an exact two-way window and numerical short-bin description on original raw support. Actual good exposure tail windows are nonempty and wholly inside the harmonic cutoff, their bad-key mass tends to zero even after prior conditioning with a fixed positive mass bound, and the original tail log/residue-conditioned law factors exactly into coordinate-conditioned raw laws. Exact full posterior factorization with the pivot short bin and typical original-raw posterior domination are now proved. Quantitative bounded-multiple cube comparisons and the required prior-event lower bounds remain to be assembled. The literal short-exposure fiber now has a uniform common numerical H-interval theorem for all earlier-cutoff-bounded realizations and fixed natural multiples C*R, under margin (C+3)*aux*R. Its exposure-wide good event has original raw probability tending to one. The actual full original-raw short-exposure posterior now has the proved 3*2^card(T) domination by the product-uniform dyadic residue law on an explicit good-key event of probability tending to one. Its full cutoff, bin-origin positivity, width and discretization conditions are derived from actual master parameters. Additional-prior-event posterior comparison and quantitative native-array observable bounds remain to be connected. The actual canonical residues and progressions now instantiate the exposure-wide interval theorem and give a frozen full interval/residue label on original raw support. The retained original piecewiseLinearNilsequence has the exact frozen observable/group/basepoint reading at the affine-plus-array exponent, including the original integer base quotient. The original numerical models now have exact continuous native-array and joint readings, with inherited uniform value and difference bounds and smoothness for smooth original observables. The original uniform value and Lipschitz bounds now yield compact families of intrinsic readings and one common subsequence with uniform convergence across all stored factors, all integer array inputs and all joint states. Uniform quantitative Lipschitz bounds on array readings, posterior comparison after additional prior conditioning and face-invariance remain unproved. HasAlignmentMonomialRecurrence remains an explicit unproved input. Its genuine nilpotent recurrence proof, the connection of the constructed joint model to all prescribed quantitative readings, microcell boundary and point-law estimates, and positive-probability Alignment bounds remain unproved. Final ordered positive rapidly separated monochromatic extraction is incomplete. No unavoidable blocker is established. A complete public proof repository, official contribution PR, independent review and prize application remain pending; no completed prize submission is claimed. The cube-coordinate change, exact canonical numerical exponent, degree-two rational exponent polynomial and exact nested step-class division are now proved. Common-scale box geometry, exposure-wide polynomial coefficient identification, joint BCH log-polynomiality, the uniform rough-step estimate and its probabilistic application remain to be connected. Actual cube base and increment upper bounds at the literal common scale t_lo*R/M are now proved, including strict sub-modulus rounding error and absorption into a fixed multiple. Full box side-length comparability, finite counting endpoint losses and normalized retained-step box geometry are still unproved. Exact integer affine sample sets with residue conditions, residue-aligned endpoint equality, side comparability from explicit original length bounds, retained-step interval normalization, and uniform actual endpoint displacement o(Z) are now proved. Concrete permitted cube box construction, its original side lower bounds, normalized average/counting error bounds and growth after retaining other factors still require assembly. The actual cube scale divided by d times any retained earlier-tail product now dominates every fixed power of the removed dyadic factor scale, uniformly over all original raw-supported samples, retained subsets and removed indices. Arbitrary varying admissible sequences satisfy the actual PowerDominates predicate. CRT selection of retained representatives, S/L growth, concrete box construction, average comparisons, joint log-polynomiality and rough-step application remain open.'

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
        application_review=COMPONENTS+['Reviewed denominator positivity and the two auxiliary factors lost to the modulus and retained product. The dyadic lower product is at least one; no unsupported cancellation of arbitrary factors is used.', 'Reviewed uniformity: thresholds depend on the fixed exponent, fixed residue modulus and error tolerance, before any sample, retained subset or removed index is chosen. Raw support supplies the actual original cutoffs and positivity.', 'Reviewed scope: the retained-subset theorem intentionally permits any subset of the tail, so in particular applies at every factor-removal stage. It assumes neither independence nor coprimality. Growth alone does not prove a rough-step comparison or determine the required retained residue representative.', 'All prior proof source hashes and transitive axiom sets are checked unchanged; no independent kernel replay or full-target proof is claimed.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='08_alignment: common-scale growth after retaining other tail factors')
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
