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

PREFIX = 'round-rough-native-filtered-polynomial'
OLD = 'round-rough-stretched-filtration-weighted-difference'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughNativeStretchedLattice.lean', 'Hindman168/RoughParametricWeightedDegree.lean', 'Hindman168/RoughParametricEvaluation.lean', 'Hindman168/RoughParametricWeightedPicard.lean', 'Hindman168/RoughParametricBilinearPerturbation.lean', 'Hindman168/RoughParametricAdPerturbation.lean', 'Hindman168/RoughParametricDefectPerturbation.lean', 'Hindman168/RoughParametricFieldPerturbation.lean', 'Hindman168/RoughParametricPicardPerturbation.lean', 'Hindman168/RoughNativeGroupDifferencePolynomial.lean', 'Hindman168/RoughFilteredPolynomialRestriction.lean', 'Hindman168/RoughNativePolynomialFiltered.lean', 'Hindman168/RoughVectorParameterSpecialization.lean', 'Hindman168/RoughNativeJointPolynomialFiltered.lean']
COMPONENTS = ['The actual stretched native Lie layers are rational relative to the original specified lattice log span. Their actual lattice-intersection quotients are compact and metrizable, and their actual quotient inclusions are closed embeddings with compact orbits, by exact original group/Lie equality.', 'The sufficient spatial weighted coefficient condition extends to actual finite parametric curves. It is stable under append, finite sum, endpoint, rational scale, time primitive and brackets. Actual Picard, defect and field operations preserve each base weighted offset.', 'Actual parametric evaluations satisfy exact singleton, append, finite sum, bracket, scale, endpoint and Bochner primitive laws. Primitive perturbations equal the actual difference of the two original primitives, using continuous polynomial integrability.', 'Finite constructive bilinear, iterated adjoint, defect and field perturbation polynomials evaluate exactly to the respective new-minus-old actual operations. Every perturbation remains at its supplied higher weighted offset while base operations stay at their base offset.', 'A finite constructive Picard perturbation has exact new-minus-old actual Picard evaluation and retains the higher weighted offset through every finite iteration. This uses the existing original native Picard product construction rather than an assumed formal BCH series.', 'The actual native group difference logarithm has a constructed vector polynomial representation at one higher weighted offset. Its baseline endpoint vanishes by original exponential inverse and global-logarithm identities, thereby rigorously removing all terms with no perturbation.', 'Iterated actual group differences have constructed logarithm polynomials with offset increased by the actual list length. Every bounded-degree original logarithm polynomial exponentiates to a polynomial map for the actual stretched group filtration, over real coordinates and over integer coordinates.', 'Actual additive homomorphism restriction preserves all iterated group differences and filtered polynomiality. Fixing the scalar parameter in an actual joint vector polynomial preserves its spatial degree and exact evaluation; joint integer affine sampling is filtered polynomial with fixed positive stretch max(1,q), including degree zero.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The geometric and algebraic corrected box consequence is now assembled for actual integer samples of half-open real boxes, including exact ceil endpoint representation, count and location budgets, actual equal-cube tiling and selection, fixed floor side, finite character index retention and native binomial-to-monomial transfer. The transfer remains conditional on exact equal-cube binomial character obstruction; it does not prove quantitative Leibman or construct a uniformly finite nonzero horizontal character list. Prove the equal-side quantitative Leibman input and its finite character construction. The actual stretched rational connected filtration and polynomiality of bounded-degree native logarithm polynomials are now proved, including actual lattice compact quotients, weighted native Picard perturbation, baseline BCH cancellation, iterated group differences and joint integer affine sampling with fixed positive stretch max(1,q). No bound on coefficients is imposed. An explicit degree bound uniform over all iterated difference lengths has not yet been extracted from this representation; actual filtered membership at every length is proved. The equal-side quantitative Leibman theorem, its adapted rational basis and uniformly finite nonzero character construction remain open analytic inputs. Connect the resulting finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Every group layer, logarithm, exponential, Lie bracket and lattice used is the original native object. The rational layer statement concerns the original rational log span, not an assumed additive Log Gamma lattice.', 'The termwise weighted condition is sufficient and can be stronger than coefficient membership after cancellation. Starting from an arbitrary degree-D list representation satisfies it, and all constructed perturbation lists retain it.', 'Bilinear perturbation uses B(dp,q1)+B(p0,dq), which evaluates to B(p1,q1)-B(p0,q0). Both original maps are preserved in the evaluated identity; higher weights are carried only by perturbation inputs.', 'Finite adjoint, defect powers and Picard perturbations are constructed recursively and their exact evaluation is proved at every spatial point and real time. No unproved BCH formula or cancellation axiom is introduced.', 'Time primitive preserves the higher spatial weight because it only rescales spatial vectors by rational inverse time degree. Its exact evaluated difference is proved using actual Bochner integral subtraction with continuous finite polynomial integrability.', 'The native group difference uses unchanged second input -A and actual first-input ordinary difference. The reference product exp(A)*exp(-A) equals one and its original global logarithm is zero. Cancellation is semantic through proved endpoint equality, not an unsupported syntactic list cancellation.', 'All k-fold actual left group differences are treated by induction on the actual list of shifts. The resulting logarithm representation has weighted offset k, which implies actual exponential membership in the kth group layer. Integer restriction is via an actual additive cast homomorphism.', 'The stretch is max(1,q) for joint degree q, fixed before every scalar parameter, origin and dilation. Parameter specialization and real affine substitution have exact actual evaluations and do not increase degree. No coefficient bound or positive dilation hypothesis is needed for polynomiality.', 'This closes the stretched-filtration polynomiality portion of the paper argument. It does not prove quantitative equal-side Leibman or construct its adapted Malcev basis and finite character bound. Uniform ordinary degree of all iterated representations has not been claimed.', 'Focused autoImplicit=false checks, full build, retained source hashes and selected standard-only axiom reports are author-side verification. All six pinned primary sections are compared; no complete StrongConjecture, independent replay or prize eligibility is claimed.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual rational stretched filtration and native weighted Picard/BCH group-difference polynomiality; equal-side quantitative Leibman remains open')
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
