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

PREFIX = 'round-leibman-dense-directions'
OLD = 'round-leibman-short-lines'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/LeibmanPolynomialZeroCount.lean', 'Hindman168/LeibmanMonomialVectors.lean', 'Hindman168/LeibmanDenseMonomialSpan.lean', 'Hindman168/FiniteRationalCoordinateReconstruction.lean', 'Hindman168/IntegerCombinationModOneBound.lean', 'Hindman168/LeibmanDenseDirectionReconstruction.lean', 'Hindman168/ModOneNaturalMultiplier.lean', 'Hindman168/LeibmanSimultaneousDirectionReconstruction.lean', 'Hindman168/NativeFilteredHorizontalMultiplier.lean']
COMPONENTS = ['The genuine pinned Schwartz-Zippel theorem yields actual polynomial zero-filter cardinality times the coordinate-set cardinality <= actual total degree times the actual cube cardinality. A polynomial of degree <=d vanishing on an actual subset with d*|S|^n<|T|*|S| is the zero polynomial.', 'Actual monomial evaluation vectors and actual corresponding multivariate polynomials have exact coefficient recovery, evaluation dot products and total-degree bounds. A genuine nonzero linear functional on the finite vector space gives a nonzero actual monomial polynomial with evaluation equal to that functional on the actual monomial vector.', 'If actual sampled monomial vectors fail to span, a genuine nonzero annihilating functional and actual Schwartz-Zippel zero counting contradict the actual dense-set cardinality. Actual natural integer direction subsets of [0,L)^n therefore span the same original rational monomial vector space under d*L^n<|T|*L. The injective rational cast preserves the original cube subset and its exact cardinality.', 'Any actual finite rational spanning family reconstructs every actual coordinate vector with integer coefficients after one positive common integer multiplier. For a fixed actual finite candidate family, a single positive bound uniformly bounds this multiplier and every integer row natAbs sum for every actual spanning subset. The full finite powerset supplies the uniform bound before later coefficients or errors are supplied.', 'For actual dense integer direction subsets, the same bounded integer reconstruction identities hold over the real numbers. Actual modular small values of directional monomial sums imply bounded modular coefficients after the same positive bounded multiplier; the multiplier is chosen before arbitrary actual real coefficients and errors. Actual real density and direction-size inequalities imply the exact natural cardinality condition.', 'An actual positive product of finite positive bounded multipliers gives one common bounded multiplier. Its modular error estimate retains each individual error. Applied to any fixed finite family of monomial index sets, one positive bounded multiplier reconstructs every family member simultaneously and preserves each member error; no character switching between degrees is used.', 'For the same original filtered lattice basis, actual positive natural multiples preserve true nonzero Gamma-integral horizontal functionals. Their exact horizontal coefficient norm scales by that same natural number. Bounded multipliers therefore enter the actual original filtered integer character grid with the explicit enlarged norm budget.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The full original filtered smooth lattice basis and identical-column rational basis, original bracket constants, actual natural and prescribed stretched suffixes, actual linear Log layer criteria and actual horizontal head projection are retained. Complete original continuous-character classification, exact Gamma integer head image, actual coefficient norm/grid and bounded rational normalization/Gamma periods are proved. Full deeper nonlinear ordered-coordinate prefix criteria and arbitrary supplied filtration adaptation are not claimed. The actual corrected equal-cube short-line approximation and dense-origin step are retained. Actual dense direction monomial spanning, uniformly bounded integer coordinate reconstruction over a fixed finite direction cube, real/modular coefficient extraction, simultaneous bounded positive multipliers and actual original filtered character grid enlargement are now proved. These uniform bounds are fixed-data existence bounds; no power-law dependence in L or delta is asserted. The genuine one-parameter quantitative Leibman nonzero character existence and uniform modular binomial smoothness bounds remain open. The equal-cube correction still requires actual multivariate small-value inverse coefficient estimates and common-character/direction density extraction from the one-parameter outputs, plus their actual polynomial/difference/binomial compatibility and assembly. Candidate character grids and conditional coefficient reconstruction do not discharge character existence or these inverse estimates. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target.'

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
        application_review=COMPONENTS+['Actual Schwartz-Zippel applies to the true polynomial and finite coordinate set, not a heuristic dimension argument. Nonnegative-rational denominators are cleared only after actual coordinate-set positivity. The resulting natural inequality is valid even for zero variables. Actual dense-set inclusion in the true zero filter then forces the zero polynomial.', 'The monomial family is any actual finite subset of Fin n -> Nat with true total-degree bounds; no repeated formal monomial indices are allowed. Actual coefficient extraction proves the corresponding polynomial is nonzero for nonzero coefficients. The standard finite coordinate basis proves a nonzero functional has some nonzero coefficient. Actual vector reconstruction by standard coordinate singletons proves polynomial evaluation equals that same functional, without assuming sampled-vector independence.', 'Proper-span separation is the genuine existing Submodule.exists_le_ker_of_lt_top theorem. Its kernel contains the actual sampled-vector span, so the actual polynomial vanishes at the actual sampled points. Dense zero count yields the contradiction. The rational image of natural directions is injective; original subset membership and cardinality are transported before applying the generic field theorem.', 'Rational coordinate reconstruction uses genuine span membership for each standard coordinate vector and the retained finite rational denominator clearing theorem on the actual product of coordinate and sample indices. The actual cleared sum is the actual positive scalar times the original coordinate vector. The uniform theorem considers every actual spanning subset of the fixed original candidate family. It sums their chosen positive multipliers and all actual integer coefficient natAbs sums to get a bound valid before arbitrary future polynomial coefficients, errors or sampled subset are chosen.', 'Fixed-data finite-powerset bounds meet the OpenAI Section 06 statement, which fixes the nilmanifold, variable count and delta and asks for a uniform constant A independent of polynomial coefficients and N. No polynomial-in-delta or polynomial-in-L quantitative rate is claimed. Such stronger dependence would need a separate adjugate/height estimate. The present bound depends only on the fixed finite direction family and monomial data, not on later real coefficient values or errors.', 'Actual rational reconstruction identities are cast to real identities and finite sums are commuted to isolate each original coefficient. Modular integer-combination estimates use actual nearest integers and real absolute-value triangle inequalities, so no false real scalar linearity on the additive circle is assumed. The coefficient multiplier is chosen before arbitrary real coefficients and error eps; every original coefficient has the same multiplier.', 'The simultaneous theorem chooses one bounded multiplier per fixed family member, then their true positive product. Each factor divides the same product, and actual natural division gives the true remaining multiplier. The modular natural multiplier estimate preserves each member own error and a fixed common bound. This addresses the correction need for a single final character multiplier, without asserting that unrelated one-parameter characters can be combined.', 'Actual original horizontal functionals remain nonzero after positive natural scaling, still kill the actual commutator model, and still take integer values on original Gamma. The exact same-basis Euclidean head norm scales by the natural number; only after proving this equality and true functional preservation is actual filtered-grid membership concluded.', 'The primary corrected route is https://arxiv.org/pdf/1311.6170v3 Section 3, dense-direction Lemma 3.2 and its coefficient reconstruction. This round proves the required algebraic/directional pieces and uniform fixed-data bounds, not the one-parameter theorem, multivariate small-value inverse estimates, or complete corrected quantitative Leibman theorem. All original six pinned OpenAI sections and prior registered proof hashes/axiom sets remain unchanged.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions corrected equal-cube route: genuine dense monomial spanning, fixed-data uniform integer/modular reconstruction, one simultaneous positive multiplier and actual filtered character grid enlargement; analytic existence and small-value inverse inputs remain open')
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
