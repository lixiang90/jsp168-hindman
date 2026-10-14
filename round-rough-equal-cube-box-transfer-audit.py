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

PREFIX = 'round-rough-equal-cube-box-transfer'
OLD = 'round-rough-cube-selection-start'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughEqualIntervalCoordinates.lean', 'Hindman168/RoughEqualCubeDefinitions.lean', 'Hindman168/RoughEqualCubeFibers.lean', 'Hindman168/RoughEqualTiledBoxGeometry.lean', 'Hindman168/RoughProductBoundaryFraction.lean', 'Hindman168/RoughEqualBoxBoundaryFraction.lean', 'Hindman168/RoughEqualBoxBoundaryScale.lean', 'Hindman168/RoughEqualCubeSampling.lean', 'Hindman168/RoughEqualCubeHaarSelection.lean', 'Hindman168/RoughEqualCubeSideFloor.lean', 'Hindman168/RoughEqualCubeOriginBounds.lean', 'Hindman168/RoughEqualCubeRatioChoice.lean', 'Hindman168/RoughCorrectedBoxCubeSelection.lean', 'Hindman168/RoughNativeBoxBinomialTransfer.lean', 'Hindman168/RoughFilteredPolynomialTranslation.lean']
COMPONENTS = ['RoughEqualIntervalCoordinates proves exact quotient labels for full integer interval tiles, the equivalence between a retained point with a specified quotient and membership in its actual tile, and local coordinates in range N for every tile point.', 'RoughEqualCubeDefinitions defines actual finite integer boxes by signed origin and natural widths, their retained equal-cube region, equal cube origins, actual cubes and finite dependent quotient labels. It proves the equal interval product representation and exact box and cube cardinalities.', 'RoughEqualCubeFibers proves that every actual retained point has its natural quotient label and that each label fiber equals the specified actual equal-side cube. Every full cube lies inside the original width box.', 'RoughEqualTiledBoxGeometry proves actual retained-region containment and nonemptiness when N > 0 and N fits every width, exact product cardinality of that region, and nonemptiness of all full cubes.', 'RoughProductBoundaryFraction proves the finite product deficit inequality for factors in [0,1], used to bound the total omitted fraction by the sum of individual coordinate deficits.', 'RoughEqualBoxBoundaryFraction proves the actual omitted integer-box cardinality divided by original cardinality is at most the sum of coordinate remainder ratios, and at most the sum of N divided by coordinate widths.', 'RoughEqualBoxBoundaryScale converts the actual boundary fraction to (number of variables)*lam/c when every integer width is at least c*Z and the cube side is at most lam*Z.', 'RoughEqualCubeSampling proves injection of local natural cube coordinates, equality of the actual cube to their translated image, and equality of its complex mean to the equal-side range-N sample mean.', 'RoughEqualCubeHaarSelection selects an actual cube with equal-side range-N sample discrepancy at least eta minus delta after trimming a boundary with error budget delta. Label fibers are actual cubes, not assumed components.', 'RoughEqualCubeSideFloor proves positivity and fixed-ratio lower and upper bounds for the actual natural floor cube side once lam*Z >= 2, and proves that this side fits every integer width when lam <= c.', 'RoughEqualCubeOriginBounds proves the actual cube origin belongs to its cube and derives its coordinate absolute bound C*Z from original box endpoint bounds, including negative origins.', 'RoughEqualCubeRatioChoice constructs one fixed positive ratio <= min(1,c) whose boundary contribution 2*B*(number of variables)*lam/c is at most eta/4. It handles B = 0 and a zero-dimensional spatial type using B+1 and dimension+1 in its denominator.', 'RoughCorrectedBoxCubeSelection assembles the actual integer equal-cube selection. It chooses lam and Z0 before all varying boxes, observables and means; outputs a positive side N between lam*Z/2 and lam*Z, a bounded signed origin, actual sampled-point containment and at least eta/2 Haar discrepancy.', 'RoughNativeBoxBinomialTransfer combines this actual cube selection with the proved integer binomial coefficient transfer into a uniform positive ordinary monomial obstruction budget on the actual multiplied native scalar projection. Character indices remain in the supplied finite set. Exact equal-cube binomial character obstruction is still an explicit premise.', 'RoughFilteredPolynomialTranslation defines actual left group differences and their iterates, proves they commute exactly with additive-domain translation, and proves preservation of prescribed subgroup-valued polynomiality under translation. It also proves that a zero step gives the identity group element.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual multivariate equal-cube geometry for integer width boxes, exact finite quotient-label fibers, sample-mean equality, boundary fraction, fixed small floor side, bounded signed origin and Haar discrepancy selection are proved. The conditional native box transfer now assembles this geometry and all coefficient conversions with character indices in a supplied finite set. The equal-cube binomial obstruction premise is not proved; it still contains the essential quantitative Leibman character existence input. Connect general real-box endpoints to the integer width representation with uniform count and location bounds where needed. Prove the equal-side quantitative Leibman theorem and construction of its uniformly finite nonzero horizontal character list. Group difference translation is proved, but the actual native logarithm polynomial still needs the stretched lower-central filtration, its rational connected subgroup properties and BCH coefficient/difference membership proof. Connect the resulting finite character selection to normalized descent and finish dimension induction using actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction from exceptional sets and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The definitions describe actual finite integer point sets. Quotient-label types are finite dependent functions with each coordinate in Fin(width/N). The default label outside the retained region is zero, whose admissibility is derived from N <= width and N > 0; all retained points use their true quotient.', 'The label fiber equality is proved from quotient-remainder arithmetic in each coordinate. No cube partition, local-coordinate bijection or convex mixture identity is an additional assumption of corrected cube selection.', 'All coordinates may have signed integer origins and unequal original widths. Only the selected full cube has equal side N in every coordinate. The proof does not invoke an unrestricted unequal-side quantitative equidistribution theorem.', 'The boundary fraction is the actual discarded cardinality divided by the positive original box cardinality. The proof casts the exact cardinal subtraction using actual containment, identifies the retained-to-original product ratio and applies the proved finite product deficit inequality.', 'The boundary bound first retains exact coordinate remainders and then bounds each remainder by N. Integer widths of at least c*Z and N <= lam*Z yield the uniform dimension*lam/c bound. No independence or probabilistic boundary approximation is assumed.', 'Complex boundary trimming controls normalization of the mean by 2*B times the discarded fraction. Nonempty retained cubes are proved before finite convex discrepancy selection. The selected discrepancy has no loss depending on the number of cubes.', 'Finite operations sometimes infer distinct decidability instances for the function type. They are transported by subsingleton equality of decision procedures; no new typeclass instance, unsafe code or computational proof oracle is introduced.', 'The actual cube side is the natural floor of lam*Z. Z0 >= max(1,2/lam) guarantees positive N and N >= lam*Z/2. Taking lam <= c makes N fit every coordinate width. lam and Z0 are selected before variable source data.', 'The fixed ratio is positive even when B = 0 or the spatial type is empty. B+1 and dimension+1 avoid zero denominators; min with one and c yields all required size bounds. Cube and sample identities also handle the empty spatial type.', 'The origin bound is derived by membership of the actual cube origin in the original box and its endpoint location bounds. It therefore supplies precisely the bounded integer translation required in the coefficient comparison.', 'The native transfer retains an explicit finite index set s: the analytic cube premise must return i in s, and the resulting ordinary monomial obstruction has i in the same s. The integer multiplier preserves actual projection identity and earlier lattice integrality results; no existence or bounded-height theorem for characters is inferred.', 'The final native transfer has a uniform positive output budget max(1,budget), chosen before all source boxes, vector logarithm polynomials, parameter values, observables and means. Positive spatial coefficients of every degree are covered by the preceding actual total-degree proof.', 'The analytic premise supplies both equality of the actual translated real binomial polynomial and coefficient modular estimates on the equal cube. Its existence is not asserted, and it has not been added as an axiom. Completion of this conditional transfer is not completion of quantitative Leibman or StrongConjecture.', 'Group differences use P(x+h)*P(x)^(-1), matching the pinned rough-progressions section. Iterated differences range over all finite step lists and retain their length. Translation preservation is proved for an arbitrary prescribed subgroup family; this alone does not prove that the family is the rational connected stretched lower-central filtration or that actual logarithm polynomials satisfy the membership predicate.', 'Paper comparison covers actual equal-side cube tiling, omitted strips, complex convex Haar selection, bounded cube location, uniform coefficient conversion and preservation of group polynomiality under integer translation. All six pinned primary sections are checked against fixed Git content.', 'All retained proof source hashes and transitive axiom sets are unchanged. Focused autoImplicit=false checks, full build, standard-only selected axiom reports and pinned primary source checks are author-side verification, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions actual multivariate equal-cube box consequence, conditional native coefficient transfer and group difference translation')
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
