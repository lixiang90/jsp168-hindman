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

PREFIX = 'round-native-smooth-character-coordinates'
OLD = 'round-native-lattice-smooth-coordinates'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeOrderedCharacterEvaluation.lean', 'Hindman168/NativeSmoothBasisCharacterIntegrality.lean', 'Hindman168/NativeSmoothBasisIntegerCharacters.lean', 'Hindman168/NativeSmoothBasisIntegerCharacterGrid.lean', 'Hindman168/NativeSmoothIntegerCharacterNormalization.lean']
COMPONENTS = ['Every actual horizontal logarithmic character evaluates the original ordered exponential product as the exact linear sum of its actual basis evaluations. The character is smooth on the original group. The same evaluation law holds in the actual inverse coordinates of the fixed original lattice Diffeomorph.', 'For the same fixed smooth ordered lattice real basis, a functional killing the actual original commutator layer is integral on the entire original Gamma if and only if its actual evaluations on every fixed basis column are integers. The reverse direction uses actual original Gamma/integer ordered-coordinate membership and character additivity, not an additive Log Gamma lattice.', 'Integer coefficient vectors on the fixed smooth original lattice basis injectively parameterize real linear functionals. Their actual horizontality is equivalent to finitely many linear equations using the actual rational original bracket structure constants. Nonzero horizontal integer vectors are exactly nonzero Gamma-integral horizontal functionals; every such functional has a unique integer vector.', 'A finite horizontal character grid is constructed directly from bounded integer evaluations on that same smooth original lattice basis. Its membership is characterized exactly, its cardinality is at most (2*B+1)^dim(E), and every actual horizontal functional with bounded basis evaluations belongs. A bound on the full Euclidean integer vector places the character in the grid with ceiling budget fixed before source data.', 'For every character in that actual finite integer grid, a normalized rational direction and a positive original lattice period at most B are constructed explicitly from a nonzero integer coefficient. Direction and bounded period functions are chosen simultaneously over the entire fixed finite grid before varying source data.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. The corrected real-box geometric and coefficient transfer, actual rational connected stretched filtration, native weighted Picard/BCH group difference polynomiality and uniform ordinary difference degree are proved. Fixed finite nonzero horizontal character candidates, actual normalized rational directions and positive lattice periods are constructed from a fixed operator norm budget. The real-box transfer is still conditional on equal-cube exact binomial obstruction existence and its modular coefficient bounds. The actual rational real basis adapted to the commutator layer and the conversion from identified Euclidean horizontal integer coordinates to the fixed functional norm budget are now proved. This split basis is not yet a lattice-coordinate Malcev basis adapted to the whole filtration; integrality of its complement coordinates is not asserted. Prove the actual equal-side quantitative Leibman input, including character existence and uniform coefficient bounds, and finish the required Malcev basis and filtration adaptation. Global ordered exponential coordinates of the correct dimension, with bijectivity and exact original Gamma/integer-coordinate correspondence, are now proved by actual center induction. The chosen original ordered vector family is now proved linearly independent and upgraded to an actual real basis and an identical-column rational basis of the original logarithmic span, with rational original bracket structure constants and actual unique integral functional evaluations. A strengthened original center induction now constructs a fixed original ordered lattice real basis with a genuine global smooth two-sided inverse and packages its ordered exponential map as an actual Diffeomorph. That same smooth basis has an identical-column rational basis of the original logarithmic span and rational original adjoint differential structure constants. Full adaptation of the original ordered lattice basis to all specified filtration layers remains unproved. This strengthened smooth basis is chosen separately from the earlier basis-only choice; their literal equality is not asserted. For the same smooth original lattice-coordinate basis, exact character linear evaluation, the two-way Gamma-integrality/integer-evaluation criterion, unique integer differential representation, finite rational bracket equations and a direct bounded-integer horizontal grid are now proved. Every character in this direct grid has a normalized rational direction with an explicitly positive original lattice period at most the fixed integer grid budget. The Euclidean size here is the full integer vector in that smooth basis; it is still not identified with the paper filtration-adapted horizontal coefficient norm. No analytic character existence or modular binomial coefficient bound is discharged. No quantitative equidistribution theorem is asserted by the finite grid construction. Connect the actual finite candidate obstruction to normalized descent and finish dimension induction with actual length restriction, cofinal scales and the zero-dimensional base. Finite density extraction and the full uniform rough-step comparison remain open. Conditional face laws, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds, face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs; final ordered positive rapidly separated monochromatic extraction remains open. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['The original noncommutative ordered List product is retained. Additivity is proved from the actual original logarithmic product error lying in the commutator layer; only after applying that genuine character is the ordered product converted to a scalar sum. The zero identity uses the actual original global logarithm at one.', 'Smoothness is proved by composing the actual continuous linear functional with the genuine original smooth global logarithm. It requires no character nonzero or lattice assumption. All inverse-coordinate evaluations use the SAME strengthened smooth basis choice as the actual original Diffeomorph.', 'The reverse lattice-integrality implication takes a genuine original Gamma element, applies the actual original smooth inverse coordinates, uses the proved exact original lattice/integer-coordinate predicate, and constructs its integer character value as the finite integer dot product. The other direction tests actual original exponentials of the fixed basis columns.', 'The finite horizontality test uses real-basis extensionality in both slots of the actual continuous bilinear adjoint differential. Its reverse implication proves annihilation of ALL actual brackets before invoking the proved commutator span theorem. Its forward implication uses actual next-layer membership of adjoint generators. It does not replace full horizontality by unproved basis tests.', 'The integer functional uses actual real basis construction. Its injectivity uses evaluation on the full fixed spanning basis and injectivity of integer cast; zero, nonzero and unique-representation laws include the zero-dimensional case. Integrality of every admissible integer functional is discharged by the two-way original Gamma criterion.', 'The finite equations use real coordinates of the original adjoint differential in the same smooth real basis. Their rationality is already proved by the registered same-basis rational-coordinate theorem. These equations are not claims of an additive lattice of original group logarithms or arbitrary integer logarithm coordinates.', 'The fixed finite grid enumerates all integer vectors in the actual closed integer box, maps them to actual functionals, and filters to genuine nonzero Gamma-integral horizontal functionals. Its exact membership, cardinal bound and completeness under a supplied coefficient bound are separately proved. The full Euclidean vector bound is supplied; no bound from non-equidistribution is asserted.', 'Normalization selects a nonzero actual integer coefficient n, takes the rational direction n^-1 times its genuine original lattice basis column, and period natAbs(n). Its original exponential is the genuine column exponential or its inverse according to the sign of n. Hence the period is positive and at most the fixed integer box budget. This discharges original lattice membership directly without assuming an additive lattice of logarithms; simultaneous grid choices retain the uniform period bound and include empty-grid cases.', 'Full prescribed filtration adaptation, the paper horizontal coordinate norm conversion, quantitative Leibman existence and modular coefficient bounds, final StrongConjecture, unavoidable obstruction, independent replay and prize eligibility remain unclaimed.', 'All retained registered proof sources and axiom sets are checked unchanged. Focused autoImplicit=false compilation, full build, standard-only selected axiom reports, source scans and all six pinned primary sections are author-side verification, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions exact original horizontal integer coordinates in the same smooth ordered lattice basis; full filtration adaptation and quantitative existence remain open')
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
