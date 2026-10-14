"""Audit actual original relative/reduced filtered polynomial degree, projected Lie layers and genuine reduced layer topology.

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

PREFIX = 'round-native-relative-filtered-degree'
OLD = 'round-native-relative-polynomial'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeArbitraryLieFilteredPolynomial.lean', 'Hindman168/NativeBasepointPairDifferencePolynomial.lean', 'Hindman168/NativeBasepointReducedFilteredPolynomial.lean', 'Hindman168/NativeBasepointReducedLieWeights.lean', 'Hindman168/NativeBasepointRelativeFilteredPolynomial.lean', 'Hindman168/NativeBasepointRelativePolynomialWeights.lean', 'Hindman168/NativeConstantProductPerturbation.lean', 'Hindman168/NativeProductAdjointDifferential.lean', 'Hindman168/NativeProductPerturbationPolynomial.lean', 'Hindman168/NativeRelativeLieExponentialLayers.lean', 'Hindman168/NativeRelativeLieFiltration.lean', 'Hindman168/NativeRelativeLieLayerLogarithm.lean', 'Hindman168/NativeRelativeReducedLayerTopology.lean', 'Hindman168/NativeRelativeReducedLieFiltration.lean', 'Hindman168/RelativeLinearFiltration.lean', 'Hindman168/RoughVectorCoefficientEvaluationEquality.lean']
COMPONENTS = ['Exact native product adjoint differential is coordinatewise; actual smooth relative inclusion transports the native adjoint differential. Relative Lie layers consist of Fi-times-Fi pairs with difference in Fi+1 and satisfy the genuine bracket weight addition.', 'Actual parametric Picard product perturbations give exact logarithmic product differences. Arbitrary constant left/right corrections have weight ONE in the original positively stretched filtration; no coefficient size bound is assumed.', 'Actual normalized shifted first-minus-second logarithmic polynomial has weight ONE. Aggregated coefficient identities follow from all real evaluations and retain cancellations. Every actual ambient pair coefficient lies in the genuine relative layer at its monomial degree.', 'The CONSTRUCTED original relative native coefficient polynomial has genuine relative Lie weights. Actual antitone/bracket/Exp-layer proofs discharge every input of generic Picard group-difference transport. Both real and integer original normalized pair sequences are filtered for the SAME actual internal relative filtration.', 'The actual constructed reduced integer sequence equals the true terminal quotient projection of the original normalized relative pair. All iterated integer group differences of length at least s*d equal identity. The actual reduced filtration degree is at most s*d-1; this is not a decrease of the native nilpotency step bound s.', 'Exact logarithmic membership characterizes every original internal relative layer and every actual reduced group layer. Genuine projected relative Lie subspaces define the reduced Lie filtration, with actual bracket transport through the proved smooth terminal quotient projection and exact identity differential. The reduced Lie filtration vanishes from s*d onward.', 'Every ACTUAL reduced group layer is homeomorphic through original native Exp/Log to its actual finite-dimensional projected Lie subspace. Closedness, contractibility, connectedness and simple connectedness are proved for all actual reduced layers. Rationality against the actual image lattice remains OPEN.', 'The ACTUAL constructed reduced polynomial has weights in that same projected relative Lie filtration and genuine REAL filteredness. All aggregated monomial coefficients at degree at least s*d vanish. After removing zero vector terms its actual ordinary degree is at most s*d-1, with evaluations retained by the existing exact zero-trim identity.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Actual original normalized univariate relative polynomial weights, real/integer filteredness and genuine terminal quotient filtration-degree decrease are now PROVED for arbitrary starting values, representatives, integer shifts and UNBOUNDED coefficients. The actual reduced image Lie/group layers, exact logarithmic membership, brackets and closed/contractible/connected/simply-connected topology are now PROVED. SAME native nilpotency-step bound s is unchanged; the actual reduced filtration is NOT assumed to be another stretched lower-central series. Ordinary degree after removing zero terms is now at most s*d-1 with actual samples preserved. NEXT: rationality of every actual internal relative/reduced image layer against the SAME restricted/image lattice, recursive native rational-filtered induction, genuine ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction and pullback with finite-grid/operator/binomial bounds. Further original linear-step normalization P(n)*gamma^(-n) with true P(1)=a*gamma and ONE FIXED compact a remains to prove; representatives of P(1)^h alone do not bound P(1). The univariate degree-drop proof does not supply a multivariate inverse; justify corrected equal-side reduction or prove the multivariate branch. Fixed-data existence bounds only, no unsupported power laws or bounded original coefficients. Preserve corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample; this counterexample does not obstruct the corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports are preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute the authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.'

def declarations():
    return {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}


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
    review = dict(date='2026-10-12', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions and Green-Tao section 7: genuine relative weights/filteredness, actual reduced degree decrease and actual reduced layer topology; lattice rationality/recursive quantitative inverse/full prize theorem open')
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
    review.update(mathematical_review_file=PREFIX+'-mathematical-review.txt', mathematical_review_sha256=digest(PREFIX+'-mathematical-review.txt'))
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
