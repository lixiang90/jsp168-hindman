"""Audit ACTUAL general original basepoint native polynomial/weighted filtration/horizontal coefficients/sample/Haar normalization and compact double-translation finite-unit detection.

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

PREFIX = 'round-native-basepoint-normalization'
OLD = 'round-native-normalized-integer-pair'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughGroupBasepointNormalization.lean', 'Hindman168/RoughNativeProductWeighted.lean', 'Hindman168/RoughVectorMvConstant.lean', 'Hindman168/NativeBasepointPolynomial.lean', 'Hindman168/RoughNativeWeightedFilteredPolynomial.lean', 'Hindman168/NativeBasepointTrimmedPolynomial.lean', 'Hindman168/NativeBasepointCharacter.lean', 'Hindman168/NativeBasepointHorizontalPolynomial.lean', 'Hindman168/NativeBasepointObservable.lean', 'Hindman168/NativeBasepointPolynomialSamples.lean', 'Hindman168/NativeBasepointRelativeIntegerPair.lean', 'Hindman168/NativeBasepointTerminalPairSamples.lean', 'Hindman168/NativeBasepointReducedPairRegularity.lean', 'Hindman168/NativeBasepointTerminalPairDetection.lean']
COMPONENTS = ['ACTUAL original basepoint normalization r^-1*P(x)*P(0)^-1*r is constructed. Its original starting value is ONE. EVERY nonempty iterated original group difference is EXACT original difference conjugated by SAME r; any original normal filtration with initial zero layer TOP is genuinely preserved. Under actual original P(0)=r*gamma, SAME original possibly NONNORMAL lattice coset samples are retained after original left translation r.', 'ACTUAL original native logarithmic polynomial multiplication genuinely preserves SAME original termwise stretched-Lie filtration weights. This uses proved original weighted Picard construction, not a larger ordinary-degree filtration or an assumed polynomial-group closure input.', 'ACTUAL original constant vector polynomials have exact evaluation, ordinary degree ZERO, exact scalar projection and the genuine weight of their actual coefficient. Constants and original logarithmic coefficients may be UNBOUNDED.', 'ACTUAL general original MULTIVARIATE basepoint normalization has a genuine native logarithmic coefficient polynomial, built with actual original native product polynomials and actual original log representative/starting value. Its evaluation is EXACT original global logarithm of original normalized group sequence; its SAME original stretched-Lie weights at zero are proved from actual ordinary degree and proved weighted multiplication.', 'SAME original termwise stretched-Lie weights imply genuine original filtered polynomiality on real and integer inputs, even if ordinary degree exceeds original stretch. Genuine iterated native group-difference polynomial weights and original Exp/Log identities supply actual filteredness. Original stretch is NOT enlarged to the product ordinary-degree bound.', 'ACTUAL zero-trimmed original basepoint logarithmic polynomial has original evaluation, exact original normalized exponential sequence and starting LOG value ZERO. Its ordinary degree is genuinely bounded by s*d from actual original terminal Lie layer and original step bound, while SAME original filtration with stretch d remains genuinely preserved on real/integer multivariate inputs. No nilpotency-step/dimension decrease is claimed.', 'ANY ACTUAL original real linear horizontal character killing ORIGINAL commutator Lie layer changes under actual basepoint normalization by EXACT original starting constant only. Actual original global log additive character proves the pointwise assertion, not a torus-only or assumed compatibility interface.', 'COMPLETE actual original MULTIVARIATE horizontal scalar polynomial after normalization equals original scalar polynomial minus EXACT original starting constant polynomial. ALL coefficients are explicitly identified; EVERY NONCONSTANT original monomial coefficient is EXACTLY unchanged. Actual polynomial evaluation on all real points and genuine infinite-field polynomial extensionality prove the whole-polynomial identity.', 'ACTUAL original basepoint translated observable is continuous in SAME original specified metric; translation/input family is genuinely jointly continuous and compact on ANY fixed original compact representative set times original UNIT inputs, with original pointwise bound ONE. Original terminal Fourier projection COMMUTES with arbitrary original translation, and genuine ORIGINAL canonical Haar integral is unchanged. No spatial UNIT/Lipschitz property of translated observables is presumed.', 'ACTUAL general starting-value MULTIVARIATE normalization retains EXACT original integer orbit/coset samples, original continuous observable values and genuine original native canonical finite discrepancies. ONE FIXED compact original representative set covers ALL starting values before ALL original polynomials and coefficients, by genuine native compact coset representatives. Original starting log need not be zero.', 'ACTUAL general-starting-value UNIVARIATE normalized source has starting value ONE and genuine filteredness for SAME original stretch d. It supplies an ACTUAL original normalized shifted pair inside SAME original native relative-square GROUP, for ALL representatives/shifts/integer samples. No ordinary-degree-enlarged filtration or original starting-zero premise remains in this group-membership step. Native inclusion is EXACT actual pair.', 'ACTUAL original terminal Fourier sample identity is preserved under general original starting-value normalization. With true original basepoint and normalized linear-shift lattice factorizations, actual relative terminal pair using translated original observable equals EXACT original shifted/unshifted terminal Fourier derivative product; SAME original finite derivative mean is retained. Original ambient lattice normality is not assumed.', 'ACTUAL reduced specified-metric pair family with BOTH original compact basepoint and linear-shift translations is genuinely jointly continuous and uniformly COMPACT, for ONE FIXED pair of compact parameter sets and original UNIT inputs. Genuine compact-family approximation gives ONE FIXED finite spatial Lipschitz approximant family/shared positive bounds before all original inputs/translations/samples. No topology-to-spatial-Lipschitz inference or presumed translated spatial unit bound.', 'ONE FIXED original compact representative set, positive threshold and finite ACTUAL reduced specified-metric UNIT observable family detect ALL large ORIGINAL univariate terminal Fourier derivative means, before ALL original polynomials of degree at most d, arbitrary starting values, UNBOUNDED coefficients, integer shifts, original UNIT inputs and finite samples. True original basepoint/linear-shift representatives lie in SAME fixed compact set; SAME original relative group samples, genuine relative/reduced Haar zero mean, actual metric spatial approximation and normalization discharge all compatibility inputs. SAME original stretch d is retained. This is not a nonzero quantitative horizontal-character inverse or a full relative filtered-degree theorem.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic FS/FP is the prize target. All retained scalar/standard-torus/native abelian inverse, original group and nonnormal quotient Haar uniqueness, actual child zero-mode canonical Haar/metric finite-unit detection and horizontal character pullback, actual step-at-most-two ZERO-frequency inverse branch, original full-product/entire-diagonal factor, actual rational relative-square subgroup/native data and terminal-diagonal reduced native quotient/filtration remain proved. Original terminal torus/Fourier reconstruction/finite frequency selection permits ZERO and does not itself prove a horizontal inverse. Genuine original RELATIVE nonzero terminal pair mean ZERO uses actual first-coordinate terminal translations for filtration degree at least TWO, rather than substituted original/full-product Haar. Actual relative/reduced canonical integrals, terminal descent, target specified-metric compact families/spatial Lipschitz approximation/finite-unit detection are proved. NOW every starting-zero ORIGINAL ordinary UNIVARIATE logarithmic polynomial gives actual normalized shifted pair in SAME native relative GROUP, from proved ordinary-degree filteredness and genuine integer second-difference linearization, for ALL positive/zero/negative integer shifts and samples. Exact original translated first/unshifted second lattice cosets and finite terminal Fourier derivative averages are retained. ONE FIXED compact original representative set covers ALL original group elements and linear shifts. ONE FIXED finite ACTUAL reduced UNIT family/threshold detects ALL large original derivative averages before ALL starting-zero univariate original polynomials with UNBOUNDED coefficients, shifts, inputs and samples. NOW PROVED: genuine original general starting-value MULTIVARIATE normalization with actual compact representatives, native logarithmic coefficient polynomial, SAME original stretched Lie weights/real-integer filteredness, ordinary degree at most s*d with ORIGINAL stretch d unchanged, exact original native canonical discrepancy/sample/terminal Fourier identities and COMPLETE horizontal scalar polynomial compatibility with ALL nonconstant original monomial coefficients unchanged. Original starting-zero restriction is removed. BOTH actual basepoint/linear-shift compact parameters give genuine reduced specified-metric compact families, finite spatial Lipschitz approximation and ONE FIXED finite ACTUAL UNIT detection before ALL ORIGINAL ordinary-degree-bounded UNIVARIATE polynomials with arbitrary starting values and UNBOUNDED coefficients. STILL OPEN: full actual normalized RELATIVE filtered polynomial degree and relative logarithmic coefficient polynomial reconstruction; multivariate normalization or justified corrected equal-side reduction to the univariate case; recursive image-layer closedness/connectedness/rationality and appropriate native rational-filtered induction; NONZERO quantitative Leibman degree induction and genuine ORIGINAL nonzero finite-grid horizontal character reconstruction/operator/binomial coefficient bounds. Reduced filtration has real algebraic degree decrease, but SAME native step bound s is not a nilpotency-step/dimension decrease, and image filtration need not be stretched lower-central again. Never replace those actual proofs by assumed inverse or compatibility interfaces. Quantitative constants are fixed-data existence bounds only, with NO unsupported power laws or bounded original coefficients. Preserve corrected GT equal-side/erratum scope, actual large-N threshold, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample. That counterexample does not obstruct the corrected full goal. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence remains unproved, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final original positive ordered separated FS/FP extraction remain unproved. Author build/hash/source/standard-axiom audits are not independent kernel replay or external peer review. Full target remains unproved. No public repository, PR or prize submission yet; execute the authorized publication/application at actual completion or genuine unavoidable obstruction with honest scope. NEXT full normalized RELATIVE filtered polynomial/degree and actual relative logarithmic coefficient reconstruction, then recursive rational image-layer induction and genuine original nonzero horizontal character reconstruction. General original starting-value normalization is now proved, but does not itself prove the relative degree drop or inverse.'

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
        reference_scope='06_rough_progressions and Green-Tao section 7: ACTUAL general original basepoint polynomial/SAME weighted filtration/complete horizontal coefficients/original samples/canonical Haar/terminal Fourier normalization and compact double-translation finite-unit detection; full relative filtered polynomial degree/recursive quantitative inverse/full prize theorem open')
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
