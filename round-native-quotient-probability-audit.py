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

PREFIX = 'round-native-quotient-probability'
OLD = 'round-native-group-haar'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/CompactQuotientFinitePatches.lean', 'Hindman168/FinitePatchTransversal.lean', 'Hindman168/DiscreteCocompactFundamentalDomain.lean', 'Hindman168/NativeNilmanifoldFundamentalDomain.lean', 'Hindman168/FundamentalCosetProbability.lean', 'Hindman168/NativeNilmanifoldQuotientProbability.lean', 'Hindman168/NativeNilmanifoldProbabilityTesting.lean', 'Hindman168/NativeAbelianCanonicalProbability.lean', 'Hindman168/RoughNativeBadIndexHaarComparison.lean']
COMPONENTS = ['ACTUAL finite precompact injective patch cover is constructed from ORIGINAL locally injective open surjective quotient map, local compactness and compact quotient. No finite-cover or section existence is assumed at the native root.', 'ACTUAL finite patch strata U_i minus preimage of earlier image patches give a genuinely MEASURABLE relatively-compact transversal. True minimum finite-index construction proves each original coset has a representative; true stratum disjointness and local injectivity prove UNIQUE representative. No supplied selector/transversal property.', 'ACTUAL ORIGINAL discrete cocompact lattice Gamma.op right action has exactly ONE translate in the constructed measurable transversal. Genuine IsFundamentalDomain follows. ACTUAL original group Haar and original countable lattice prove fundamental domain mass POSITIVE, and its actual compact containment proves FINITE mass. Generic native root constructs and selects this actual domain for EVERY original step s, retaining measurability, fundamental property, positive finite mass and compact containment.', 'ACTUAL group Haar restricted to genuine fundamental domain is mapped by ORIGINAL coset map, then normalized by ACTUAL positive finite domain mass. Genuine probability normalization, original G-action invariance and choice-of-fundamental-domain independence are proved. NativeNilmanifoldData(s) root has no invariant-probability or fundamental-domain existence assumption; ORIGINAL nonnormal Gamma retained.', 'ACTUAL normalized invariant probability on ORIGINAL NONNORMAL G/Gamma is constructed for EVERY NativeNilmanifoldData(s). Actual canonical quotient Borel and original specified metric quotient Borel agreement, original metric compactness and true original group translate pushforward invariance are proved. Model/group Borel structures are explicit; no default volume is substituted.', 'Actual ORIGINAL compatible-metric continuous complex observables are genuinely integrable under constructed quotient probability. True bounded integral and original-group translated integral identities are proved. Actual finite pair discrepancy is split into one ORIGINAL sample Haar discrepancy without changing either original mean or observable.', 'ACTUAL general quotient probability has EXACT standard product-circle-Haar coordinates in the ABELIAN native case. TRUE original homeomorphism action equivariance and actual projection surjectivity prove torus coordinate measure is translation invariant; actual probability Haar uniqueness proves exact coordinate pushforward and ORIGINAL observable integral identity. No agreement between separately constructed measures is assumed, and no coordinate Lipschitz bound assumed.', 'ACTUAL ORIGINAL RoughNativeComplexBadIndex yields either original residue-box or original full-box discrepancy from the CONSTRUCTED native quotient Haar mean, retaining original observable, original Q/time, endpoints/residue, bounds and BOTH original positive sample cardinalities. True complexExpectation_uniformFinset equality connects original masses to exact finite means. General NONABELIAN orbit inverse/rough-step/full StrongConjecture remain open.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. All prior original filtered lattice, horizontal classification, exact coefficient norm/grid, rational normalization, short-line averaging, dense monomial spanning, fixed-data bounded integer reconstruction, simultaneous modular multiplier and conditional common-character/direction selection results remain retained. A genuine scalar affine linear torus inverse with a fixed delta-dependent bound is now proved. The COMPLETE one-variable scalar polynomial inverse for ALL bounded unit Lipschitz observables and the corrected large-box scalar small-value inverse INCLUDING the constant and eps=0 are now genuinely proved. Scalar monomial-to-binomial compatibility, actual rough singleton-basis expansion, and genuine one-based translation of ALL coefficients are now proved. COMPLETE genuine scalar TARGET-circle multiparameter polynomial phase/observable and large-box all-coefficient small-value inverses are now proved for every fixed input dimension and degree. COMPLETE genuine standard HIGHER-DIMENSIONAL TARGET TORUS monomial-coefficient observable inverse is now proved for every fixed target/input dimension and degree, on every positive original N, with an ACTUALLY produced bounded nonzero integer horizontal character and true continuous lattice-integral real character. General native/nonabelian one-parameter nilsequence inverse remains open. The unrestricted short-box O(eps) polynomial small-value auxiliary statement is disproved by an actual degree-two polynomial. Its use in the corrected equal-cube proof is under a large-N threshold; retain that restriction and handle small N separately by the original fixed A target. This is an avoidable auxiliary scope defect, not an established obstruction to the complete OpenAI route. Genuine affine scalar norm-bump Haar control, coarse inverse, actual modular interval-hit counting, strong linear recurrence and large-box O(eps) control of BOTH affine coefficients are now proved. Genuine positive-lag density on actual remaining intervals, true scalar difference degree/top-coefficient identities and the scalar Weyl TOP-coefficient inverse for EVERY fixed positive degree bound and ALL positive N are now proved. Genuine actual short progression localization, true rational top-phase control, top stripping, actual integer coefficient recovery and the COMPLETE scalar PHASE simultaneous monomial-coefficient inverse for EVERY fixed degree bound and ALL positive N are now proved. Genuine uniform Fourier reduction for ALL scalar observables and the actual large-box small-value inverse for EVERY scalar coefficient, including constant and zero tolerance, are now proved. Actual multivariable line coefficient degree/homogeneous identities, genuine scalar short-line candidate production and actual two-layer cube common-candidate density are now proved, as are actual fixed homogeneous coefficient correspondence and degree-zero bases. The lower-degree line-recovery IH is now GENUINELY discharged by the proved full natural-degree scalar small-value induction. The full scalar multiparameter phase and arbitrary-observable inverses now GENUINELY construct ALL original nonconstant coefficient estimates on EVERY positive N without any inverse existence hypothesis. Genuine multivariable O(eps) small-value refinement includes original constant and eps=0 on original sufficiently large cubes, and full natural degree induction is closed. Actual full multivariable monomial-to-binomial transformation, original rough-box basis expansion and genuine same-character scalar/standard-target-torus binomial inverses are now proved, including scalar constant/zero-tolerance small-value input. Next native/nonabelian orbit-equidistribution quantitative Leibman input; finish native general polynomial/difference compatibility and corrected equal-cube assembly. Uniform bounds are fixed-data existence bounds; no power-law dependence in delta/L is asserted. Connect actual finite obstruction existence/bounds to normalized rough-progression descent and finish density extraction, dimension induction, length restriction, cofinal scales, zero-dimensional base and full uniform rough-step comparison. Conditional face laws, face invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, quantitative smooth-observable bounds and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Final ordered positive rapidly separated monochromatic finite sums/products extraction remains open. Author verification only: no independent kernel replay, external peer review, public repository, PR or award application is claimed. The complete original prize theorem remains the goal and submission target. Distinguish the remaining nonabelian orbit-equidistribution/quantitative Leibman input from the separate HasNativePeriodicIntervalInverse finite-list interval Gowers-to-nilsequence correlation existence input; neither that Gowers inverse nor HasAlignmentMonomialRecurrence is discharged by the standard torus result. COMPLETE native ABELIAN original-metric multiparameter monomial inverse is now genuinely proved, with original quotient homeomorphism, explicit normalized translation-invariant Haar and compact-family Fourier transfer, and ACTUAL continuous-linear original lattice-integral horizontal character/operator budget. Next transfer native binomial coefficient form and actual finite native obstruction grid, then NONABELIAN orbit-equidistribution quantitative Leibman induction. General native/nonabelian inverse, SEPARATE interval Gowers correlation inverse and full StrongConjecture remain open. Native ABELIAN same-character BINOMIAL equal-cube inverse, common operator/coefficient bound, actual finite native grid, fixed B/L observable normalization, exact original vector spatial/affine projection and GENUINE original-real-box fixed finite obstruction existence are now proved for every fixed variable count n, with all cube hypotheses discharged. Next arbitrary finite-index transport if needed by rough-family API, and NONABELIAN normalized invariant quotient measure/central Fourier quantitative Leibman induction; no general nonabelian inverse or complete rough-step assembly is claimed. ACTUAL ORIGINAL nonabelian group bi-invariant sigma-finite Haar is now constructed for EVERY NativeNilmanifoldData(s), from original lattice basis additive Haar and original exponential. Original Ad/dexp/log-left Jacobian determinant-one facts are genuinely proved; no invariant group measure existence or unimodularity is assumed. Original group Polish/local compactness, original lattice countability and original coset covering in specified metric are genuinely proved. Next construct ACTUAL relatively-compact measurable fundamental domain and normalized invariant probability on ORIGINAL nonnormal cosets, then central-fiber Fourier quantitative Leibman induction. Group Haar is NOT quotient probability, and no nonabelian orbit inverse/full target completion is claimed. ACTUAL relatively-compact measurable positive finite fundamental domain for ORIGINAL countable discrete nonnormal Gamma is now constructed. ACTUAL normalized ORIGINAL nonnormal quotient invariant probability is now genuinely constructed for every native step, with actual metric Borel/compactness and translation/integral testing, domain independence and genuine abelian standard-Haar coordinate compatibility. Actual original complex bad index is genuinely reduced to either original residue/full-box Haar discrepancy. Next canonical-measure abelian analytic root assembly and residue affine/scales obstruction production, then actual NONABELIAN central-fiber Fourier quantitative Leibman induction. Generic quotient invariant probability uniqueness across arbitrary group Haar/central disintegration is not yet asserted; no general nonabelian orbit inverse or full StrongConjecture completion claimed.'

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
        application_review=COMPONENTS+['Construction review: actual local injective open patches shrink to compact K with original point in interior K. ACTUAL compact coset image cover has finite subcover, genuinely indexed by Fin m through actual Fintype equivalence. Strata remove preimages of all EARLIER image patches; a true minimum of nonempty finite set of patches yields coverage. True ordered-index comparison and original local injectivity yield global pi injectivity on F.', "Fundamental-domain review: ORIGINAL Gamma.op acts by RIGHT multiplication, even when Gamma nonnormal. Coset equivalence x^-1*y in Gamma constructs ACTUAL a in Gamma.op with a*x=y. Injectivity of pi on F and right-action cancellation prove UNIQUE a. Actual measurable F and this uniqueness satisfy existing IsFundamentalDomain.mk'. Actual compact containment K is retained in the NATIVE chosen-domain spec; positive finite mass is proved from real Haar compact finiteness/open positivity, actual countability and genuine translated-domain cover.", 'Probability review: ORIGINAL quotient measure is exact map pi of ORIGINAL group Haar restricted to actual F. Total mass equals ACTUAL nu(F), then inverse mass normalizes to one using genuine 0<nu(F)<infinity. Existing quotient fundamental-domain equality, true actual left/right Haar and actual countable original lattice prove native G-action invariance. Fundamental-domain independence is proved by TRUE unnormalized quotient measure equality and equality of total masses; no uniqueness of all homogeneous invariant probabilities assumed.', 'Measurability review: model/group Borel spaces explicit. ORIGINAL coset sigma-algebra is actual quotient of ORIGINAL group Borel sigma-algebra. Genuine original G Polish and original discrete-lattice closedness allow actual nonnormal CosetSpace.borelSpace. Proved original compatible metric topology equality transfers that Borel property and actual compactness. Integration uses ORIGINAL specified metric continuous observables and this actual Borel/probability measure.', 'Abelian compatibility review: general native quotient probability is pushed by ACTUAL original metric torus homeomorphism. Original projection is genuinely surjective. Every actual torus translation comes from ORIGINAL g-action; exact equivariance and true native translate invariance prove coordinate translation invariance. ACTUAL probability and compact group additive-Haar criteria plus Mathlib probability Haar uniqueness prove EXACT Pi(circle Haar), not merely equal total mass or assumed Haar agreement. True measurable embedding integral change of variables retains original observable.', 'Bad-index review: actual original bad-index functions are promoted to C(original metric quotient,complex) by ORIGINAL Lipschitz continuity. Exact ORIGINAL uniform finite-mass means equal actual finite set means. Actual strict pair discrepancy and true triangle inequality give eta/2 strict discrepancy on at least one ORIGINAL sample from SAME constructed quotient Haar integral, while retaining ALL original box/residue/bounds/positive-cardinality data. No residue cube/affine obstruction existence is yet claimed from this dichotomy.', 'Scope review: true original nonnormal quotient probability now exists for EVERY original step s, including nonabelian and dimension/class zero. Original abelian coordinate mean compatibility and general metric integration are proved. Canonical-measure abelian inverse root wrappers, arbitrary finite-index rough API transport, actual residue affine/scales obstruction production, general central Fourier quantitative Leibman, full rough-step/density/Alignment and original StrongConjecture remain unfinished. SEPARATE interval Gowers-to-nilsequence correlation inverse and alignment recurrence remain unproved. Author verification only; no independent kernel replay, peer review, public repo, PR or award application claimed.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: actual ORIGINAL nonnormal native quotient probability and fundamental domain, genuine abelian Haar compatibility and ORIGINAL bad-index Haar comparison; central Fourier/nonabelian quantitative Leibman/full prize target open')
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
