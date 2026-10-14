"""Audit actual dense useful Fourier derivative shifts, common relative character selection, BOTH original-scale coefficient bounds, complete degree-two dense extraction and raw pure-diagonal monomial reconstruction.

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

PREFIX = 'round-native-rational-dense-relative-character'
OLD = 'round-native-rational-nonzero-relative-character'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/FiniteCoefficientScaleTransfer.lean', 'Hindman168/FiniteComplexMeanEnergy.lean', 'Hindman168/FiniteDenseDerivativeMeans.lean', 'Hindman168/FiniteDenseWitnessSelection.lean', 'Hindman168/NativeRationalDegreeTwoDenseRelativeCharacter.lean', 'Hindman168/NativeRationalDenseFourierDerivatives.lean', 'Hindman168/NativeRationalDenseRelativeCharacter.lean', 'Hindman168/NativeRationalPureDiagonalReconstruction.lean', 'Hindman168/NativeRationalRelativeCoefficientScale.lean']
COMPONENTS = ['ACTUAL arbitrary bounded complex sequences have a positive-density set of genuine positive derivative shifts. Each derivative mean uses its TRUE remaining interval N-h, with 0<h<N and N-h >= (delta^2/8)*N. Exact natural-range/integer-Ico mean transport is proved. No truncated or zero-extended sample is identified with a full original sample.', 'Actual native rational-terminal Fourier projection is globally bounded by ONE on original unit observations. Its genuine large original univariate orbit mean produces a positive-density set of actual original Fourier derivative means on SAME actual remaining intervals, with no unit-Lipschitz assumption on the projected observable.', 'A general finite witness-selection theorem proves ONE ACTUAL common witness on a nonempty subset, preserving an explicit cardinality bound involving the FIXED witness-list cardinality. Source-dependent witness choices do not redefine the finite list.', 'TRUE retained sample lengths transfer monomial and paper-binomial coefficient bounds to the ORIGINAL N scale. The proved inflation A*tau^(-ell) precedes all source coefficients and shifts. The finite nonconstant degree range 1<=j<=ell is explicit; no vanishing theorem outside this range is claimed.', 'GENUINE common ACTUAL nonzero relative horizontal character is extracted on a positive-density subset of useful shifts CONDITIONALLY on the FULL desired lower-degree inverse. The finite CONTINUOUS-character list, positive density, norm bound and BOTH ORIGINAL-scale coefficient budgets precede ALL original polynomials with unbounded coefficients, ALL observations and sample lengths. Actual remaining lengths and integer shifts agree literally with the genuine child-inverse inputs.', 'Degree-TWO common ACTUAL nonzero RELATIVE character on a positive-density shift set is FULLY PROVED with NO child inverse premise, using the genuine degree-one inverse on TRUE child geometry/filtration. This is univariate and does NOT close the degree-two original nonzero inverse branch.', 'When the ACTUAL difference character is ZERO, the complete actual relative scalar polynomial equals the original compact-normalized diagonal scalar. ACTUAL relative nonzeroness then proves original diagonal nonzeroness. TRUE lattice/basepoint/linear normalizations preserve all NONCONSTANT ORIGINAL monomial coefficients modulo integers; hence original raw monomial bounds are derived in the explicit 1<=j<=ell range. The general nonzero difference/cancellation cases, parent binomial reconstruction and full original inverse remain OPEN.', 'Genuine normalized complex Cauchy-Schwarz/energy and exact pair-duplication means are checked. These author checks do not constitute independent kernel replay, external review, full formalization or prize eligibility.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Original true normalized relative/reduced weights/filteredness/degree, lattice rational geometry and BOTH actual Green-Tao normalizations are retained, including bounded true corrected P(1), SAME nonnormal original coset samples and every original nonconstant horizontal scalar coefficient modulo integers. Arbitrary finite rational native Lie-filtered relative GEOMETRY is retained and actually applies to original reduced IMAGE layers. NOW arbitrary actual terminal quotient NativeData/chart/model/image lattice/metric/smooth projection/identity differential/native Exp/Log and actual projected rational Lie/group filtration of bound ell-1 are CONSTRUCTED. Original model projection is surjective with kernel EXACT F(ell), and all source/image lattice logarithms/Q-spans agree exactly. EVERY actual relative-then-terminal quotient geometric recursion stage exists with bound ell-n; at ell stages the actual group is SUBSINGLETON. Geometric recursion is APPLIED to BOTH original stretched and retained original reduced IMAGE data, with SAME actual projected layers. ACTUAL weighted native terminal polynomial projection has genuine real filteredness, zero-trim degree (ell-1)-k, complete scalar coefficients/native exponentials/exact integer factor samples, and is APPLIED to ACTUAL twice-normalized ORIGINAL univariate source at SAME stretch d without inflating to ordinary s*d. NOW arbitrary WEIGHTED normalized RELATIVE coefficient-polynomial reconstruction is CONSTRUCTED with actual integer pair samples, all aggregate coefficient membership, SAME relative weights, real/integer filteredness, COMPLETE scalar pullbacks and zero-trim degree ell. Actual relative-then-terminal polynomial reduction has degree ell-1 and is APPLIED to ACTUAL twice-normalized ORIGINAL source at SAME stretch d. Generic true basepoint/lattice-linear normalizations preserve ALL actual image filtration weights and PROVE normalized logarithmic zero and degree ell. NOW actual iterated WEIGHTED POLYNOMIAL recursion is CONSTRUCTED at bound ell-n, with genuine compact representative/lattice normalization choices, all original pair coordinate/observable samples, complete scalar and aggregate coefficient preservation, true image weights/degree and exact EVERY-stage integer quotient factor samples. ALL actual stage group/model/lattice/chart/metric/filtration GEOMETRY is PROVED fixed before original coefficients and ALL shifts, equal to geometry-only recursion. At ell stages actual group/orbit is trivial and actual specified-metric canonical native Haar discrepancy is ZERO for every NONEMPTY finite sample. The FULL polynomial recursion is APPLIED to ORIGINAL degree <=d input at SAME stretch d, degree s*d-n and termination at s*d. NOW the TRUE degree-ONE rational-filtration quantitative inverse BASE CASE is PROVED on the ORIGINAL group/model/lattice/metric/canonical Haar. Original group commutativity and proven step<=1 are discharged; literal reclassification preserves original Haar/fundamental-domain/probability/samples/discrepancy. An ACTUALLY NONZERO original horizontal character is PRODUCED with fixed original finite grid, true operator norm and BOTH original monomial/paper-binomial bounds, for RAW UNBOUNDED weighted coefficients and ANY finite variable type including Unit. Exact variable equivalence preserves original cube samples, canonical discrepancy and COMPLETE monomial/binomial coefficients. This inverse is APPLIED to actual recursive degree-one polynomial state; actual node at j=ell-1 exists for ell>0 and retains SAME coefficient/shift-independent actual stage geometry. NOW ANY original finite rational Lie filtration has ACTUAL ORIGINAL terminal torus/action/canonical-Haar invariance, continuous Fourier projections/GROUP eigenlaws/NONZERO frequency mean zero, fixed finite uniform reconstruction/frequency selection/l1 bound, and genuine ZERO-mode OR NONZERO original-terminal-frequency alternative. ACTUAL terminal image-lattice native factor is surjective/equivariant with exact fibers and open quotient in BOTH specified metrics. ZERO mode descends to ACTUAL native terminal quotient; original pushforward equals TRUE quotient canonical Haar by PROVED probability/invariance/uniqueness and explicit metric/Borel transport. Original/descended ZERO integrals and canonical discrepancies agree on EXACT original samples. Compact FUNCTION-space zero family yields fixed finite actual SPATIAL Lipschitz/unit child family and positive detection threshold before ALL source inputs. Actual ZERO-mode weighted-polynomial reduction produces SAME actual image weights, ordinary degree ell-1, complete original scalar pullback and large TRUE quotient native canonical discrepancy in a fixed UNIT child observation. NOW the actual NONZERO-frequency relative-pair OBSERVABLE/MEASURE/UNIT/SAMPLE reduction is PROVED for ANY original rational filtration: true relative terminal-diagonal geometry, first-coordinate eigenlaw, relative canonical mean ZERO, actual metric terminal-factor descent, general canonical integral transport, actual degree-reduced canonical mean ZERO and exact discrepancy, compact spatial approximation and fixed finite unit detection. BOTH actual compact normalizations retain EXACT original univariate Fourier derivative samples; actual constructed weighted degree-reduced polynomial discrepancy equals SAME original derivative mean. A SINGLE fixed finite actual child UNIT family/positive threshold precede ALL raw unbounded coefficients/shifts/samples/original unit observations; no translated observation is assumed unit Lipschitz. Higher-degree nonzero inverse/original horizontal character reconstruction remains OPEN; NOW ACTUAL arbitrary terminal quotient character pullback PROVES ORIGINAL nonzero/horizontal/lattice-integral character, true fixed operator budget and ORIGINAL finite grid. COMPLETE original scalar/monomial coefficients and true scalar degree ell-1 survive, and actual binomial degree extension PROVES child ell-1 table equals ORIGINAL parent ell table. FULL desired NativeRationalWeightedInverseStatement is named ONLY as a proposition; degrees zero/one are PROVED, higher universal inverse UNPROVED. Genuine arbitrary-degree ZERO-MODE induction step is PROVED CONDITIONALLY on FULL LOWER-DEGREE child inverse, with ALL actual original geometry/measure/unit/weights and character/grid/operator/BOTH coefficient inputs discharged. Fixed NATURAL budget and actual bounded Fourier alternative combine the zero character result with the remaining nonzero-mode signal. Degree-TWO ZERO-MODE inverse is NOW FULLY PROVED with NO child inverse hypothesis; degree-TWO original full-discrepancy horizontal-character OR bounded nonzero-frequency alternative is PROVED. Neither the unresolved degree-two nonzero branch nor higher-degree universal inverse is declared solved. NOW genuine NONZERO actual CHILD inverse extraction and actual RELATIVE nonzero horizontal character/grid/operator/BOTH raw monomial and paper-binomial bounds are PROVED CONDITIONALLY on the FULL desired actual lower-degree child inverse. Exact Unit-cube/interval canonical discrepancy transport and all actual normalization/unit/weights/Haar inputs are discharged. The actual compact relative polynomial projects/zero-trims EXACTLY to the true compact degree-reduced polynomial, with COMPLETE scalar/coefficient/binomial table preservation. Degree-TWO NONZERO RELATIVE character extraction is FULLY PROVED with NO child inverse premise, using the true degree-ONE base; this new nonzero reduction is UNIVARIATE and does NOT close original degree-two nonzero inverse. Actual relative diagonal/F_2 model decomposition and native group/Log/lattice embeddings are CONSTRUCTED. Actual diagonal character is ORIGINAL horizontal WHEN genuinely nonzero, with original fixed operator budget/grid; when diagonal is ZERO, actual F_2 difference character is genuinely nonzero continuous/additive and restricted-lattice integral, with fixed norm bound. Relative nonzeroness is not substituted for diagonal nonzeroness; F_2 character extension to all original G is not asserted. Actual reduced quotient character diagonal kills ORIGINAL terminal F_ell. Actual F_2 difference character kills ORIGINAL mixed Lie commutators [G,F_2] by true native relative bracket compatibility and relative horizontality; full [G,G] annihilation/whole-group character extension is not inferred. COMPLETE relative scalar polynomial/every coefficient splits into actual original normalized diagonal scalar plus true F_2 difference scalar. Small combined coefficients do not imply individually small component coefficients. NEXT: actual scalar difference/commutator formula, combined coefficient separation and ORIGINAL nonzero horizontal reconstruction with genuine degree and nonlinearity induction; genuine ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction/pullback with actual finite-list/operator/binomial bounds. GEOMETRIC termination alone does not establish orbit inverse or nonzero character reconstruction. SAME native step bound s unchanged; actual image filtration never re-stretched. Corrected equal-side multivariate inverse or justified reduction remains open. Fixed-data existence bounds only; no unsupported power laws or bounded original coefficients. Keep corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample, which does not obstruct corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION inverse remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.\nNEW DENSE-SHIFT MILESTONE: Actual useful shifts and repeated common relative characters with BOTH ORIGINAL-scale coefficient bounds are now PROVED, conditional only on genuine lower-degree inverse; degree-two version has NO child premise. Pure diagonal (actual difference ZERO) reconstruction of raw original monomial bounds is PROVED in the explicit 1<=j<=ell range. NEXT: original actual nonzero-difference polynomial formula P(n)+Q(n+h)-Q(n)+sigma(h)*n, true group commutator character identities, dense polynomial separation (Green-Tao Lemma 7.6), bracket-polynomial alternative (Claim 7.7), and actual original character reconstruction or refinement of the nonlinearity filtration. Degree induction alone is insufficient for the reducible case: the actual secondary nonlinearity/dimension induction remains required. General original inverse, corrected multivariate inverse, interval Gowers correlation inverse, rough progressions, Alignment and StrongConjecture remain UNPROVED. No unavoidable obstruction has been established. No public repository, PR or prize application yet.'

def declarations():
    result = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}
    return result


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
        code = re.sub(r'\[local instance(?: \d+)?\]', '', helpers.lean_code(read(p)))
        assert not re.search(r'\b(?:set_option|setOptions|instance)\b', code)
        structures = re.findall(r'^\s*structure\s+(\w+)', code, re.M)
        assert structures == (['NativeRationalLieFiltration'] if p.endswith('/NativeRationalLieFiltration.lean') else [])
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
        new_structures=sum(k=='structure' for vs in ds.values() for k,_ in vs),
        new_structure_generated_reports=sum(k=='structure_generated' for vs in ds.values() for k,_ in vs),
        retained_proof_sources_unchanged=True,retained_axiom_sets_unchanged=True,
        standard_axioms_only=True,full_target_proved=False,independent_kernel_replay=False)
    return baseline,files,summary,fixed


def record():
    baseline,files,summary,fixed = check()
    review = dict(date='2026-10-13', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions and Green-Tao section 7 equation 7.10: genuine dense useful shifts, repeated relative characters and original-scale bounds; pure-diagonal raw monomial transfer; nonlinear reconstruction and full target open')
    manifest=dict(baseline)
    manifest.update(date='2026-10-13',files=files,hindman_module_count=summary['project_modules'],
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
    Path('AUDIT.txt').write_text(audit.split(marker)[0]+'\n2026-10-13 '+PREFIX+': PROGRESS. '+' '.join(COMPONENTS)+'\n'+json.dumps(summary)+'\n\n'+marker+'\n'+REMAINING+'\n',encoding='utf-8')
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
