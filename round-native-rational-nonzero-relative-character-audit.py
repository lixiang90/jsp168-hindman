"""Audit ACTUAL nonzero child/relative inverse extraction, closed degree-two relative extraction, genuine original diagonal/F_2 character alternatives and complete scalar/coefficient splitting.

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

PREFIX = 'round-native-rational-nonzero-relative-character'
OLD = 'round-native-rational-nonzero-pair'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeRationalCompactRelativePolynomial.lean', 'Hindman168/NativeRationalDegreeTwoNonzeroRelativeInverse.lean', 'Hindman168/NativeRationalNonzeroChildInverse.lean', 'Hindman168/NativeRationalNonzeroRelativeInverse.lean', 'Hindman168/NativeRationalRelativeCharacterBudget.lean', 'Hindman168/NativeRationalRelativeCharacterSplitting.lean', 'Hindman168/NativeRationalRelativeDiagonalGeometry.lean', 'Hindman168/NativeRationalRelativeDiagonalTerminal.lean', 'Hindman168/NativeRationalRelativeDifferenceCharacter.lean', 'Hindman168/NativeRationalRelativeMixedCommutator.lean', 'Hindman168/NativeRationalRelativePolynomialSplitting.lean', 'Hindman168/NativeRationalRelativeReconstructionAlternative.lean', 'Hindman168/NativeUnitCubePolynomialDiscrepancy.lean', 'Hindman168/ScalarUnitCubeMean.lean']
COMPONENTS = ['Exact Unit-variable cube/interval finite means and ACTUAL native canonical polynomial discrepancies agree, including empty intervals. The nonzero derivative signal on original integer intervals is transported onto the exact Unit cube used by the desired child inverse, without a change of sample length or canonical mean.', 'GENUINE nonzero-mode actual CHILD inverse extraction is PROVED CONDITIONALLY on the FULL desired lower-degree inverse for ACTUAL relative-then-terminal data/true image filtration. All Fourier pair/actual canonical Haar/unit detection/original normalization/weighted child polynomial/sample inputs are discharged. A positive NATURAL child norm/finite-grid/monomial/binomial budget is fixed before ALL raw original coefficients, ALL shifts, positive sample lengths and original unit observations.', 'Actual compact-normalized RELATIVE polynomial is explicitly constructed with TRUE relative rational-filtration weights. Its terminal projection/zero-trim is EXACTLY the previously constructed actual compact degree-reduced polynomial. Actual quotient character pullback preserves the COMPLETE scalar polynomial, EVERY monomial coefficient and the paper-binomial table from true child degree ell-1 to relative parent degree ell; the degree-table extension is discharged by true weights.', 'GENUINE actual NONZERO RELATIVE horizontal character extraction is PROVED CONDITIONALLY on the sole FULL actual lower-degree child inverse. Actual quotient projection surjectivity proves relative nonzeroness; actual original relative-group commutator annihilation/restricted-lattice integrality and fixed operator norm/finite horizontal grid are proved. BOTH relative raw monomial and ell-degree paper-binomial coefficient bounds follow on the ACTUAL compact-normalized relative polynomial, with constants fixed before ALL original coefficients/shifts/sample lengths/observations.', 'Degree-TWO nonzero RELATIVE horizontal-character extraction is FULLY PROVED with NO child inverse premise: true actual degree-reduced filtration has degree ONE and its full inverse is already proved. This theorem is UNIVARIATE (Unit variables). It does NOT reconstruct an original nonzero horizontal character or close the degree-two original nonzero inverse branch. The previously closed degree-two ZERO mode covers any finite variable type and is retained.', 'Actual relative model/group diagonal embeddings are constructed with true native Log compatibility and SAME original lattice inclusion. Every relative model vector decomposes EXACTLY into its actual diagonal second coordinate plus actual FIRST DIFFERENCE direction in ORIGINAL F_2. A nonzero relative character has nonzero diagonal OR nonzero F_2 difference component. Relative nonzeroness is never used to assert diagonal nonzeroness.', 'Actual diagonal character has ORIGINAL group additivity, ORIGINAL commutator annihilation and ORIGINAL lattice integrality. WHEN its true diagonal component is nonzero, it is a genuine ORIGINAL horizontal character with a fixed true operator budget and ORIGINAL finite horizontal grid. The actual F_2 difference component is a genuine continuous additive character on the original F_2 group, integral on its actual restricted lattice; its nonzero linear component proves its actual group character nonzero by the genuine native exponential. No extension of that character to the whole original group is asserted.', 'Fixed geometry-only diagonal/difference operator budgets bound BOTH actual components. A genuine bounded reconstruction alternative gives ORIGINAL nonzero horizontal diagonal character/grid OR diagonal ZERO and a nonzero actual F_2 character. Actual characters pulled from the true reduced quotient have diagonal component annihilating ORIGINAL terminal F_ell, proved from true relative-terminal diagonal membership and actual projection kernel.', 'Complete ACTUAL compact-normalized relative scalar polynomial and EVERY monomial coefficient split EXACTLY into the original normalized diagonal scalar plus the actual F_2-valued difference polynomial scalar. The difference character is applied only to its true F_2 model. Small combined coefficients do NOT imply small separate diagonal/difference coefficients; useful-shift selection, coefficient separation and ORIGINAL nonzero horizontal reconstruction remain genuine open work. This is substantive actual induction/reconstruction progress, not the full original quantitative inverse or the prize theorem.', 'The genuine actual F_2 difference character annihilates ORIGINAL mixed Lie commutators [G,F_2], proved from actual relative bracket compatibility and relative horizontality. Actual original mixed bracket lands in SAME F_2 by the true Lie filtration bracket/antitone laws. No assumed mixed-bracket compatibility or [G,G] annihilation/whole-original-group extension is introduced.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Original true normalized relative/reduced weights/filteredness/degree, lattice rational geometry and BOTH actual Green-Tao normalizations are retained, including bounded true corrected P(1), SAME nonnormal original coset samples and every original nonconstant horizontal scalar coefficient modulo integers. Arbitrary finite rational native Lie-filtered relative GEOMETRY is retained and actually applies to original reduced IMAGE layers. NOW arbitrary actual terminal quotient NativeData/chart/model/image lattice/metric/smooth projection/identity differential/native Exp/Log and actual projected rational Lie/group filtration of bound ell-1 are CONSTRUCTED. Original model projection is surjective with kernel EXACT F(ell), and all source/image lattice logarithms/Q-spans agree exactly. EVERY actual relative-then-terminal quotient geometric recursion stage exists with bound ell-n; at ell stages the actual group is SUBSINGLETON. Geometric recursion is APPLIED to BOTH original stretched and retained original reduced IMAGE data, with SAME actual projected layers. ACTUAL weighted native terminal polynomial projection has genuine real filteredness, zero-trim degree (ell-1)-k, complete scalar coefficients/native exponentials/exact integer factor samples, and is APPLIED to ACTUAL twice-normalized ORIGINAL univariate source at SAME stretch d without inflating to ordinary s*d. NOW arbitrary WEIGHTED normalized RELATIVE coefficient-polynomial reconstruction is CONSTRUCTED with actual integer pair samples, all aggregate coefficient membership, SAME relative weights, real/integer filteredness, COMPLETE scalar pullbacks and zero-trim degree ell. Actual relative-then-terminal polynomial reduction has degree ell-1 and is APPLIED to ACTUAL twice-normalized ORIGINAL source at SAME stretch d. Generic true basepoint/lattice-linear normalizations preserve ALL actual image filtration weights and PROVE normalized logarithmic zero and degree ell. NOW actual iterated WEIGHTED POLYNOMIAL recursion is CONSTRUCTED at bound ell-n, with genuine compact representative/lattice normalization choices, all original pair coordinate/observable samples, complete scalar and aggregate coefficient preservation, true image weights/degree and exact EVERY-stage integer quotient factor samples. ALL actual stage group/model/lattice/chart/metric/filtration GEOMETRY is PROVED fixed before original coefficients and ALL shifts, equal to geometry-only recursion. At ell stages actual group/orbit is trivial and actual specified-metric canonical native Haar discrepancy is ZERO for every NONEMPTY finite sample. The FULL polynomial recursion is APPLIED to ORIGINAL degree <=d input at SAME stretch d, degree s*d-n and termination at s*d. NOW the TRUE degree-ONE rational-filtration quantitative inverse BASE CASE is PROVED on the ORIGINAL group/model/lattice/metric/canonical Haar. Original group commutativity and proven step<=1 are discharged; literal reclassification preserves original Haar/fundamental-domain/probability/samples/discrepancy. An ACTUALLY NONZERO original horizontal character is PRODUCED with fixed original finite grid, true operator norm and BOTH original monomial/paper-binomial bounds, for RAW UNBOUNDED weighted coefficients and ANY finite variable type including Unit. Exact variable equivalence preserves original cube samples, canonical discrepancy and COMPLETE monomial/binomial coefficients. This inverse is APPLIED to actual recursive degree-one polynomial state; actual node at j=ell-1 exists for ell>0 and retains SAME coefficient/shift-independent actual stage geometry. NOW ANY original finite rational Lie filtration has ACTUAL ORIGINAL terminal torus/action/canonical-Haar invariance, continuous Fourier projections/GROUP eigenlaws/NONZERO frequency mean zero, fixed finite uniform reconstruction/frequency selection/l1 bound, and genuine ZERO-mode OR NONZERO original-terminal-frequency alternative. ACTUAL terminal image-lattice native factor is surjective/equivariant with exact fibers and open quotient in BOTH specified metrics. ZERO mode descends to ACTUAL native terminal quotient; original pushforward equals TRUE quotient canonical Haar by PROVED probability/invariance/uniqueness and explicit metric/Borel transport. Original/descended ZERO integrals and canonical discrepancies agree on EXACT original samples. Compact FUNCTION-space zero family yields fixed finite actual SPATIAL Lipschitz/unit child family and positive detection threshold before ALL source inputs. Actual ZERO-mode weighted-polynomial reduction produces SAME actual image weights, ordinary degree ell-1, complete original scalar pullback and large TRUE quotient native canonical discrepancy in a fixed UNIT child observation. NOW the actual NONZERO-frequency relative-pair OBSERVABLE/MEASURE/UNIT/SAMPLE reduction is PROVED for ANY original rational filtration: true relative terminal-diagonal geometry, first-coordinate eigenlaw, relative canonical mean ZERO, actual metric terminal-factor descent, general canonical integral transport, actual degree-reduced canonical mean ZERO and exact discrepancy, compact spatial approximation and fixed finite unit detection. BOTH actual compact normalizations retain EXACT original univariate Fourier derivative samples; actual constructed weighted degree-reduced polynomial discrepancy equals SAME original derivative mean. A SINGLE fixed finite actual child UNIT family/positive threshold precede ALL raw unbounded coefficients/shifts/samples/original unit observations; no translated observation is assumed unit Lipschitz. Higher-degree nonzero inverse/original horizontal character reconstruction remains OPEN; NOW ACTUAL arbitrary terminal quotient character pullback PROVES ORIGINAL nonzero/horizontal/lattice-integral character, true fixed operator budget and ORIGINAL finite grid. COMPLETE original scalar/monomial coefficients and true scalar degree ell-1 survive, and actual binomial degree extension PROVES child ell-1 table equals ORIGINAL parent ell table. FULL desired NativeRationalWeightedInverseStatement is named ONLY as a proposition; degrees zero/one are PROVED, higher universal inverse UNPROVED. Genuine arbitrary-degree ZERO-MODE induction step is PROVED CONDITIONALLY on FULL LOWER-DEGREE child inverse, with ALL actual original geometry/measure/unit/weights and character/grid/operator/BOTH coefficient inputs discharged. Fixed NATURAL budget and actual bounded Fourier alternative combine the zero character result with the remaining nonzero-mode signal. Degree-TWO ZERO-MODE inverse is NOW FULLY PROVED with NO child inverse hypothesis; degree-TWO original full-discrepancy horizontal-character OR bounded nonzero-frequency alternative is PROVED. Neither the unresolved degree-two nonzero branch nor higher-degree universal inverse is declared solved. NOW genuine NONZERO actual CHILD inverse extraction and actual RELATIVE nonzero horizontal character/grid/operator/BOTH raw monomial and paper-binomial bounds are PROVED CONDITIONALLY on the FULL desired actual lower-degree child inverse. Exact Unit-cube/interval canonical discrepancy transport and all actual normalization/unit/weights/Haar inputs are discharged. The actual compact relative polynomial projects/zero-trims EXACTLY to the true compact degree-reduced polynomial, with COMPLETE scalar/coefficient/binomial table preservation. Degree-TWO NONZERO RELATIVE character extraction is FULLY PROVED with NO child inverse premise, using the true degree-ONE base; this new nonzero reduction is UNIVARIATE and does NOT close original degree-two nonzero inverse. Actual relative diagonal/F_2 model decomposition and native group/Log/lattice embeddings are CONSTRUCTED. Actual diagonal character is ORIGINAL horizontal WHEN genuinely nonzero, with original fixed operator budget/grid; when diagonal is ZERO, actual F_2 difference character is genuinely nonzero continuous/additive and restricted-lattice integral, with fixed norm bound. Relative nonzeroness is not substituted for diagonal nonzeroness; F_2 character extension to all original G is not asserted. Actual reduced quotient character diagonal kills ORIGINAL terminal F_ell. Actual F_2 difference character kills ORIGINAL mixed Lie commutators [G,F_2] by true native relative bracket compatibility and relative horizontality; full [G,G] annihilation/whole-group character extension is not inferred. COMPLETE relative scalar polynomial/every coefficient splits into actual original normalized diagonal scalar plus true F_2 difference scalar. Small combined coefficients do not imply individually small component coefficients. NEXT: useful shift selection, actual relative character repetition/finite-grid uniformity, combined coefficient separation and ORIGINAL nonzero horizontal reconstruction in BOTH diagonal/difference cases under genuine higher-degree induction; genuine ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction/pullback with actual finite-list/operator/binomial bounds. GEOMETRIC termination alone does not establish orbit inverse or nonzero character reconstruction. SAME native step bound s unchanged; actual image filtration never re-stretched. Corrected equal-side multivariate inverse or justified reduction remains open. Fixed-data existence bounds only; no unsupported power laws or bounded original coefficients. Keep corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample, which does not obstruct corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION inverse remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.'

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
        reference_scope='06_rough_progressions and Green-Tao section 7: actual nonzero relative character induction/reconstruction and genuine diagonal/F_2 alternatives; original coefficient separation/full inverse and prize theorem open')
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
