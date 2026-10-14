"""Audit genuine original rational relative-square Lie geometry, restricted lattice and exact original native relative data.

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

PREFIX = 'round-native-relative-data'
OLD = 'round-relative-square-filtration'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeRealIdealCosets.lean', 'Hindman168/RelativeLieSubalgebra.lean', 'Hindman168/NativeRelativeSquareLieModel.lean', 'Hindman168/NativeRelativeSquareExponentialSubgroup.lean', 'Hindman168/RelativeLinearModelSpan.lean', 'Hindman168/NativeProductRationalInclusions.lean', 'Hindman168/NativeRelativeSquareRational.lean', 'Hindman168/NativeRelativeSquareLatticeGeometry.lean', 'Hindman168/SubgroupStructureTransport.lean', 'Hindman168/NativeRelativeSquareStructures.lean', 'Hindman168/NativeRelativeSquareMetric.lean', 'Hindman168/NativeRelativeSquareData.lean']
COMPONENTS = ['For ANY ACTUAL original REAL native Lie ideal, the ORIGINAL group coset criterion is NOW EXACTLY original global-logarithm difference membership. Genuine native BCH pair-ideal theorem applies via scalar restriction to arbitrary real vectors; actual ideal invariance and global inverses discharge all inputs. No rationality, quotient Exp/Log, lattice-normality or BCH identity premise.', 'ACTUAL relative real model consists of two original vectors in original ideal A whose difference lies in original ideal B. Its genuine Lie-subalgebra bracket closure is PROVED from original ideal invariance and exact bilinear bracket difference. No supplied relative bracket closure.', 'ACTUAL original stretched relative-square Lie subalgebra and ACTUAL product tangent model are NOW constructed from ORIGINAL native Lie lower-central ideals. Exact original model membership and genuine native product Lie-model equality are proved; actual original product Lie equivalence is used, not an assumed matrix model.', 'ACTUAL exponential subgroup of constructed relative Lie algebra EQUALS SAME ORIGINAL relative-square subgroup literally. Genuine real-ideal coset/log criteria and retained exact group/Lie lower-central identification prove both inclusions. ACTUAL original relative square is NOW proved contractible and simply connected.', 'ENTIRE ACTUAL relative linear model is EXACT sum of original layer diagonal image and original next-layer first-coordinate image, for nested original layers. Genuine inclusion and full-span equality are proved, without a spanning premise.', 'ACTUAL original diagonal and first-coordinate embeddings preserve ACTUAL ORIGINAL product-lattice rational log span, using the true positive-power rational-hull criterion and original product exponential. No assertion that original nonabelian Log Gamma is an additive lattice.', 'For EVERY positive fixed stretch and original layer index, GENUINE ACTUAL relative-model rationality against ORIGINAL product lattice is NOW PROVED. ORIGINAL rational lower-central layer spans plus genuine rational embeddings span the ENTIRE actual relative model. All layer/nesting/rational-inclusion inputs are discharged, with no rationality or adapted-basis assumption.', 'ORIGINAL product-lattice intersection in SAME ORIGINAL relative-square group is NOW genuinely DISCRETE, CO-COMPACT and CLOSED. Actual coset quotient embeds CLOSEDLY into original product coset space, its original orbit is COMPACT and its actual quotient is metrizable. PROVED actual rationality/exponential-subgroup equality discharge ALL retained rational-subgroup lattice hypotheses.', 'ACTUAL charted/Lie/boundaryless structures transport along PROVED literal subgroup equality while retaining ORIGINAL subgroup topology and ORIGINAL operations. Actual native source structures are supplied, rather than an assumed smooth compatibility.', 'SAME ORIGINAL relative-square subgroup NOW has constructed native chart, Lie-infinity and boundaryless structures, through PROVED actual exponential-subgroup equality and genuinely proved original native Lie-subalgebra geometry. No Lie/boundaryless or merely compatible replacement-group assumption.', 'An ACTUAL compatible metric on SAME ORIGINAL relative-square coset space is NOW constructed from PROVED original restricted-lattice discreteness/cocompactness and inherited original topology. Actual metric topology equality and original quotient map open/continuous are proved. No spatial Lipschitz inference from topology equality.', 'GENUINE NativeNilmanifoldData(s) is NOW constructed on EXACT SAME ORIGINAL relative-square group, ACTUAL relative tangent subspace, ORIGINAL restricted product lattice and ACTUAL compatible metric. Literal original group/lattice identities and actual relative model TYPE equality are proved. ALL structural, connectedness, rational/lattice and metric inputs are discharged. SAME step bound s ONLY; actual reduced relative quotient, terminal model/rationality, Haar/sample/normalized-polynomial compatibility and NONZERO quantitative inverse still remain open.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic FS/FP remains prize target. ALL retained scalar/standard-torus/native ABELIAN inverse/obstructions, original group/quotient Haar, central Fourier reconstruction/finite frequency detection, original zero-mode descent and actual low-step child native data/metric/exp-log projection, actual relatively compact measurable section/counting lift and compact finite Haar scalar classification remain proved. ACTUAL transversal restriction/counting recovery now EXACTLY recovers original arbitrary base nu with probability mass ONE. GENERAL ORIGINAL NONNORMAL invariant coset probability uniqueness is NOW genuinely proved by actual group Haar scalar normalization and actual original fundamental-domain independence. ACTUAL original center-factor pushforward probability NOW equals genuine child NativeData(s-1) canonical Haar, under actual PROVED Borel sigma-algebra compatibility; true zero-mode child canonical integral/discrepancy identities retain SAME original samples/observables. No normal-lattice converse or homogeneous uniqueness/measure agreement input remains in this compatibility step. The actual child-metric zero-mode family now has genuine uniform compactness and spatial Lipschitz approximation, with one fixed finite ACTUAL UNIT child family and positive fixed discrepancy threshold before all original observables and finite sample sets. SAME actual projected samples and child canonical Haar are retained. No topology-to-Lipschitz inference or assumed descended spatial regularity remains in this step. Actual child character pullback NOW genuinely preserves nonzero/horizontal/original lattice-integral properties with explicit operator bounds and ORIGINAL finite-grid membership. Actual polynomial orbit/degree/log representations and COMPLETE scalar polynomial/monomial/spatial-specialization coefficients are retained. ABELIAN root inverse NOW uses genuine ORIGINAL canonical Haar with proved measure/integral agreement. The actual step-at-most TWO ZERO-FREQUENCY inverse branch is NOW proved, producing a genuine ORIGINAL nonzero finite-grid horizontal character with BOTH monomial and paper-binomial bounds from the PROVED actual abelian child inverse. This is NOT a full step-two inverse: NONZERO central-frequency discrepancies and general child/nonabelian orbit inverse still remain open. Actual same-frequency Fourier pair observable is NOW constructed on ORIGINAL product lattice cosets, with genuine diagonal-center invariance and unique continuous descent to ACTUAL diagonal-center quotient/image lattice. Its actual shifted-pair polynomial preserves degree and gives SAME original shifted/unshifted integer orbit; actual factor sample mean equals original derivative average for EVERY finite sample set. Actual descended pair family is uniform-norm COMPACT and pointwise bounded by ONE for original unit inputs. This is NOT a quantitative inverse. Actual rational diagonal image lattice, native diagonal data and compatible metric are now genuinely proved, while appropriate fiber-product filtered subgroup induction geometry still needs to be constructed and verified. Actual original product canonical Haar is NOW genuinely the transported product of ORIGINAL native probabilities, by true original nonnormal uniqueness and actual product group invariance. Exact original canonical product integrals and coordinate pushforward are proved. Actual same-frequency pair mean equals parent Fourier mean times its conjugate, hence NONZERO original pair mean ZERO. ACTUAL diagonal-factor pushforward probability is PROVED probability and fully invariant under its actual quotient-group action; actual descended pair mean is ZERO for nonzero frequencies and actual factor discrepancy equals SAME original finite derivative average. ACTUAL diagonal center is NOW PROVED CLOSED. ACTUAL original diagonal-center model, full original lattice-column span and actual product-lattice RATIONALITY are NOW PROVED. Its actual exponential subgroup EQUALS ORIGINAL diagonal center literally. Original image lattice is NOW PROVED discrete/cocompact/closed; actual diagonal quotient Lie-infinity/boundaryless/T2/simply-connected structures and compatible metric are constructed. GENUINE NativeData(s) NOW uses EXACT ORIGINAL diagonal quotient group/model/image lattice/metric, with SAME s step bound only. Actual diagonal pushforward probability NOW EXACTLY equals genuine original native diagonal canonical Haar by PROVED original nonnormal uniqueness. NONZERO pair mean ZERO and SAME original derivative sample discrepancy NOW use actual original native canonical Haar itself, not presumed factor agreement. Appropriate rational fiber-product filtration and actual induction-complexity reduction are STILL OPEN, as is NONZERO quantitative Leibman inverse. ACTUAL native diagonal smooth projection, identity derivative, original exp/log compatibility, projected polynomial degree/evaluation/orbit/log and COMPLETE scalar polynomial/coefficient identities are NOW PROVED. SAME descended Fourier pair is NOW transported to ACTUAL specified metric with genuine compactness. ONE FIXED finite genuine spatial Lipschitz approximant family and ONE FIXED finite ACTUAL UNIT family with positive threshold detect ALL large original nonzero-frequency derivative averages on SAME actual projected polynomial orbit and genuine canonical Haar, before all coefficients/shifts/samples. No assumed descended spatial regularity or canonical discrepancy compatibility remains in this step. NEXT suitable actual rational fiber-product filtered subgroup, filtration/degree/complexity induction and NONZERO quantitative Leibman; none may be replaced by an assumed inverse or step-drop interface. Product/diagonal-center quotient does NOT automatically decrease nilpotency step or original dimension. Existing group-difference polynomial/iterated filtration facts remain proved and should be reused; no unproved inverse interface may count as completion. Then actual rational fiber-product filtered geometry and NONABELIAN quantitative Leibman induction, fixed-data existence bounds only and no unsupported power laws. Projected/descended families are actual uniform-norm compact, not asserted spatially unit Lipschitz. Canonical-measure abelian root inverse is now proved. Generic finite-index rough API, actual original residue affine/scales finite obstruction density/descent, full rough-step/dimension/length/cofinal-scale comparison remain open. SEPARATE HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION existence input remains unproved; it is distinct from orbit quantitative Leibman. Conditional face laws/invariance, buffered short-bin geometry, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final original positive ordered separated FS/FP extraction remain unproved. Retain corrected large-N scope/actual unrestricted short-box O(eps) counterexample; no unavoidable full-goal blocker. Author build/hash/source/standard-axiom audits are not independent kernel replay or external peer review. No public repository, PR or prize submission yet; do so at actual completion or genuine unavoidable obstruction with honest scope. ACTUAL algebraic RELATIVE SQUARE subgroups and filtration are NOW constructed: both coordinates lie in original F_i and their relative product in F_(i+1); genuine relative commutator/antitone conditions and terminal diagonal equality are PROVED. Actual internal relative-group initial zero/one layers are top, terminal diagonal is central/normal, and actual quotient image filtration has terminal index d instead of d+1. For genuine ORIGINAL stretched NativeData(s) layers ALL normality/filtration/closedness/terminal inputs are discharged; actual reduced relative filtration has terminal index s*D. This is real FILTRATION-degree reduction, NOT an assumed original group step/dimension drop. ACTUAL original relative-square REAL Lie model and genuine original exponential-subgroup equality are NOW PROVED, with actual contractible/simply-connected original relative group. ENTIRE actual relative model is NOW PROVED RATIONAL against ORIGINAL product-lattice log span, from original rational lower-central layers and actual diagonal/coordinate embeddings. ORIGINAL restricted product lattice is NOW PROVED discrete/cocompact/closed, with true closed coset embedding and compact original relative orbit. Actual original relative subgroup chart/Lie-infinity/boundaryless and compatible metric/topology/open quotient are constructed. GENUINE NativeData(s) NOW uses EXACT SAME ORIGINAL relative-square group/model/restricted lattice/metric; literal group/lattice and proved actual model equality are retained. SAME step bound s only. Actual reduced relative quotient by terminal diagonal still needs native model/image-lattice geometry and canonical Haar/sample/normalized shifted polynomial compatibility; terminal-layer Fourier and NONZERO quantitative Leibman remain open. Whole-product Haar agreement does NOT supply canonical Haar on the relative subgroup; entire-center Fourier decomposition does NOT automatically supply terminal-layer decomposition. NEXT actual original relative native inclusion smoothness/identity derivative/Exp-Log compatibility, actual terminal diagonal subspace and rational central quotient native geometry, then terminal-layer Fourier and normalized polynomial/observable/Haar identities needed for genuine NONZERO quantitative Leibman degree induction. Retain all prior regularity and finite-unit detection without claiming they already prove an inverse.'

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
        reference_scope='06_rough_progressions and Green-Tao section 7: GENUINE ORIGINAL rational relative Lie model, actual restricted lattice and EXACT ORIGINAL relative NativeData(s); reduced terminal quotient geometry/Haar/normalized polynomial/nonzero quantitative Leibman/full prize theorem open')
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
