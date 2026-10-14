"""Audit actual arbitrary native rational Lie-filtered relative geometry and second original reduced-image relative application.

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

PREFIX = 'round-native-rational-filtered-relative'
OLD = 'round-native-relative-layer-rational'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeRationalFilteredGroupBrackets.lean', 'Hindman168/NativeRationalFilteredGroupGeometry.lean', 'Hindman168/NativeRationalFilteredIdeals.lean', 'Hindman168/NativeRationalFilteredRelativeSquare.lean', 'Hindman168/NativeRationalFilteredTerminal.lean', 'Hindman168/NativeRationalLieFiltration.lean', 'Hindman168/NativeRationalRecursiveRelativeApplication.lean', 'Hindman168/NativeRationalRelativeData.lean', 'Hindman168/NativeRationalRelativeExponentialLogarithm.lean', 'Hindman168/NativeRationalRelativeInclusion.lean', 'Hindman168/NativeRationalRelativeLatticeGeometry.lean', 'Hindman168/NativeRationalRelativeLieFiltration.lean', 'Hindman168/NativeRationalRelativeMetric.lean', 'Hindman168/NativeRationalRelativeRationalFiltration.lean', 'Hindman168/NativeRationalRelativeStructures.lean']
COMPONENTS = ['NativeRationalLieFiltration records ACTUAL native Lie layers/antitone/zero-one-top/bracket/rational/terminal conditions only, with NO inverse/degree-drop/geometry compatibility premise. Every field is genuinely CONSTRUCTED for BOTH original stretched filtration and SAME actual original reduced IMAGE filtration.', 'ANY actual rational native Lie filtration integrates to actual normal group layers. Genuine adjoint generator powers and actual finite adjoint formula retain weight i+j; true ideal-difference BCH and actual Exp conjugation prove original group commutator filtration compatibility. Group bracket conditions are DERIVED, not fields assumed in input data. Genuine native Log membership, initial/terminal group layers, original layer closedness/contractibility and restricted-lattice discrete/cocompact geometry are proved.', 'GENUINE relative-square native Lie/group layers NOW exist for ANY actual finite rational native Lie filtration. Actual real-ideal coset Log criterion identifies actual integrated relative Lie subgroups EXACTLY with the original relative square. Complete rational diagonal/first-direction spans recover ENTIRE relative models; SAME original product-lattice intersections are discrete and cocompact.', 'TRUE nativeRationalRelativeData is CONSTRUCTED on EXACT original relative group/model/SAME restricted product lattice, with actual charts/Lie-infinity/boundaryless/contractible structures, compatible original coset metric and open quotient map. SAME nilpotency-step bound s is preserved; no step decrease or replacement group is asserted.', 'Actual generic native relative smooth inclusion has EXACT derivative equal to the true model inclusion. Original native Exp/Log commute with it. Actual original smooth-hom adjoint differentiation and real relative Fi-times-Fi/difference-Fi+1 brackets prove EVERY genuine internal relative bracket weight. No assumed bracket transport or substituted matrix data is used.', 'ALL actual internal generic relative Lie layers, including ZERO, are rational for SAME actual restricted lattice via genuine positive-power equivalence and full injective real-span recovery. Both actual initial Lie layers are top and terminal ell+1 layer is bottom. nativeRelativeRationalLieFiltration genuinely CONSTRUCTS all finite rational Lie-filtered fields on SAME actual relative NativeData.', 'The actual terminal Lie subspace of ANY native finite rational filtration is central by bracket (ell,1) and true terminal zero. Its genuine central exponential subgroup equals SAME actual original group terminal layer. The actual image lattice in true terminal quotient is discrete/cocompact. The further quotient NativeData/chart/actual projected filtration degree decrease remains TO CONSTRUCT.', 'GENUINE SECOND relative native stage is NOW APPLIED to ACTUAL original terminal quotient NativeData and its SAME reduced IMAGE Lie filtration. Actual second relative group membership uses SAME original reduced group layers, actual model layers use SAME original reduced Lie layers, and its actual terminal subspace is central. Reduced filtration is never re-stretched or substituted by a lower-central series. This is a concrete application, not only an abstract interface.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Original actual normalized univariate relative/reduced polynomial weights, real/integer filteredness, degree decrease, lattice rationality/compact layer geometry and BOTH original Green-Tao normalizations are retained, including actual bounded corrected P(1), SAME original nonnormal coset samples and original nonconstant horizontal coefficients modulo integers. NOW an arbitrary ACTUAL finite rational native Lie filtration integrates to true normal group filtration via PROVED original adjoint/BCH commutator weight compatibility. Generic relative Lie/group squares, ENTIRE rational models, SAME specified restricted product lattice, actual native charts/Lie/metric/Exp/Log/bracket maps and genuine internal finite rational Lie filtration are CONSTRUCTED. ALL input fields are discharged for original stretched and actual reduced IMAGE filtration. A genuine SECOND relative native stage is actually APPLIED to SAME original reduced native data/IMAGE layers, with literal original reduced group/model-layer membership. ANY true rational filtered terminal Lie layer is central; its actual terminal quotient image lattice is discrete/cocompact. NEXT: construct generic terminal quotient NativeData/chart/model/lattice/metric and true projected rational Lie filtration with degree ell-1; apply after generic relative stage to close genuine recursive geometry without re-stretching. Current generic relative stage retains degree ell; image-lattice existence alone is not complete quotient data or indefinite degree recursion. ALSO weighted-input normalized relative polynomial reconstruction feeding ACTUAL twice-normalized original polynomial without inflating stretch d to ordinary degree s*d; recursive canonical Haar/metric/frequency transport and ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction/pullback with genuine finite-list/operator/binomial bounds. SAME native nilpotency-step bound s is unchanged. The univariate branch does not supply corrected equal-side multivariate inverse; justify reduction or prove that branch. Fixed-data existence bounds only; no unsupported power laws or bounded original coefficients. Keep corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample, which does not obstruct corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION inverse remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.'

def declarations():
    result = {p: re.findall(r'^\s*(?:noncomputable\s+)?(theorem|lemma|def|abbrev|structure)\s+([A-Za-z][A-Za-z0-9_.]*)', helpers.lean_code(read(p)), re.M) for p in MODULES}
    record='Hindman168/NativeRationalLieFiltration.lean'
    result[record] += [('structure_generated','NativeRationalLieFiltration.'+name) for name in ['mk','layer','antitone','zero','one','bracket','rational','terminal']]
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
        reference_scope='06_rough_progressions and Green-Tao section 7: actual arbitrary rational Lie-filtered native relative geometry/second original image application; generic quotient recursion/nonzero inverse/full prize theorem open')
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
