"""Audit actual arbitrary native terminal quotients, projected rational filtrations, finite geometric degree recursion and actual weighted terminal polynomial projection.

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

PREFIX = 'round-native-rational-terminal-recursion'
OLD = 'round-native-rational-filtered-relative'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/NativeRationalDegreeOriginalApplication.lean', 'Hindman168/NativeRationalDegreeRecursion.lean', 'Hindman168/NativeRationalOriginalTerminalPolynomial.lean', 'Hindman168/NativeRationalTerminalExponentialLogarithm.lean', 'Hindman168/NativeRationalTerminalGroupFiltration.lean', 'Hindman168/NativeRationalTerminalImageLayers.lean', 'Hindman168/NativeRationalTerminalLattice.lean', 'Hindman168/NativeRationalTerminalPolynomial.lean', 'Hindman168/NativeRationalTerminalProjection.lean', 'Hindman168/NativeRationalTerminalProjectionKernel.lean', 'Hindman168/NativeRationalTerminalQuotientData.lean', 'Hindman168/NativeRationalTerminalQuotientMetric.lean', 'Hindman168/NativeRationalTerminalQuotientStructures.lean', 'Hindman168/NativeRationalTerminalRationalSpan.lean']
COMPONENTS = ['ANY actual finite rational native Lie filtration now has TRUE terminal quotient NativeData on original group/model quotient, SAME actual image lattice and genuine compatible metric. Original central terminal model/lattice proofs discharge all actual chart/Lie/boundaryless/T2/simply-connected/discreteness/cocompactness inputs. SAME native step bound s is unchanged.', 'ACTUAL smooth original terminal group projection has identity differential EXACTLY the true model quotient projection. Native Exp/Log commute with it by actual hom uniqueness. Original lattice logarithms and their actual Q-spans map EXACTLY to SAME image lattice logarithms/Q-spans; source and image lattices are never treated as substituted coordinate lattices.', 'The actual model projection is surjective with kernel EXACT ORIGINAL terminal F(ell). True output Lie layers are images of EVERY original F(i); true output group layers are original integrated group images. Exact native Log membership/actual Exp lifting, genuine smooth-hom bracket transport, real-span rationality, initial top layers and actual terminal vanishing construct ALL output NativeRationalLieFiltration fields at degree ell-1.', 'Actual output native integrated group layers equal SAME original projected group layers; group brackets/initial/terminal conditions hold literally for these actual image layers. No re-stretched lower-central filtration or assumed degree-drop compatibility is used. Truncated ell=0 is handled from input top=bottom and actual trivial group.', 'GENUINE arbitrary degree recursion is NOW CONSTRUCTED: actual relative native data then actual terminal quotient native data gives bound ell-1; every actual group/model/lattice/chart/metric/finite rational filtration stage exists at bound ell-n. At ell stages the actual degree-zero group is proved SUBSINGLETON. This is finite GEOMETRIC termination, not a quantitative inverse conclusion.', 'FULL genuine geometric recursion is NOW APPLIED to BOTH original stretched data and SAME retained original reduced IMAGE data. The next actual projected layers literally retain original reduced Lie layers in the relative model and true quotient projection; no source layer compatibility is assumed.', 'ACTUAL weighted native coefficient polynomials project to SAME true terminal quotient with original evaluations/native exponentials/integer coset factor samples, COMPLETE scalar polynomials and EVERY scalar coefficient. All real filteredness inputs are discharged from actual output brackets/Exp layers. True zero-trim ordinary degree is at most (ell-1)-k, including zero/truncated cases.', 'Actual terminal weighted-polynomial transport is NOW APPLIED to ACTUAL twice-normalized ORIGINAL ordinary-degree-bounded univariate polynomials, arbitrary starting values and UNBOUNDED coefficients. Every source weight is discharged with SAME original stretch d, not enlarged ordinary degree s*d. True terminal output weights and zero-trim degree at most s*d-1 are proved, with actual original basepoint/lattice-corrected integer factor samples.']
REMAINING = 'StrongConjecture remains UNPROVED; no unavoidable obstruction established. Full original positive distinct rapidly separated monochromatic finite sums/products is the prize target. Original true normalized relative/reduced weights/filteredness/degree, lattice rational geometry and BOTH actual Green-Tao normalizations are retained, including bounded true corrected P(1), SAME nonnormal original coset samples and every original nonconstant horizontal scalar coefficient modulo integers. Arbitrary finite rational native Lie-filtered relative GEOMETRY is retained and actually applies to original reduced IMAGE layers. NOW arbitrary actual terminal quotient NativeData/chart/model/image lattice/metric/smooth projection/identity differential/native Exp/Log and actual projected rational Lie/group filtration of bound ell-1 are CONSTRUCTED. Original model projection is surjective with kernel EXACT F(ell), and all source/image lattice logarithms/Q-spans agree exactly. EVERY actual relative-then-terminal quotient geometric recursion stage exists with bound ell-n; at ell stages the actual group is SUBSINGLETON. Geometric recursion is APPLIED to BOTH original stretched and retained original reduced IMAGE data, with SAME actual projected layers. ACTUAL weighted native terminal polynomial projection has genuine real filteredness, zero-trim degree (ell-1)-k, complete scalar coefficients/native exponentials/exact integer factor samples, and is APPLIED to ACTUAL twice-normalized ORIGINAL univariate source at SAME stretch d without inflating to ordinary s*d. NEXT: arbitrary WEIGHTED native normalized RELATIVE coefficient-polynomial reconstruction, especially feeding actual twice-normalized source, and exact original pair samples at successive true relative/quotient stages; recursive orbit discrepancy/canonical Haar/specified metric/finite-unit/nonzero frequency transport; genuine ORIGINAL NONZERO quantitative Leibman horizontal-character reconstruction/pullback with actual finite-list/operator/binomial bounds. GEOMETRIC termination alone does not establish orbit inverse or nonzero character reconstruction. SAME native step bound s unchanged; actual image filtration never re-stretched. Corrected equal-side multivariate inverse or justified reduction remains open. Fixed-data existence bounds only; no unsupported power laws or bounded original coefficients. Keep corrected Green-Tao equal-side/erratum scope, actual large-N thresholds, equal-cube tiling/boundary discard/translation/integer bounded-location consequences and retained unrestricted-short-box O(eps) counterexample, which does not obstruct corrected full goal. Separate HasNativePeriodicIntervalInverse interval Gowers-to-finite-list nilsequence CORRELATION inverse remains UNPROVED, distinct from orbit quantitative Leibman. Actual rough progression density/obstruction/descent, step/dimension/length/cofinal-scale comparison, conditional face laws/cube invariance, buffered bins, prior-event positivity, extra-conditioning posterior control, positive-probability Alignment, HasAlignmentMonomialRecurrence and final FS/FP extraction remain UNPROVED. All earlier retained results and standard-axiom reports preserved. Author source/build/axiom checking is not independent kernel replay or external peer review. No public repository, PR or prize submission yet; execute authorized publication/application at actual full completion or genuine unavoidable obstruction with honest scope.'

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
        reference_scope='06_rough_progressions and Green-Tao section 7: actual arbitrary terminal quotient/projected rational filtration/geometric recursion/weighted polynomial projection; relative weighted reconstruction/nonzero inverse/full prize theorem open')
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
