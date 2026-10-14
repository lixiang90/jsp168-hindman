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

PREFIX = 'round-rough-slow-freezing'
OLD = 'round-rough-model-assembly'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughMonomialOscillation.lean', 'Hindman168/RoughScaledMonomialOscillation.lean', 'Hindman168/RoughSlowPolynomialOscillation.lean', 'Hindman168/RoughJointSlowOscillation.lean', 'Hindman168/RoughCompactParameterFreezing.lean', 'Hindman168/RoughNativeActionFreezing.lean', 'Hindman168/RoughNativeModelFreezing.lean', 'Hindman168/RoughNativeFrozenFactorization.lean', 'Hindman168/RoughFrozenDiscrepancy.lean', 'Hindman168/RoughConvexPieceSelection.lean']
COMPONENTS = ['RoughMonomialOscillation proves actual real power and finite monomial product oscillation bounds by finite algebraic telescoping, with uniform constants depending on the degree and a fixed normalized box radius.', 'RoughScaledMonomialOscillation proves exact rescaling of actual monomial evaluation and combines coefficient decay with the normalized coordinate oscillation. On coordinates bounded by C*Z and coordinate differences at most delta*Z, the monomial change is bounded by degree*A*delta*C^degree.', 'RoughSlowPolynomialOscillation cancels the actual constant coefficient and sums the actual monomial oscillation bounds. The whole slow polynomial changes by at most card(s)*d*A*C^d*delta, uniformly in Z and coefficient sizes.', 'RoughJointSlowOscillation transfers that bound to the actual assembled joint slow polynomial at every original progression index, for arbitrary real spatial inputs.', 'RoughCompactParameterFreezing constructs a uniform parameter modulus for a jointly continuous map on a compact strip. It obtains one positive scalar threshold before all Lipschitz test functions and points, with test error below any prescribed epsilon.', 'RoughNativeActionFreezing proves joint continuity of the original exponential scalar action on the specified metric quotient by transporting both domain and target topologies through the proved compatible metric equality. It obtains uniform original nilmanifold test freezing.', 'RoughNativeModelFreezing combines actual joint slow polynomial value and oscillation bounds with native test freezing. The positive subbox scale is chosen before every progression length, coefficient model, index, scale, observable and quotient point.', 'RoughNativeFrozenFactorization specializes native freezing to the actual original ordered factorization g=exp(aV)*Q*exp(mV). It proves the frozen original quotient test error for the exact kernel factor, preserving multiplication order without a commutation assumption.', 'RoughFrozenDiscrepancy proves that freezing with error epsilon under each of two actual finite probability laws decreases their discrepancy by at most 2*epsilon, with bounds needed only on the original supports.', 'RoughConvexPieceSelection proves that after reweighting a convex combination by total absolute weight error, one positive-weight piece retains any discrepancy threshold strictly below the original discrepancy minus B times that weight error. No division by the number of pieces occurs.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Actual slow-polynomial oscillation and original nilmanifold test freezing are now proved with one threshold preceding all varying progression and observable data. Freezing discrepancy loss and convex selection after bounded weight replacement are proved. These use a uniform continuity modulus for the specified compatible metric, not an unproved linear action bound. Uniform quantitative Lipschitz induced-observable bounds and exact finite residue sampling weights remain open. Actual scalar model assembly, integer spatial realization, original residue cosets, native joint kernel polynomiality, conjugated lattice compactness, joint orbit-map smoothness and affine spatial substitution were retained. The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Section 06 freezes the left factor on a subbox. The actual scalar error polynomial has oscillation at most N*d*A*C^d*delta when coordinate variation is at most delta*Z. The power/product proof is direct algebra and does not mistake algebraic pderiv estimates for an analytic derivative theorem.', 'The normalization identity is proved for the actual monomial evaluations. Coefficient decay cancels Z^degree exactly, while normalized coordinates and their changes are bounded by C and delta. The constant term cancels without any magnitude assumption on that constant.', 'Original real sample indices z<H and arbitrary real spatial inputs are retained. The model freezing threshold is chosen before H, q, scale Z, coefficients, model polynomials, sample index, Lipschitz observable and quotient point. It depends only on fixed native data, V, support, degree, A,C,L and epsilon.', 'NativeNilmanifoldData supplies an arbitrary compatible metric. A smooth map need not be Lipschitz in such a metric. The proof instead establishes actual action continuity in this metric and uses compactness to obtain the uniform modulus needed to select subboxes for a fixed target error. This proves the required freezing error, not a linear C2*delta estimate for all delta.', 'Metric topology transport covers both the quotient in the product domain and the quotient target. The compactness of the original quotient is also transported through that same equality. No new metric or smooth-metric certificate is assumed.', 'The native ordered-factor freezing statement uses the exact original factor Q and the exact order exp(bV)*Q*exp(mV). Neither commutativity nor normality of Gamma is assumed. The actual quotient action is used.', 'The probability discrepancy loss uses actual total mass one and support-wise test errors under both laws. Reweighting selection uses a true convex vector and sum of absolute weight differences; its retained discrepancy is independent of the number of subboxes or residue pieces.', 'Uniform Lipschitz control (or proved uniform Lipschitz approximation with controlled error) for induced tests on the smaller quotients remains a separate obligation. This freezing result alone does not establish the dimension induction or exact residue sampling weights.', 'All retained source hashes and transitive axiom sets are unchanged. These are author-side checks, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions slow-factor freezing and convex discrepancy preservation')
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
