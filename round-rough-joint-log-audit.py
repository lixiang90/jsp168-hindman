"""Audit actual joint logarithmic polynomiality of the native kernel factor.

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

PREFIX = 'round-rough-joint-log'
OLD = 'round-rough-fixed-kernel'
spec = importlib.util.spec_from_file_location('audit_helpers', 'round-native-rational-subgroup-span-audit.py')
helpers = importlib.util.module_from_spec(spec)
spec.loader.exec_module(helpers)
read, obj, digest, write = helpers.read, helpers.obj, helpers.digest, helpers.write_obj
MODULES = ['Hindman168/RoughVectorMvPolynomial.lean', 'Hindman168/RoughParametricCurve.lean', 'Hindman168/RoughParametricDegree.lean', 'Hindman168/RoughParametricPicard.lean', 'Hindman168/RoughNativeProductMvPolynomial.lean', 'Hindman168/RoughVectorMvCoordinates.lean', 'Hindman168/RoughNativeKernelLogPolynomial.lean']
COMPONENTS = ['RoughVectorMvPolynomial represents a vector-valued multivariate polynomial by a finite list of scalar MvPolynomial and original vector pairs. It proves actual evaluation and degree bounds for sums, scalar multiplication, bilinear operations and every real linear scalar projection.', 'RoughParametricCurve lifts the existing finite vector-polynomial coefficient operations to multivariate polynomial coefficients. Specialization at every real parameter point commutes exactly with rational scaling, primitive, bilinear products, iterated adjoints, finite sums and endpoint evaluation.', 'RoughParametricDegree tracks degree in the external parameters separately from the auxiliary curve time. In particular the primitive changes auxiliary time exponents but preserves external parameter degree; bilinear operations add parameter degrees.', 'RoughParametricPicard constructs finite parameter-polynomial defect, defect powers, inverse field and Picard iterates. For nilpotence parameter s and input degree d its n-th Picard coefficient family has external degree at most (s*s+1)^n*d.', 'RoughNativeProductMvPolynomial proves pointwise specialization is exactly the original native rational defect, field and Picard polynomial, then identifies its endpoint with the actual original logarithm of exp(u(x))*exp(w(x)). The joint degree bound is (s*s+1)^(s+1)*d with s the original group nilpotency class.', 'RoughVectorMvCoordinates converts ordinary finite-basis coordinate MvPolynomials to the finite vector representation without increasing degree. It also proves every intrinsic linear coordinate on a subspace-valued polynomial is polynomial of the same degree, using extension of a linear map.', 'RoughNativeKernelLogPolynomial explicitly constructs the joint logarithm of Q(x)=exp(-a(x)V)*P(x)*exp(-m(x)V) by two applications of the actual native product polynomial. It proves equality for every real parameter point, degree at most (((s*s+1)^(s+1))^2)*d, interfaces from ordinary logarithmic coordinates, actual membership in the given character kernel, and the same degree bound for intrinsic kernel coordinates.']
REMAINING = 'StrongConjecture remains unproved; no unavoidable obstruction is established. Joint bounded-degree native logarithmic polynomiality of the exact kernel factor is now proved for arbitrary simultaneous real parameters, from ordinary logarithmic coordinate polynomials, including intrinsic kernel coordinates. Fixed-character rational normalization, strict kernel dimension descent, original kernel quotient compactness, exact ordered factorization and integer-polynomial residue cosets were retained. Assembly with the extracted scalar coefficient models, affine spatial substitution, rational conjugated lattices and their kernel quotients, uniformly Lipschitz induced observables, slow-factor freezing and sampling estimates remain open. The quantitative Leibman obstruction, affine substituted-polynomial coefficient identity, corrected box comparison, stretched-filtration prerequisites, finite density extraction, dimension induction and uniform rough-step comparison remain open. Package finite native readings and connect conditional face laws. Buffered short-bin geometry, prior-event positive probability, extra-conditioning posterior control, quantitative native smooth-observable bounds, conditional face invariance and positive-probability Alignment remain open. HasNativePeriodicIntervalInverse and HasAlignmentMonomialRecurrence remain explicit unproved existence inputs. Complete final ordered positive rapidly separated monochromatic extraction. No independent kernel replay, external review, public contribution or prize submission is claimed.'

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
        application_review=COMPONENTS+['Compared with Section 06 rough-kernel-polynomial: the parameter type sigma is arbitrary, and every evaluation theorem holds for all x:sigma->Real. Thus z and all spatial variables may be included simultaneously; the result is not just separate or single-parameter polynomiality.', 'The old nativeLieRationalProductPolynomial controls an auxiliary real curve time. Merely substituting into that single time would not prove polynomiality in arbitrary u(x),w(x). This batch lifts every coefficient operation and proves exact specialization to the original finite Picard construction before invoking its original-group endpoint theorem.', 'External degree and auxiliary time exponent are separated. Rational integration coefficients depend on the auxiliary time exponent only. Primitive therefore preserves external degree. Bracket products add degree, defect powers give n*s*d+e, field gives s*s*d+e, and Picard iteration is bounded by (s*s+1)^n*d.', 'The new product endpoint is proved equal to nativeLieGlobalLogarithm of the original group product. The three-factor construction preserves multiplication order and uses the genuine global exponential/logarithm inverse twice. No formal BCH model or unrelated matrix group is substituted.', 'The bound C(s)^2*d for C(s)=(s*s+1)^(s+1) is coarse but depends only on old degree and group nilpotency class. It is independent of input polynomial coefficients, progression length, scale and parameter values. All-zero/constant degree and nilpotency class zero are included.', 'Finite-list vector polynomials need not have unique representations. The ordinary basis-coordinate interface proves that every supplied finite-basis logarithmic coordinate family of degree d has the required vector representation. Linear projections yield actual MvPolynomial statements, so polynomiality is not merely a custom predicate.', 'Actual kernel membership follows from the same fixed character and the previously proved factor membership, identically for all real parameter values. Intrinsic linear coordinates on the kernel are covered by extending the linear functional to the ambient space; the degree does not increase. No coefficient-size control is required or claimed.', 'Extracted coefficient models and affine spatial substitutions still need to be assembled with this joint logarithm theorem. Conjugated lattice compactness, analytic slow-factor and induced-observable estimates, sampling comparison and dimension induction remain separate open obligations.', 'All retained proof sources and axiom sets are unchanged; these are author-side checks, not independent kernel replay.']+[REMAINING],
        verified=summary,new_modules=MODULES,remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions rough-kernel-polynomial: joint native logarithm polynomiality and uniform degree bounds')
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
