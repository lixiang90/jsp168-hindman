"""Register and audit the actual product quotient and representation increment against its saved baseline."""
from pathlib import Path
import hashlib
import importlib.util
import json
import re
import subprocess
import sys
import time

PREFIX = 'round-product-nil-representation'
OLD = 'round-piece-refinement-hilbert'
spec = importlib.util.spec_from_file_location('previous_audit', 'round-native-rational-subgroup-span-audit.py')
old = importlib.util.module_from_spec(spec)
spec.loader.exec_module(old)
read, obj, digest, write = old.read, old.obj, old.digest, old.write_obj
MODULES = ['Hindman168/ProductCosetQuotient.lean', 'Hindman168/ProductCosetMetric.lean', 'Hindman168/ProductPieceNilRepresentation.lean', 'Hindman168/BoundedRealProductLipschitz.lean', 'Hindman168/ProductPieceNilMultiplication.lean', 'Hindman168/ProductLatticeGeometry.lean']
COMPONENTS = ['The NATURAL coset map from (G x H)/(Gamma x Lambda) to G/Gamma x H/Lambda is bijective and is a homeomorphism for the original group topologies. Neither lattice is assumed normal.', 'The product quotient metric is induced through that exact natural coset equivalence, which is an isometry for the product metric. Compactness is transferred. When the factor metric quotient maps are open quotient maps, the product map is an open quotient map and its metric topology is proved EQUAL to the original quotient topology.', 'Actual original piecewise orbit sums use the product group and SAME product lattice with observable f(z1)+g(z2); the original globally anchored integer powers and stage/piece indices are preserved exactly. Global observable bounds and Lipschitz constants are B1+B2 and L1+L2. Scalar multiplication is realized on the same quotient.', 'Actual pointwise products use observable f(z1)*g(z2) on the same product quotient. A fully proved bounded-product Lipschitz estimate gives bound B1*B2 and Lipschitz constant B1*L2+B2*L1, uniformly in all stages and pieces.', 'The actual product lattice is discrete if its factors are discrete, and its original coset space is compact if the factors are compact. A common nilpotence-class bound s is preserved by the product, using the exact max formula for the product class.']
REMAINING = "Original native geometry, original-law Hilbert construction, actual piece refinement, closed-span nesting and clipping contraction remain proved. Binary product-quotient representation is NOW PROVED for addition and multiplication, with exact original powers, product lattices, explicit uniform observable/Lipschitz bounds and preservation of compactness, lattice discreteness and nilpotence-step bounds. The induced product metric is proved compatible with the original quotient topology under the explicit factor metric quotient-map compatibility conditions. Scalar multiplication on the same quotient is also proved. Next assemble the finite recipe/product closure with complete native manifold data and uniform common complexity, construct the full admissible step-at-most-s nilsequence closed span, and instantiate clipped dense approximation and Ramsey selection with the paper's padding/principal tuple indexing. Calibration/Alignment, subgroup inverse inputs, actual coloring/arithmetic data, ordered positive rapidly separated monochromatic witnesses and quantitative bounds where required remain. Original models, groups, Gamma, laws and StrongConjecture are unchanged. The full target remains unproved. No unavoidable blocker is established; publication, PR and prize application remain pending."


def declarations():
    return {p: old.declarations(p) for p in MODULES}


def register():
    baseline = obj(PREFIX + '-baseline.json')
    assert len(baseline['files']) == 945
    assert all(digest(f['path']) == f['sha256'] for f in baseline['files'])
    ds = declarations()
    names = ['Hindman168.' + name for values in ds.values() for _, name in values]
    assert len(names) == len(set(names)) == 25
    assert sum(kind in {'theorem', 'lemma'} for values in ds.values() for kind, _ in values) == 18
    root, registry = read('Hindman168.lean'), read('Verification.lean')
    for path in MODULES:
        line = 'import ' + path[:-5].replace('/', '.')
        assert line not in root.splitlines()
        root += '\n' + line + '\n'
    for name in names:
        line = '#print axioms ' + name
        assert line not in registry.splitlines()
        registry += '\n' + line + '\n'
    Path('Hindman168.lean').write_text(root, encoding='utf-8')
    Path('Verification.lean').write_text(registry, encoding='utf-8')
    write(PREFIX + '-registration.json', {'baseline_hash_count': 945, 'modules': MODULES,
        'names': names, 'theorem_count': 18, 'declarations': ds})
    print(json.dumps({'registered': len(names), 'modules': len(MODULES)}))


def run_build(kind):
    command = ['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean']
    if kind == 'kernel':
        result = obj(PREFIX + '-build-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + '-build.txt')
    log = PREFIX + ('-build.txt' if kind == 'build' else '-axioms.txt')
    start = time.monotonic()
    with open(log, 'wb') as stream:
        result = subprocess.run(command, stdout=stream, stderr=subprocess.STDOUT)
    record = dict(command=command, exit_code=result.returncode, terminal=True,
                  elapsed_seconds=time.monotonic() - start, log_sha256=digest(log))
    write(PREFIX + '-' + kind + '-result.json', record)
    print(json.dumps(record))
    if result.returncode:
        print(read(log)[-16000:])
        sys.exit(result.returncode)


def check():
    baseline = obj(PREFIX + '-baseline.json')
    registration = obj(PREFIX + '-registration.json')
    changed = [f['path'] for f in baseline['files'] if digest(f['path']) != f['sha256']]
    assert changed == ['Hindman168.lean', 'Verification.lean']
    own = sorted(Path('Hindman168').glob('*.lean'))
    pnt = sorted(Path('PrimeNumberTheoremAnd').rglob('*.lean'))
    assert len(own) == 933 and len(pnt) == 9
    assert set(str(p).replace('\\', '/') for p in own) == {
        f['path'] for f in baseline['files'] if f['path'].startswith('Hindman168/')} | set(MODULES)
    imports = re.findall(r'^import (Hindman168\.\S+)', old.lean_code(read('Hindman168.lean')), re.M)
    assert len(imports) == len(set(imports)) == len(own)
    assert set(imports) == {str(p.with_suffix('')).replace('\\', '.').replace('/', '.') for p in own}
    names = ['Hindman168.' + n for ds in declarations().values() for _, n in ds]
    assert names == registration['names'] and len(names) == 25
    for p in own + pnt + [Path('Hindman168.lean'), Path('Verification.lean')]:
        code = old.lean_code(read(p))
        assert not re.search(r'\b(?:sorry|admit|sorryAx|native_decide|implemented_by)\b', code), p
        assert not re.search(r'^\s*(?:(?:private|protected|noncomputable)\s+)*(?:axiom|unsafe)\b', code, re.M), p
    for p in MODULES:
        assert not re.search(r'\b(?:set_option|setOptions)\b', old.lean_code(read(p)))
        olean = Path('.lake/build/lib/lean') / Path(p).with_suffix('.olean')
        assert olean.stat().st_mtime_ns >= Path(p).stat().st_mtime_ns
    for kind, log in [('build', '-build.txt'), ('kernel', '-axioms.txt')]:
        result = obj(PREFIX + '-' + kind + '-result.json')
        assert result['terminal'] and result['exit_code'] == 0
        assert result['log_sha256'] == digest(PREFIX + log)
        assert result['command'] == (['lake', 'build'] if kind == 'build' else ['lake', 'env', 'lean', 'Verification.lean'])
        assert not re.search(r'(?:error:|warning:)', read(PREFIX + log))
    jobs = re.findall(r'Build completed successfully \((\d+) jobs\)\.', read(PREFIX + '-build.txt'))
    assert len(jobs) == 1 and int(jobs[0]) >= baseline['build_job_count'] + len(MODULES)
    previous, actual = old.reports(OLD + '-axioms.txt'), old.reports(PREFIX + '-axioms.txt')
    assert obj(OLD + '-kernel-result.json')['log_sha256'] == digest(OLD + '-axioms.txt')
    registered = re.findall(r'^#print axioms (\S+)', old.lean_code(read('Verification.lean')), re.M)
    assert len(registered) == len(set(registered)) == len(actual) == 4570
    assert set(registered) == set(actual)
    assert set(actual) - set(previous) == set(names)
    assert all(actual[n] == v for n, v in previous.items())
    assert all(v <= old.ALLOWED for v in actual.values())
    assert {n for n, v in actual.items() if not v} == old.AXIOM_FREE | {'Hindman168.intervalResidueParent'}
    assert old.run(['git', '-C', '.lake/packages/mathlib', 'rev-parse', 'HEAD']) == baseline['mathlib_commit']
    assert old.run(['git', '-C', '../reference-pntplus', 'rev-parse', 'HEAD']) == baseline['pntplus_commit']
    lean = old.run(['lake', 'env', 'lean', '--version'])
    assert 'version 4.32.2,' in lean and 'f3b06c705e6c85f5314019d5d3baab0fec5b580c' in lean
    fixed = obj(OLD + '-preprint-local-check.json')
    assert fixed['fixed_openai_math_commit'] == baseline['openai_math_commit']
    for section in fixed['sections']:
        data = (Path('E:/codex-build/math') / section['path']).read_bytes().replace(b'\r\n', b'\n')
        pinned = subprocess.run(['git', '-C', 'E:/codex-build/math', 'show',
            fixed['fixed_openai_math_commit'] + ':' + section['path']], stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, check=True).stdout.replace(b'\r\n', b'\n')
        assert data == pinned and hashlib.sha256(data).hexdigest() == section['normalized_sha256']
    files = [{'path': f['path'], 'sha256': digest(f['path'])} for f in baseline['files']]
    files += [{'path': p, 'sha256': digest(p)} for p in MODULES]
    assert len(files) == len({f['path'] for f in files}) == 951
    summary = dict(project_modules=len(own), pntplus_modules=len(pnt), source_scan_modules=len(own)+len(pnt),
        source_config_hashes=len(files), build_jobs=int(jobs[0]), axiom_reports=len(actual),
        new_theorems=18, new_definitions=7, new_instances=0, new_axiom_reports=25, standard_axioms_only=True,
        retained_proof_sources_unchanged=True, retained_axiom_sets_unchanged=True,
        root_imports_exact=True, registered_kernel_names_exact=True, full_target_proved=False)
    return baseline, files, summary, fixed


def record():
    baseline, files, summary, fixed = check()
    review = dict(date='2026-10-10', classification='PROGRESS', full_target_proved=False,
        application_review=['PROGRESS. Previous audit rechecked before edits. All 945 retained baseline hashes are checked at registration. Only root imports and registry change; prior proof sources, original statements, original models/lattices/laws, pins and attribution remain intact.', 'The source route is 05_prediction.tex: products and Lipschitz real combinations of finitely many representing families are represented using product nilmanifolds. This increment proves the exact binary algebraic/metric construction and basic lattice/step preservation; it does not claim the entire finite native recipe package.', 'ProductCosetMap is constructed on genuine left-coset quotients by Quotient.lift. Well-definedness and injectivity use the exact relation a^{-1}b in Gamma x Lambda coordinatewise; surjectivity uses representatives of each factor. No normality hypothesis or quotient-group multiplication is used.', 'The topological equivalence uses actual open quotient maps of topological groups. The inverse continuity is checked after composition with the product of the original quotient maps, rather than inferred from an arbitrary set bijection.', 'ProductCosetMetric uses the natural bijection to transport the product metric. The factor metric topologies and the product metric topology are explicit in the compatibility theorem, preventing accidental synthesis of an unrelated quotient topology. The actual induced metric topology is proved equal to the original coinduced quotient topology when the factor metrics have their original quotient maps.', 'The sum observable is constructed as an actual continuous map on the product quotient. Projection maps are 1-Lipschitz, so the Lipschitz constants add. Exact product-group integer powers prove the original piecewise sequence identity; translations and basepoints are paired without changing intervals, modulus or original laws.', 'The multiplication estimate expands f(x)g(x)-f(y)g(y), uses global observable bounds and factor Lipschitz estimates, and obtains Bf*Lg+Bg*Lf. This avoids an invalid claim that multiplication is globally Lipschitz on all of R x R. The resulting bound is independent of w and the number of pieces.', 'The same specified Gamma and Lambda are used throughout. Product lattice discreteness is transported by the natural subtype-product homeomorphism. Original quotient compactness uses the natural coset homeomorphism. The common step bound follows from the exact max of the two nilpotence classes.', 'Arbitrary finite sums/products, full native product manifold packaging, admissible recipe selection and uniform common complexity still need assembly. No broad closed-span density, full Calibration/Alignment, StrongConjecture, publication or prize-submission claim is made. No unavoidable blocker is established.'], new_modules=MODULES, verified=summary, remaining=REMAINING)
    manifest = dict(baseline)
    manifest.update(files=files, hindman_module_count=933, pntplus_module_count=9,
        selected_axiom_report_count=4570, source_scan_module_count=942,
        build_job_count=summary['build_jobs'], build_log=PREFIX+'-build.txt', axiom_log=PREFIX+'-axioms.txt',
        last_round=dict(classification='PROGRESS', new_module_count=6, new_theorem_count=18,
            new_selected_report_count=25, retained_proof_sources_changed=False,
            root_and_registry_changed=True, review_file=PREFIX+'-review.json', remaining=REMAINING))
    manifest['proved_components'] = baseline['proved_components'] + COMPONENTS
    audit = read('AUDIT.txt')
    marker = 'Remaining proof work:'
    assert audit.count(marker) == 1
    assert audit.split(marker, 1)[1].strip() == baseline['last_round']['remaining']
    note = '\n2026-10-10 ' + PREFIX + ': PROGRESS. ' + ' '.join(COMPONENTS) + '\n'
    note += json.dumps(summary) + '\nReview: ' + PREFIX + '-review.json\n\n'
    Path('AUDIT.txt').write_text(audit.split(marker, 1)[0]+note+marker+'\n'+REMAINING+'\n', encoding='utf-8')
    Path('BUILD-EVIDENCE.txt').write_bytes(b'=== COMPLETE BUILD OUTPUT ===\n' +
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n')
    write(PREFIX+'-review.json', review)
    write('verification-manifest.json', manifest)
    write(PREFIX+'-preprint-local-check.json', fixed)
    write(PREFIX+'-checks.json', summary)
    print(json.dumps(summary))


def recheck():
    _, files, summary, _ = check()
    manifest = obj('verification-manifest.json')
    assert manifest['files'] == files and manifest['last_round']['remaining'] == REMAINING
    assert obj(PREFIX+'-review.json')['verified'] == summary
    assert read('AUDIT.txt').split('Remaining proof work:', 1)[1].strip() == REMAINING
    assert Path('BUILD-EVIDENCE.txt').read_bytes() == b'=== COMPLETE BUILD OUTPUT ===\n' + \
        Path(PREFIX+'-build.txt').read_bytes()+b'\n=== COMPLETE AXIOM OUTPUT ===\n'+ \
        Path(PREFIX+'-axioms.txt').read_bytes()+b'\n'
    print(json.dumps(summary))


if __name__ == '__main__':
    sys.stdout.reconfigure(encoding='utf-8')
    mode = sys.argv[1]
    if mode == 'register': register()
    elif mode in {'build', 'kernel'}: run_build(mode)
    elif mode == 'record': record()
    elif mode == 'recheck': recheck()
    else: raise ValueError(mode)
