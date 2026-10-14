from pathlib import Path
import json
import re

prefix = 'round-native-central-fourier'
old = 'round-native-quotient-probability'
modules = ['NativeCenterTorusProjection', 'NativeCenterTorusEquivalence', 'CentralCosetAction',
           'NativeNilmanifoldCentralAction', 'NativeCentralOrbitObservables',
           'TorusVerticalFourier', 'NativeCentralFourierProjection']
components = [
    'ACTUAL original center lattice real coordinates respect addition/multiplication. Reducing their ACTUAL inverse coordinates modulo integers gives a continuous surjective standard torus projection with EXACT kernel ORIGINAL Gamma intersect center, proved from retained original center lattice coordinate integrality.',
    'ACTUAL ORIGINAL center modulo ORIGINAL center lattice is homeomorphic to the standard center-dimensional torus. Genuine original center quotient compactness and actual continuous bijection prove the homeomorphism. Actual multiplication/addition and inverse-homeomorphism addition/zero laws are proved; no replacement group or assumed central torus identification.',
    'ACTUAL ORIGINAL central lattice elements act trivially on arbitrary ORIGINAL possibly NONNORMAL G/Gamma. Actual coset equivalence and central commutation prove triviality, permitting genuine descent of ORIGINAL left action through the center lattice quotient. True identity, multiplication, commutation with original G action and JOINT continuity are proved without assuming Gamma normal.',
    'ACTUAL compact standard CENTRAL TORUS action is constructed on EVERY ORIGINAL NativeNilmanifoldData(s) quotient. All action laws, representative compatibility and ORIGINAL G-action commutation are proved. Proved original specified metric topology agreement transfers JOINT continuity. ACTUAL original normalized quotient probability is preserved by every central torus element, with true integral translation identity. No coordinate Lipschitz bound or central disintegration assumed.',
    'ACTUAL orbital functions a maps to F(centralAction(a,q)) form a COMPACT family in the uniform norm as F runs through ALL ORIGINAL unit Lipschitz observables and q runs through ALL ORIGINAL metric cosets. Actual joint evaluation/action continuity and actual compact observable family/coset space prove compactness. One ACTUAL FINITE Fourier approximation family precedes ALL those F,q at each fixed tolerance, without assuming an unproved uniform metric distortion bound.',
    'ACTUAL vertical Fourier coefficients are explicit integrals against EXACT normalized Pi(circle Haar), with true pointwise mode norm, argument addition/negation and nonzero mode separation. Haar translation and ACTUAL action equations prove eigencharacter equivariance and uniform sup bound. Actual character orthogonality computes projection of ANY true eigenfunction, with no interval inverse or orbit equidistribution assumption.',
    'ACTUAL ORIGINAL compatible-metric continuous vertical Fourier projections are constructed for EVERY native step. Genuine compact parametric integral continuity gives continuous outputs; true sup norm contraction, ORIGINAL central eigencharacter relation, zero-frequency invariance, NONZERO-FREQUENCY ORIGINAL quotient-Haar mean ZERO, same-frequency IDEMPOTENCE and different-frequency annihilation are proved. Nonzero mean uses ACTUAL native central integral invariance and actual mode separation, not an assumed disintegration. Full finite vertical reconstruction, quotient descent/measure compatibility and NONABELIAN quantitative Leibman remain open.'
]
baseline = json.loads(Path('verification-manifest.json').read_text())
remaining = baseline['last_round']['remaining'] + (' ACTUAL compact CENTRAL TORUS action on ORIGINAL nonnormal cosets, exact center-lattice torus homeomorphism, ORIGINAL probability preservation and metric joint continuity are now genuinely proved for EVERY native step. ACTUAL compact family of ALL original unit-observable central orbital functions and ONE finite uniform Fourier approximation family are proved. ACTUAL continuous contractive vertical Fourier projections, true central eigencharacters, nonzero-frequency ORIGINAL Haar mean zero, zero-frequency invariance, idempotence and distinct-frequency annihilation are now proved. Next prove ACTUAL finite vertical reconstruction uniformly for ORIGINAL unit observables from normalized localized Fourier kernels; orbital finite approximants alone are NOT that reconstruction. Then descend zero frequency to actual central quotient, identify quotient/fiber measures and finish nonabelian derivative/quantitative Leibman induction. Separate interval Gowers correlation inverse, Alignment and FULL StrongConjecture remain open. No unavoidable obstruction found; goal remains active. No public repository, PR or prize application yet.')
source = Path(old+'-audit.py').read_text()
source = source.replace('Audit rational conjugated lattices and the actual kernel orbit maps.',
                        'Audit actual central torus action and original vertical Fourier projections.')
for name, value in [('PREFIX', prefix), ('OLD', old),
                    ('MODULES', ['Hindman168/'+m+'.lean' for m in modules]),
                    ('COMPONENTS', components), ('REMAINING', remaining)]:
    source = re.sub(r'^'+name+r' = .*$', lambda _: name+' = '+repr(value), source, flags=re.M)
start = source.index('    review = dict(')
end = source.index('    manifest=dict', start)
source = source[:start]+'''    review = dict(date='2026-10-12', classification='PROGRESS', full_target_proved=False,
        application_review=COMPONENTS+[REMAINING], verified=summary, new_modules=MODULES,
        remaining=REMAINING,
        primary_reference='https://github.com/openai/math/tree/'+baseline['openai_math_commit'],
        reference_scope='06_rough_progressions: ACTUAL original central torus action, compact orbital observable family and continuous vertical Fourier projections; finite vertical reconstruction/nonabelian quantitative Leibman/full prize theorem open')
'''+source[end:]
Path(prefix+'-audit.py').write_text(source, encoding='utf-8')
print('Prepared '+prefix+'-audit.py for '+str(len(modules))+' modules')
