from pathlib import Path
import json

v = json.loads(Path('round-native-orbit-degree-checks.json').read_text())
assert not v['full_target_proved']
p = Path('CONTINUATION.txt')
s = p.read_text(encoding='utf-8').replace('Current batch: round-canonical-face-counting',
    'Earlier batch: round-canonical-face-counting')
start = s.index('Immediate next substantial work:')
end = s.index('The uniform rough-step theorem', start)
s = s[:start] + f'''Current batch: round-native-orbit-degree, verified 2026-10-11. Three modules, {v['new_theorems']} theorems, {v['new_definitions']} definitions; full build ({v['build_jobs']} jobs), {v['selected_axiom_reports']} selected transitive axiom reports, {v['project_modules']} project modules. Retained proof sources and axiom sets are unchanged, standard axioms only, all six pinned paper sections match their Git objects. This is author-side verification, not independent kernel replay.
- FiniteVectorPolynomialDegree defines finiteVectorPolynomialDegreeLE p d := every exponent in the actual list p is <=d. It proves monotonicity, singleton, append, finite sum, rational scale, primitive (d+1), bilinear composition (d+e) and adPower (n*d+e) bounds. It deliberately bounds support exponents, not a minimal degree after cancellation.
- NativeLiePolynomialDegree bounds the actual defect at C*d+e, defect power n at n*(C*d)+e, and field at C*(C*d)+e, where C=nilpotencyClass G. The genuine Picard polynomial has exponent bound (C*C+1)^n. Consequently nativeLieRationalProductPolynomial has bound (C*C+1)^(C+1). These are proved for the actual recursive lists, independent of coefficient values.
- NativeLieOrbitLogPolynomial proves lieOneParameterCurve_int using map_zsmul, defines the polynomial with u=Log(x), w=Log(x^-1*g*x), and proves its real evaluation at EVERY integer k equals the genuine native global Log(g^k*x). The conjugation identity is proved in the original group. nativeLieOrbitLogPolynomial_degree gives the uniform bound (s*s+1)^(s+1) from nilpotencyClass G<=s. No replacement BCH model or assumed log formula is introduced.

Review: the integer-orbit statement has the original complete finite-dimensional simply connected nilpotent Lie-group hypotheses, and is valid for signed k and arbitrary g,x. The bound is coarse but depends only on the class ceiling s. It supplies the ingredient in pinned 08_alignment lines 498-509, not yet the joint native array-log polynomial theorem. Coefficient magnitudes remain unrestricted as required.

Immediate next algebra work: compose the proved actual orbit-log polynomial with the exposed degree-two scalar exponent at finitely many integer array evaluations. A convenient scalar-coordinate construction is, for linear ell:E->R and multivariate P, sum over (m,v) in the orbit list of C(ell(v))*P^m. Prove its evaluation and totalDegree bound <=degree(P)*(s*s+1)^(s+1); projection through a chosen basis yields a vector polynomial. Alternatively introduce finite lists of multivariate scalar polynomials with vector coefficients, preserving exact evaluation and degree. Then apply the existing fixed linear coefficient-recovery map to recover the native ARRAY logarithm from those finitely many evaluations, and substitute t=product of individual tail variables with a bound depending only on fixed dimensions/class. The exact alignmentExposedCubePolynomial_eval theorem supplies equality with integer exponents on admissible actual samples, so the orbit identity need only be applied there; do not claim g^k is defined for arbitrary real exponents. Keep unknown microcell origins in vertex variables, not frozen coefficients. Do not redo Picard degree or orbit-log algebra.

Native face counting is already proved for actual Delta and original raw-supported samples. Connect the model-array/coset translation and reading identities to the cube vertex tests after the joint polynomial work. All previous posterior/rough-step obligations remain below.

''' + s[end:]
p.write_text(s, encoding='utf-8')
print('Updated continuation checkpoint from verified counts.')
