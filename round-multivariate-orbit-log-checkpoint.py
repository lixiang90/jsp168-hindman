from pathlib import Path
import json

v = json.loads(Path('round-multivariate-orbit-log-checks.json').read_text())
assert not v['full_target_proved']
p = Path('CONTINUATION.txt')
s = p.read_text(encoding='utf-8').replace('Current batch: round-native-orbit-degree',
    'Earlier batch: round-native-orbit-degree')
start = s.index('Immediate next algebra work:')
end = s.index('The uniform rough-step theorem', start)
s = s[:start] + f'''Current batch: round-multivariate-orbit-log, verified 2026-10-11. Five modules, {v['new_theorems']} theorems, {v['new_definitions']} definitions; full build ({v['build_jobs']} jobs), {v['selected_axiom_reports']} selected transitive axiom reports, {v['project_modules']} project modules. Retained sources and axiom sets are unchanged, standard axioms only, all six pinned paper sections match their Git objects. This is author-side verification, not independent kernel replay.
- VectorPolynomialMultivariateProjection constructs sum C(ell(v))*P^m recursively from the actual vector coefficient list. Evaluation equals ell(finiteVectorPolynomialEval p (eval P)), with total degree <=listExponentBound*P.totalDegree.
- NativeLieMultivariateOrbitLog composes that construction with the actual nativeLieOrbitLogPolynomial. It has degree <=(s*s+1)^(s+1)*d and evaluates to ell(Log(g^k*b)) at all points where eval P equals the signed integer k. This is an actual multivariate real polynomial, not a polynomiality assumption.
- RationalPolynomialRealTransfer proves total degree nonincrease and exact evaluation commutation for MvPolynomial.map (Rat.castHom R), instantiated at R=real. The proof of evaluation uses eval2_eq_eval_map and hom_eval2, preserving integer casts.
- AlignmentExposedOrbitLogPolynomial specializes to the exposure-fixed original degree-two scalar exponent. Degree <=2*(s*s+1)^(s+1), integer evaluation and freezing on the complete exposure fiber are proved. The group elements g,b and linear functional ell are fixed inputs, not claimed to become fixed without their own exposure facts.
- AlignmentActualOrbitLogEvaluation discharges the scalar-integrality premise using alignmentExposedCubePolynomial_eval at the actual cube vertex and tail product, with actual integer array argument divided by M. It returns precisely ell(Log(g^k*b)) for that original integer exponent. Signed inputs, own-target filtering and unknown microcell origin in X are preserved.

Review: the projected single-orbit logarithm is now explicit and uniformly bounded-degree after the original exponent. It is not yet the full native array-group log polynomial. No real-valued exponent g^r is introduced. No hypothesis on coefficient magnitudes is added.

Immediate next algebra work: recover full array-log coordinates from the fixed finite evaluation family, then substitute cube vertex and individual tail variables with uniform degree. Located exact APIs: AlignmentNativeArrayTranslationCoordinates.alignmentNativeArrayModelCoefficients n u hu is a REAL LINEAR EQUIVALENCE from alignmentNativeFiniteImageModel to alignmentLiePolynomialArrays; alignmentNativeArrayExponential_evaluation identifies every integer evaluation with the actual native exponential. AlignmentNativeArrayTopology.alignmentNativeArrayEquiv_symm_coordinate gives selected group values. AlignmentNativeArrayCharted.alignmentNativeArrayExponentialHomeomorph gives the actual model-to-array global chart. Use its inverse and native Log/Exp inverse identities to prove that the model coefficient array's selected evaluations are the native logs of the selected group values. For polynomial extension off the admissible set, FiniteRealSubmoduleRetraction.finiteRealSubmoduleRetraction V is a constructed continuous linear retraction from ambient finite product to the actual image subspace, with finiteRealSubmoduleRetraction_left; compose with alignmentNativeArrayModelCoefficients. One must not assume the polynomial tuple lies in that image at arbitrary real inputs. Expand any resulting scalar linear functional on the finite product via coordinate inclusions, sum the already-constructed orbit-coordinate polynomials, and prove the uniform degree survives finite sums. This yields polynomial coordinates agreeing on admissible original integer arrays. Follow with actual tail/product and vertex substitutions; do not redo the now-proved orbit projection or rational transfer.

Native face counting is already proved for actual Delta and raw-supported samples. Connect model-array/coset translation and reading identities to cube tests after the joint polynomial work. Posterior and rough-step obligations remain below.

''' + s[end:]
p.write_text(s, encoding='utf-8')
print('Updated continuation checkpoint from verified counts.')
