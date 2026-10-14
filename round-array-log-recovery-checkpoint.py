from pathlib import Path
import json

v = json.loads(Path('round-array-log-recovery-checks.json').read_text())
assert not v['full_target_proved']
p = Path('CONTINUATION.txt')
s = p.read_text(encoding='utf-8').replace('Current batch: round-multivariate-orbit-log',
    'Earlier batch: round-multivariate-orbit-log')
start = s.index('Immediate next algebra work:')
end = s.index('The uniform rough-step theorem', start)
s = s[:start] + f'''Current batch: round-array-log-recovery, verified 2026-10-11. Four modules, {v['new_theorems']} theorems, {v['new_definitions']} definitions; full build ({v['build_jobs']} jobs), {v['selected_axiom_reports']} selected transitive axiom reports, {v['project_modules']} project modules. Retained sources and axiom sets are unchanged, standard axioms only, all six pinned paper sections match their Git objects. This is author-side verification, not independent kernel replay.
- AlignmentNativeCoefficientLog defines coefficient logarithm by alignmentNativeArrayModelCoefficients composed with the inverse actual array exponential homeomorphism. Evaluation at EVERY integer slot equals original nativeLieGlobalLogarithm of the group value. alignmentNativeSelectedEvaluation is the real linear map to the fixed selected tuple, proved injective from the native embedding. alignmentNativeCoefficientRecovery is its LinearMap.leftInverse, defined globally on the ambient tuple, with exact left-inverse and actual-array-log recovery theorems. No arbitrary-input image membership is needed. hu is explicitly included in injectivity and left-inverse proofs. Native product coordinate rewrites need direct equality composition because rw's instances transparency cannot always unfold GroupLieAlgebra.
- NativeFiniteOrbitLogProjection sums the previously constructed multivariate orbit-log projections with linear coordinate functionals ell.comp(LinearMap.single ... j). Exact sum of inclusions recovers the finite tuple functional. Degree <=(s*s+1)^(s+1)*d does not grow with selected-point count.
- AlignmentNativeArrayLogPolynomial composes that construction with fixed coefficient recovery. It represents every real linear coefficient-log coordinate for actual arrays having the stated selected orbit values, with exact evaluation and the same degree bound.
- AlignmentNativeModelLogPolynomial specializes to the original alignmentNativeModelArray g b k Delta. It builds selected exponent polynomials P+sum_e C(u_j(e))*Q_e and proves their degree <=d if P and all Q_e have degree<=d. Its array-log polynomial evaluates exactly to ell(coefficientLog(modelArray)) whenever P,Q evaluate to the integer k,Delta. This uses actual model-array membership, not a postulated array existence.

Review: recovery is now proved and globally extended by a constructed linear left inverse. The group-array coefficient logarithm is explicitly the inverse of the existing actual array exponential chart followed by the proved coefficient linear equivalence; its pointwise original-log identity is proved. No degree or coefficient bound is assumed on the desired logarithm. Instantiation with the original frozen data and separate tail variables is still required for the complete paper statement.

Immediate next algebra work: build the original base/increment parameter polynomials in vertex X and tail product t, using exposed scalar formula C(Y+(r-rv)/M)+X+(s/M)*t and Q_e=(q_e-t*rho_e)/M with own-target filter. They are affine in (X,t) before substituting tail products. Freeze them using existing exposed data equalities, and prove they evaluate to actual original base integer quotient and filtered canonical Delta. Alternatively specialize alignmentExposedCubePolynomial at each fixed selected integer array coordinate to obtain P_j in X,t directly and invoke AlignmentNativeArrayLogPolynomial. The exact original array quotient formula from AlignmentCubeArrayExponent / AlignmentCanonicalCubePolynomial and alignmentPairProgression_exact must discharge all integrality and original-model identity premises. Then substitute X=x0+sum omega_j*x_j and t=product_l t_l using MvPolynomial.bind1, proving degree bounded by fixed cube/tail dimensions times the established orbit bound. Unknown cell origin stays in X, not coefficients. Do not redo recovery or generic model-array log polynomiality. Native face counting and posterior/rough-step obligations remain below.

''' + s[end:]
p.write_text(s, encoding='utf-8')
print('Updated continuation checkpoint from verified counts.')
