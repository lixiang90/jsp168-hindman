/-
Copyright OpenAI contributors. Licensed under Apache-2.0; see dependencies/openai-finite-szemeredi/LICENSE.
Original source: openai/math commit adc7f1241b42e322a6451854ab7e4b4c146bf78a.
Modified for Lean 4.32.2 / mathlib 905b958 compatibility.
Changes: dite_eq_right -> dif_neg (2)
No mathematical statements or assumptions changed.
-/
import OAI.Combinatorics.Progressions.Estimates.ComparisonAmbient

namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonCoefficient_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonCoefficient π p a) =
      coefficients p.val a := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, hp]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_first]

theorem realComparisonCoefficient_second (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonCoefficient π p a)) =
      (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p.val a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, map_zero, hp, map_zero]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_second]

end Erdos3.MultidegreeLieFiltration

end

end OAI
