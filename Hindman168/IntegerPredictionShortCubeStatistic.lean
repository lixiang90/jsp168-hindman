import Hindman168.MasterCommonCyclicShortCube

namespace Hindman168
open scoped BigOperators Classical

/-- The actual harmonic short-increment cube, with its original polynomial
step and quotient-dependent length. No cyclic cell statistic replaces it. -/
noncomputable def integerPredictionShortCubeStatistic {n : ℕ}
    (w M R X d J : ℕ) (pol : MvPolynomial (Fin n) ℤ) (f : ℤ → ℝ) (x : Fin n → ℕ) : ℝ :=
  let P := (predictionCubeModulus w M pol x).natAbs
  let b := R / P
  ∑ y ∈ Finset.Ico (X : ℤ) (X ^ 2 : ℕ), integerMass X (primorial w) y *
    finiteHaarMean (fun v₀ : Fin d → Fin (b / J) =>
      finiteHaarMean (fun v₁ : Fin d → Fin (b / J) =>
        ∏ ω : Finset (Fin d), f (y + (P : ℤ) *
          ∑ j ∈ ω, (((v₁ j).val : ℤ) - (v₀ j).val))))

end Hindman168
