import Hindman168.NativeRationalFullInverseInductionStep

/-! UNCONDITIONAL full native rational-filtration Unit inverse, by genuine
strong degree induction and strong natural nonlinearity induction on ALL
actual native data. Every original positive length, original nonzero/grid/
norm character and BOTH COMPLETE raw coefficient tables are retained.
This is not the multiparameter inverse or the final finite sums/products goal. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_rational_weighted_inverse_unit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) :
    NativeRationalWeightedInverseStatement D L Unit := by
  have hAll (degree : ℕ) : ∀ (step : ℕ) (D0 : NativeNilmanifoldData.{u} step)
      (L0 : NativeRationalLieFiltration D0 degree), NativeRationalWeightedInverseStatement D0 L0 Unit := by
    induction degree using Nat.strong_induction_on with
    | h degree ih =>
      intro step D0 L0
      by_cases h0 : degree=0
      · subst degree
        exact native_rational_weighted_inverse_degree_zero D0 L0 Unit
      by_cases h1 : degree=1
      · subst degree
        exact native_rational_weighted_inverse_degree_one D0 L0 Unit
      have hdeg : 2 ≤ degree := by omega
      have hNonlin : ∀ n : ℕ, ∀ (D1 : NativeNilmanifoldData.{u} step)
          (L1 : NativeRationalLieFiltration D1 degree), nativeRationalFiltrationNonlinearity D1 L1=n →
          NativeRationalWeightedInverseStatement D1 L1 Unit := by
        intro n
        induction n using Nat.strong_induction_on with
        | h n hn =>
          intro D1 L1 hMeasure
          apply native_rational_full_inverse_induction_step D1 L1 hdeg
          · exact ih (degree-1) (by omega) step (nativeRationalDegreeReducedData D1 L1)
              (nativeDegreeReducedRationalLieFiltration D1 L1)
          · exact ih (degree-1) (by omega) step (nativeRationalTerminalQuotientData D1 L1)
              (nativeTerminalRationalLieFiltration D1 L1)
          · intro D2 L2 hLess
            exact hn (nativeRationalFiltrationNonlinearity D2 L2) (hLess.trans_eq hMeasure) D2 L2 rfl
      exact hNonlin (nativeRationalFiltrationNonlinearity D0 L0) D0 L0 rfl
  exact hAll ℓ s D L

end Hindman168
