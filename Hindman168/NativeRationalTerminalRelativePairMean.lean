import Hindman168.NativeRationalTerminalRelativePairTranslation
import Hindman168.NativeNilmanifoldProbabilityTesting

/-! NONZERO ORIGINAL terminal pair has mean ZERO against GENUINE
relative canonical Haar, from ACTUAL first-coordinate terminal translation.
Original single-factor or whole-product zero mean is not substituted. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_rational_terminal_relative_pair_nonzero_mean {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ) (hdeg : 2 ≤ ℓ)
    (k : nativeRationalTerminalIndex D L → ℤ) (hk : k ≠ 0) (g : D.G) :
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
    letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeRationalTerminalRelativePairObservable D L k g F q
        ∂nativeNilmanifoldQuotientProbability (nativeRationalRelativeData D L 1)) = 0 := by
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).E := borel (nativeRationalRelativeData D L 1).E
  letI : MeasurableSpace (nativeRationalRelativeData D L 1).G := borel (nativeRationalRelativeData D L 1).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  obtain ⟨a,ha⟩ := unit_torus_nonzero_fourier_exists k hk
  obtain ⟨z,hz⟩ := native_rational_terminal_torus_projection_surjective D L a
  let c := UnitAddTorus.mFourier k a
  let J := ∫ q, nativeRationalTerminalRelativePairObservable D L k g F q
    ∂nativeNilmanifoldQuotientProbability (nativeRationalRelativeData D L 1)
  have h : c*J = J := by
    calc
      _ = ∫ q, c * nativeRationalTerminalRelativePairObservable D L k g F q
          ∂nativeNilmanifoldQuotientProbability (nativeRationalRelativeData D L 1) := (integral_const_mul _ _).symm
      _ = ∫ q, nativeRationalTerminalRelativePairObservable D L k g F
          (nativeRationalRelativeFirstTerminalElement D L hdeg z • q)
          ∂nativeNilmanifoldQuotientProbability (nativeRationalRelativeData D L 1) := by
        apply integral_congr_ae
        filter_upwards with q
        have he := native_rational_terminal_relative_pair_first_equivariant D L hdeg k g F z q
        rw [hz] at he
        exact he.symm
      _ = J := native_nilmanifold_probability_integral_translation (nativeRationalRelativeData D L 1)
        (nativeRationalRelativeFirstTerminalElement D L hdeg z) (nativeRationalTerminalRelativePairObservable D L k g F)
  have hz0 : (c-1)*J = 0 := by rw [sub_mul,one_mul,h,sub_self]
  exact (mul_eq_zero.mp hz0).resolve_left (sub_ne_zero.mpr ha)

end Hindman168
