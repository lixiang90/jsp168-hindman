import Hindman168.NativeTerminalRelativePairTranslation
import Hindman168.NativeNilmanifoldProbabilityTesting

/-! NONZERO ORIGINAL terminal pair has mean ZERO against GENUINE
relative canonical Haar, from ACTUAL first-coordinate terminal translation.
Original single-factor or whole-product zero mean is not substituted. -/

namespace Hindman168
open MeasureTheory
open scoped Manifold ContDiff
universe u

theorem native_terminal_relative_pair_nonzero_mean {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (d : ℕ) (hd : 0 < d) (hdeg : 2 ≤ s*d)
    (k : nativeOriginalTerminalIndex D d → ℤ) (hk : k ≠ 0) (g : D.G) :
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
    letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ,ℂ),
      (∫ q, nativeTerminalRelativePairObservable D d hd k g F q
        ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1)) = 0 := by
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).E := borel (nativeRelativeSquareData D d hd 1).E
  letI : MeasurableSpace (nativeRelativeSquareData D d hd 1).G := borel (nativeRelativeSquareData D d hd 1).G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro F
  obtain ⟨a,ha⟩ := unit_torus_nonzero_fourier_exists k hk
  obtain ⟨z,hz⟩ := native_original_terminal_torus_projection_surjective D d hd a
  let c := UnitAddTorus.mFourier k a
  let J := ∫ q, nativeTerminalRelativePairObservable D d hd k g F q
    ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1)
  have h : c*J = J := by
    calc
      _ = ∫ q, c * nativeTerminalRelativePairObservable D d hd k g F q
          ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1) := (integral_const_mul _ _).symm
      _ = ∫ q, nativeTerminalRelativePairObservable D d hd k g F
          (nativeRelativeFirstTerminalElement D d hd hdeg z • q)
          ∂nativeNilmanifoldQuotientProbability (nativeRelativeSquareData D d hd 1) := by
        apply integral_congr_ae
        filter_upwards with q
        have he := native_terminal_relative_pair_first_equivariant D d hd hdeg k g F z q
        rw [hz] at he
        exact he.symm
      _ = J := native_nilmanifold_probability_integral_translation (nativeRelativeSquareData D d hd 1)
        (nativeRelativeFirstTerminalElement D d hd hdeg z) (nativeTerminalRelativePairObservable D d hd k g F)
  have hz0 : (c-1)*J = 0 := by rw [sub_mul,one_mul,h,sub_self]
  exact (mul_eq_zero.mp hz0).resolve_left (sub_ne_zero.mpr ha)

end Hindman168
