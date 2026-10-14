import Hindman168.FiniteComplexMean
import Mathlib.Data.Complex.BigOperators
import Mathlib.Topology.ContinuousMap.Basic

namespace Hindman168
open scoped BigOperators Classical
open NNReal

/-- Rotate a complex observable by a unit phase and take its real part. -/
noncomputable def phaseRealObservable {X : Type*} [TopologicalSpace X]
    (η : ℂ) (obs : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun x => (η * obs x).re,
    Complex.continuous_re.comp (continuous_const.mul obs.continuous)⟩

theorem phaseRealObservable_abs_le {X : Type*} [TopologicalSpace X]
    (η : ℂ) (hη : ‖η‖ = 1) (obs : C(X, ℂ)) (B : ℝ)
    (hB : ∀ x, ‖obs x‖ ≤ B) (x : X) : |phaseRealObservable η obs x| ≤ B := by
  change |(η * obs x).re| ≤ B
  exact (Complex.abs_re_le_norm _).trans (by rw [norm_mul, hη, one_mul]; exact hB x)

theorem phaseRealObservable_lipschitz {X : Type*} [PseudoMetricSpace X]
    (η : ℂ) (hη : ‖η‖ = 1) (obs : C(X, ℂ)) (L : ℝ≥0)
    (hL : LipschitzWith L obs) : LipschitzWith L (phaseRealObservable η obs) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    _ = |(η * (obs x - obs y)).re| := by
      rw [dist_eq_norm, Real.norm_eq_abs]
      change |(η * obs x).re - (η * obs y).re| = _
      rw [← Complex.sub_re, ← mul_sub]
    _ ≤ ‖η * (obs x - obs y)‖ := Complex.abs_re_le_norm _
    _ = ‖obs x - obs y‖ := by rw [norm_mul, hη, one_mul]
    _ ≤ (L : ℝ) * dist x y := by simpa only [dist_eq_norm] using hL.dist_le_mul x y

theorem finiteComplexMean_re {A : Type*} [Fintype A] (f : A → ℂ) :
    (finiteComplexMean f).re = finiteHaarMean (fun a => (f a).re) := by
  simp only [finiteComplexMean, finiteHaarMean, Complex.div_natCast_re, Complex.re_sum]

theorem finiteComplexMean_const_mul {A : Type*} [Fintype A] (c : ℂ) (f : A → ℂ) :
    finiteComplexMean (fun a => c * f a) = c * finiteComplexMean f := by
  unfold finiteComplexMean
  rw [← Finset.mul_sum]
  ring

theorem finite_real_phase_correlation {A : Type*} [Fintype A]
    (v : A → ℝ) (ψ : A → ℂ) (η : ℂ) :
    finiteHaarMean (fun a => v a * (η * ψ a).re) =
      (η * finiteComplexMean (fun a => (v a : ℂ) * ψ a)).re := by
  rw [← finiteComplexMean_const_mul, finiteComplexMean_re]
  congr 1
  funext a
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero]
  ring

/-- The selected unit phase converts the exact complex correlation modulus
to a nonnegative real correlation without reducing its size. -/
theorem finite_real_correlation_phase_choice {A : Type*} [Fintype A]
    (v : A → ℝ) (ψ : A → ℂ) :
    ∃ η : ℂ, ‖η‖ = 1 ∧ finiteHaarMean (fun a => v a * (η * ψ a).re) =
      ‖finiteComplexMean (fun a => (v a : ℂ) * ψ a)‖ := by
  obtain ⟨η, hη, he⟩ := Complex.exists_norm_eq_mul_self
    (finiteComplexMean (fun a => (v a : ℂ) * ψ a))
  refine ⟨η, hη, ?_⟩
  rw [finite_real_phase_correlation]
  have hr := congrArg Complex.re he
  simpa only [Complex.ofReal_re] using hr.symm

end Hindman168
