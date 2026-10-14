import Hindman168.NativeRationalWeightedIntegerPair
import Hindman168.NativeRationalWeightedNormalizations
import Hindman168.RoughVectorCoefficientSubmodule
import Hindman168.RoughVectorSubmodulePolynomial

/-! The ACTUAL nonlinear part P(n)*P(1)^(-n) is a genuine coefficient
polynomial in the original F_2 model. Coefficient membership is recovered
from actual integer samples; no F_2 polynomial is assumed. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_nonlinear_group_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (n : ℤ) :
    nativeIntegerLogPolynomialSequence D p n *
      (nativeIntegerLogPolynomialSequence D p 1^n)⁻¹ ∈ nativeRationalFilteredGroupLayer D L 2 := by
  letI := native_rational_filtered_group_normal D L 2
  apply rough_filtered_integer_nonlinear_part_mem _ _
    (native_rational_weighted_integer_sequence_filtered D L hp)
  simp only [nativeIntegerLogPolynomialSequence,Int.cast_zero,h0]
  exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)

noncomputable def nativeRationalNonlinearGroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (n : ℤ) :
    nativeRationalFilteredGroupLayer D L 2 :=
  ⟨nativeIntegerLogPolynomialSequence D p n * (nativeIntegerLogPolynomialSequence D p 1^n)⁻¹,
    native_rational_nonlinear_group_mem D L p hp h0 n⟩

theorem native_rational_nonlinear_log_integer {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (p : RoughVectorMvPolynomial Unit D.E) (n : ℤ) :
    roughVectorMvEval (E := D.E)
      (nativeLinearStepPolynomial D p (nativeIntegerLogPolynomialSequence D p 1)) (fun _ => (n : ℝ)) =
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeIntegerLogPolynomialSequence D p n*(nativeIntegerLogPolynomialSequence D p 1^n)⁻¹) := by
  have he := congrArg (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G))
    (native_linear_step_integer_exponential D p (nativeIntegerLogPolynomialSequence D p 1) n)
  rw [nativeLieGlobalLogarithm_exponential] at he
  simpa only [nativeIntegerLogPolynomialSequence,zpow_neg] using he

theorem native_rational_nonlinear_coefficient_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (J : Unit →₀ ℕ) :
    roughVectorMvCoefficient (nativeLinearStepPolynomial D p
      (nativeIntegerLogPolynomialSequence D p 1)) J ∈ L.layer 2 := by
  apply rough_vector_coefficient_mem_of_nat_values
  intro x
  have hx : (fun j => (x j : ℝ)) = (fun _ : Unit => ((x () : ℤ) : ℝ)) := by
    funext j
    cases j
    simp only [Int.cast_natCast]
  rw [hx,native_rational_nonlinear_log_integer]
  exact (native_rational_filtered_group_logarithm_iff D L 2 _).mp
    (native_rational_nonlinear_group_mem D L p hp h0 (x ()))

noncomputable def nativeRationalNonlinearPolynomial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) : RoughVectorMvPolynomial Unit (L.layer 2) :=
  roughVectorMvSubmodulePolynomial (L.layer 2)
    (nativeLinearStepPolynomial D p (nativeIntegerLogPolynomialSequence D p 1))
    (native_rational_nonlinear_coefficient_mem D L p hp h0)

theorem native_rational_nonlinear_polynomial_eval {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (n : ℤ) :
    (roughVectorMvEval (nativeRationalNonlinearPolynomial D L p hp h0) (fun _ => (n : ℝ))).val =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeRationalNonlinearGroup D L p hp h0 n).val := by
  exact (rough_vector_submodule_polynomial_eval (L.layer 2)
    (nativeLinearStepPolynomial D p (nativeIntegerLogPolynomialSequence D p 1))
    (native_rational_nonlinear_coefficient_mem D L p hp h0) (fun _ => (n : ℝ))).trans
      (native_rational_nonlinear_log_integer D p n)

end Hindman168
