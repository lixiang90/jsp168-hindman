import Hindman168.NativeLieRationalProductCurve
import Hindman168.RationalVectorPolynomialCoefficients

/-! A true finite rational-coefficient vector polynomial for the actual
original adjoint curve, padded by two genuinely zero terminal powers.
The padding permits coefficient-one extraction even in classes zero/one. -/

namespace Hindman168
open Finset
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieAdjointCurve_apply_rational_polynomial (v w : E) (t : ℝ) :
    (nativeLieAdjointCurve (I := I) (G := G) v t : E →L[ℝ] E) w =
      ∑ j ∈ range (Group.nilpotencyClass G), t ^ j •
        ((j.factorial : ℚ)⁻¹ • (nativeLieAdjointGenerator (I := I) (G := G) v ^ j) w) := by
  rw [nativeLieAdjointCurve_finite_formula_of_group_isNilpotent]
  simp only [_root_.sum_apply, smul_pow, smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hc : (((j.factorial : ℚ)⁻¹ : ℚ) : ℝ) = (j.factorial : ℝ)⁻¹ := by push_cast; rfl
  rw [smul_comm, ← hc, Rat.cast_smul_eq_qsmul]

 theorem nativeLieAdjointCurve_apply_padded_rational_polynomial (v w : E) (t : ℝ) :
    (nativeLieAdjointCurve (I := I) (G := G) v t : E →L[ℝ] E) w =
      ∑ j ∈ range (Group.nilpotencyClass G + 2), t ^ j •
        ((j.factorial : ℚ)⁻¹ • (nativeLieAdjointGenerator (I := I) (G := G) v ^ j) w) := by
  let c := Group.nilpotencyClass G
  let B : E →L[ℝ] E := nativeLieAdjointGenerator (I := I) (G := G) v
  have hc : B ^ c = 0 := nativeLieAdjointGenerator_pow_nilpotencyClass v
  have hc1 : B ^ (c + 1) = 0 := by rw [pow_succ, hc, zero_mul]
  rw [nativeLieAdjointCurve_apply_rational_polynomial]
  change (∑ j ∈ range c, t ^ j • ((j.factorial : ℚ)⁻¹ • (B ^ j) w)) =
    ∑ j ∈ range (c + 1 + 1), t ^ j • ((j.factorial : ℚ)⁻¹ • (B ^ j) w)
  rw [sum_range_succ, sum_range_succ, hc, hc1]
  simp only [zero_apply, smul_zero, add_zero]

 theorem nativeLieAdjointGenerator_mem_of_nat_curve_values
    (S : Submodule ℚ E) (v w : E)
    (h : ∀ n : ℕ, (nativeLieAdjointCurve (I := I) (G := G) v (n : ℝ) : E →L[ℝ] E) w ∈ S) :
    nativeLieAdjointGenerator (I := I) (G := G) v w ∈ S := by
  have hc : ((1 : ℕ).factorial : ℚ)⁻¹ •
      (nativeLieAdjointGenerator (I := I) (G := G) v ^ (1 : ℕ)) w ∈ S := by
    apply rationalVectorPolynomial_coeff_mem_of_real_nat_values S (k := Group.nilpotencyClass G + 2)
      (a := fun j => (j.factorial : ℚ)⁻¹ • (nativeLieAdjointGenerator (I := I) (G := G) v ^ j) w)
      _ (by omega)
    intro n
    rw [← nativeLieAdjointCurve_apply_padded_rational_polynomial]
    exact h n
  simpa only [Nat.factorial_one, Nat.cast_one, inv_one, one_smul, pow_one] using hc

end Hindman168
