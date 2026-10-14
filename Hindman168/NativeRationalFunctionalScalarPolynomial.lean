import Hindman168.NativeRationalWeightedOperations
import Hindman168.RoughVectorCoefficientSubmodule
import Hindman168.NativeLieLogarithmCharacter

/-! Actual horizontal scalar projection of the TRUE native product, and
actual degree bounds from a highest killed filtration layer. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_functional_scalar_degree {s ℓ : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial σ D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (F : D.E →L[ℝ] ℝ) (j : ℕ) (hF : L.layer (j+1) ≤ F.toLinearMap.ker) :
    (roughVectorMvProjection F.toLinearMap p).totalDegree ≤ j := by
  unfold MvPolynomial.totalDegree
  apply Finset.sup_le
  intro J hJ
  by_contra! hhigh
  have hm := rough_vector_weighted_coefficient L.layer L.antitone hp J
  rw [Nat.add_zero] at hm
  have hz := hF (L.antitone (Nat.succ_le_of_lt hhigh) hm)
  change F (roughVectorMvCoefficient p J)=0 at hz
  have he := rough_vector_coefficient_projection F.toLinearMap p J
  exact (MvPolynomial.mem_support_iff.mp hJ) (he.symm.trans hz)

theorem native_rational_product_horizontal_projection {s : ℕ} {σ : Type*}
    (D : NativeNilmanifoldData.{u} s) (F : D.E →L[ℝ] ℝ)
    (hF : nativeLieLowerCentralModel (I := D.I) (G := D.G) 1 ≤ F.toLinearMap.ker)
    (p q : RoughVectorMvPolynomial σ D.E) :
    roughVectorMvProjection F.toLinearMap (roughNativeProductMvPolynomial (I := D.I) (G := D.G) p q) =
      roughVectorMvProjection F.toLinearMap p+roughVectorMvProjection F.toLinearMap q := by
  apply MvPolynomial.funext
  intro x
  rw [roughVectorMvProjection_eval,roughNativeProductMvPolynomial_eval,MvPolynomial.eval_add,
    roughVectorMvProjection_eval,roughVectorMvProjection_eval]
  have he := nativeLieLogarithmCharacter_mul (E := D.E) (I := D.I) (G := D.G) F.toLinearMap hF
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) p x))
    (nativeLieExponential (E := D.E) (I := D.I) (G := D.G) (roughVectorMvEval (E := D.E) q x))
  simp only [nativeLieLogarithmCharacter_exponential (E := D.E) (I := D.I) (G := D.G)] at he
  exact he

noncomputable def unitMvNonlinearPart (P : MvPolynomial Unit ℝ) : MvPolynomial Unit ℝ :=
  P-MvPolynomial.C (P.coeff 0)-MvPolynomial.C (P.coeff (Finsupp.single () 1))*MvPolynomial.X ()

theorem unit_mv_linear_part_degree (P : MvPolynomial Unit ℝ) :
    (MvPolynomial.C (P.coeff 0)+MvPolynomial.C (P.coeff (Finsupp.single () 1))*MvPolynomial.X ()).totalDegree ≤ 1 := by
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · rw [MvPolynomial.totalDegree_C]
    omega
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X,zero_add] using (le_rfl : 1 ≤ 1))

theorem unit_mv_nonlinear_part_degree (P : MvPolynomial Unit ℝ) (j : ℕ) (hj : 1 ≤ j)
    (hP : P.totalDegree ≤ j) : (unitMvNonlinearPart P).totalDegree ≤ j := by
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · exact (MvPolynomial.totalDegree_sub_C_le _ _).trans hP
  · exact (MvPolynomial.totalDegree_mul _ _).trans (by
      simpa only [MvPolynomial.totalDegree_C,MvPolynomial.totalDegree_X,zero_add] using hj)

end Hindman168
