import Hindman168.NativeRationalWeightedOperations
import Hindman168.NativeRationalRelativeLieFiltration
import Hindman168.NativeNormalizedIntegerPair

/-! The ACTUAL normalized original pair lies in the ACTUAL relative native
group for ANY true weighted univariate polynomial starting at zero. -/

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_weighted_integer_sequence_filtered {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    {p : RoughVectorMvPolynomial Unit D.E} (hp : RoughVectorMvWeightedDegree F.layer p 0) :
    RoughFilteredPolynomial (nativeRationalFilteredGroupLayer D F) (nativeIntegerLogPolynomialSequence D p) := by
  let c : ℤ →+ (Unit → ℝ) := {
    toFun := fun n _ => (n : ℝ)
    map_zero' := by funext j; exact Int.cast_zero
    map_add' := by intro n m; funext j; exact Int.cast_add _ _ }
  exact rough_filtered_polynomial_precompose _ _ (native_rational_weighted_real_polynomial_filtered D F hp) c

theorem native_rational_weighted_integer_pair_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h n : ℤ) :
    roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) t h n ∈ nativeRationalRelativeGroupLayer D F 1 := by
  letI := native_rational_filtered_group_normal D F 2
  have hz : nativeIntegerLogPolynomialSequence D p 0 = 1 := by
    simp only [nativeIntegerLogPolynomialSequence,Int.cast_zero]
    rw [h0]
    exact nativeLieExponential_zero (E := D.E) (I := D.I) (G := D.G)
  exact rough_normalized_integer_pair_mem _ (native_rational_filtered_group_conditions D F)
    (native_rational_filtered_group_one D F) _ (native_rational_weighted_integer_sequence_filtered D F hp) hz t h n

noncomputable def nativeRationalWeightedIntegerPair {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h n : ℤ) :
    (nativeRationalRelativeData D F 1).G :=
  ⟨roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) t h n,
    native_rational_weighted_integer_pair_mem D F p hp h0 t h n⟩

theorem native_rational_weighted_integer_pair_inclusion {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree F.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0) (t : D.G) (h n : ℤ) :
    nativeRationalRelativeGroupInclusion D F 1 (nativeRationalWeightedIntegerPair D F p hp h0 t h n) =
      roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) t h n := rfl

end Hindman168
