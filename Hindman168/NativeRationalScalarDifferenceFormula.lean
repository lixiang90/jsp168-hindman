import Hindman168.NativeRationalNonlinearPolynomial
import Hindman168.NativeRationalRelativeGroupDecomposition
import Hindman168.NativeRationalCommutatorCharacter
import Hindman168.NativeRationalWeightedRelativePolynomial
import Hindman168.SubgroupCharacterNormalizedPair

/-! The ACTUAL original relative scalar on integer samples is precisely
P(n)+Q(n+h)-Q(n)+sigma(h)*n. Q is constructed in the actual original F_2;
the real commutator term is derived from actual group characters. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeRationalNonlinearScalar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) : MvPolynomial Unit ℝ :=
  roughVectorMvProjection (nativeRationalRelativeDifferenceCharacter D L χ).toLinearMap
    (nativeRationalNonlinearPolynomial D L p hp h0)

theorem native_rational_nonlinear_scalar_integer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ) (n : ℤ) :
    MvPolynomial.eval (fun _ => (n : ℝ)) (nativeRationalNonlinearScalar D L p hp h0 χ) =
      nativeRationalRelativeDifferenceLogCharacter D L χ (nativeRationalNonlinearGroup D L p hp h0 n) := by
  rw [nativeRationalNonlinearScalar,roughVectorMvProjection_eval,
    native_rational_relative_difference_log_character_apply]
  change nativeRationalRelativeDifferenceCharacter D L χ
    (roughVectorMvEval (nativeRationalNonlinearPolynomial D L p hp h0) (fun _ => (n : ℝ))) =
    nativeRationalRelativeDifferenceCharacter D L χ _
  apply congrArg (nativeRationalRelativeDifferenceCharacter D L χ)
  apply Subtype.ext
  exact native_rational_nonlinear_polynomial_eval D L p hp h0 n

theorem native_rational_relative_scalar_difference_formula {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (h0 : roughVectorMvEval (E := D.E) p (fun _ => 0) = 0)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hχ : nativeLieLowerCentralModel (I := (nativeRationalRelativeData D L 1).I)
      (G := (nativeRationalRelativeData D L 1).G) 1 ≤ χ.toLinearMap.ker)
    (t : D.G) (h n : ℤ) :
    MvPolynomial.eval (fun _ => (n : ℝ)) (roughVectorMvProjection χ.toLinearMap
      (nativeRationalWeightedRelativePolynomial D L p hp h0 t h)) =
      MvPolynomial.eval (fun _ => (n : ℝ))
        (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p) +
      MvPolynomial.eval (fun _ => ((n+h : ℤ) : ℝ)) (nativeRationalNonlinearScalar D L p hp h0 χ) -
      MvPolynomial.eval (fun _ => (n : ℝ)) (nativeRationalNonlinearScalar D L p hp h0 χ) +
      (n : ℝ)*nativeRationalRelativeCommutatorValue D L χ (nativeIntegerLogPolynomialSequence D p 1) t := by
  letI := native_rational_filtered_group_normal D L 2
  let g := nativeRationalWeightedIntegerPair D L p hp h0 t h n
  have hEval : MvPolynomial.eval (fun _ => (n : ℝ)) (roughVectorMvProjection χ.toLinearMap
      (nativeRationalWeightedRelativePolynomial D L p hp h0 t h)) =
      nativeLieLogarithmCharacter (I := (nativeRationalRelativeData D L 1).I)
        (G := (nativeRationalRelativeData D L 1).G) χ.toLinearMap g := by
    rw [roughVectorMvProjection_eval]
    dsimp only [g]
    rw [← native_rational_weighted_relative_polynomial_exponential,
      nativeLieLogarithmCharacter_exponential]
  rw [hEval,native_rational_relative_group_character_decomposition D L χ hχ g]
  have hdiag : nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap g.val.2 =
      MvPolynomial.eval (fun _ => (n : ℝ))
        (roughVectorMvProjection (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap p) := by
    change nativeLieLogarithmCharacter (I := D.I) (G := D.G)
      (nativeRationalRelativeDiagonalCharacter D L χ).toLinearMap
        (roughNormalizedIntegerPair (nativeIntegerLogPolynomialSequence D p) t h n).2 = _
    rw [rough_normalized_integer_pair_second,nativeIntegerLogPolynomialSequence,
      nativeLieLogarithmCharacter_exponential,roughVectorMvProjection_eval]
  have hdiff := subgroup_real_normalized_pair_difference _
    (native_rational_original_commutator_mem_two D L) (nativeRationalRelativeDifferenceLogCharacter D L χ)
    (native_rational_relative_difference_log_character_mul D L χ hχ)
    (native_rational_difference_character_conjugation D L χ hχ)
    (nativeIntegerLogPolynomialSequence D p) (nativeRationalNonlinearGroup D L p hp h0)
    (fun _ => rfl) t h n (nativeRationalRelativeGroupDifference D L g) rfl
  rw [hdiag,hdiff,← native_rational_nonlinear_scalar_integer,← native_rational_nonlinear_scalar_integer]
  dsimp only [nativeRationalRelativeCommutatorValue]
  ring

end Hindman168
