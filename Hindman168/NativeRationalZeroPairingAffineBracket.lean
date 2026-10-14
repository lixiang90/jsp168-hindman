import Hindman168.NativeRationalBracketFullAlternative
import Hindman168.UnitCircleDenseScaledAffineInverse

/-! Actual zero original pairing makes the SAME native bracket affine.
Applying the TRUE dense affine inverse supplies the missing paper second
binomial coefficient at original N^-2 and true P(1) at original N^-1. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

theorem native_rational_zero_pairing_bracket_affine {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ)
    (hzero : ∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (M : ℕ) (b : NativeRationalFirstLayerIndex D L → ℤ) (h : ℝ) :
    scalarFractionalBracket (nativeRationalCompactBracketBeta D L p χ M b)
      (nativeRationalCompactBracketAlpha D L p hp χ M) (nativeRationalCompactBracketCoefficient D L p χ M)
      (nativeRationalCompactBracketFrequency D L p) h =
        (M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1+
          (M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2*h := by
  have hz (i : NativeRationalFirstLayerIndex D L) : nativeRationalCompactBracketCoefficient D L p χ M i=0 := by
    dsimp only [nativeRationalCompactBracketCoefficient,nativeRationalCommutatorFirstLayerCoefficient]
    rw [hzero,zero_div,mul_zero]
  simp only [scalarFractionalBracket,nativeRationalCompactBracketBeta,nativeRationalCompactBracketAlpha,
    hz,zero_mul,Finset.sum_const_zero,add_zero]

theorem native_rational_zero_pairing_affine_inverse {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (δ B : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hB : 0 ≤ B) :
    ∃ A T : ℕ, 0 < A ∧ 0 < T ∧ ∀ (p : RoughVectorMvPolynomial Unit D.E)
      (hp : RoughVectorMvWeightedDegree L.layer p 0)
      (χ : (nativeRationalRelativeData D L 1).E →L[ℝ] ℝ),
      (∀ g h : D.G, nativeRationalRelativeCommutatorValue D L χ g h=0) →
      ∀ (M : ℕ) (b : NativeRationalFirstLayerIndex D L → ℤ) (N : ℕ), T ≤ N →
      ∀ V : Finset ℕ, δ*(N : ℝ) ≤ V.card →
      (∀ h ∈ V, h < N ∧ (N : ℝ)*‖((scalarFractionalBracket
        (nativeRationalCompactBracketBeta D L p χ M b) (nativeRationalCompactBracketAlpha D L p hp χ M)
        (nativeRationalCompactBracketCoefficient D L p χ M) (nativeRationalCompactBracketFrequency D L p)
        (h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B) →
      ∃ r : ℕ, 0 < r ∧ r ≤ A ∧
        (N : ℝ)^2*‖(((r*M : ℕ) : ℝ)*scalarPolynomialBinomialCoefficient
          (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2 : UnitAddCircle)‖ ≤ (A : ℝ)*B ∧
        (N : ℝ)*‖(((r*M : ℕ) : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1 : UnitAddCircle)‖ ≤ (A : ℝ)*B := by
  obtain ⟨A,T,hA,hT,hinv⟩ := unit_circle_dense_scaled_affine_inverse δ B hδ hδ1 hB
  refine ⟨A,T,hA,hT,?_⟩
  intro p hp χ hzero M b N hTN V hdense hUseful
  have hsub : V ⊆ (Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1+
        ((M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2)*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B) := by
    intro h hh
    obtain ⟨hlt,hsmall⟩ := hUseful h hh
    rw [native_rational_zero_pairing_bracket_affine D L χ hzero p hp M b] at hsmall
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt,hsmall⟩
  have hcount := hdense.trans (show _ ≤ (((Finset.range N).filter (fun h : ℕ =>
      (N : ℝ)*‖(((M : ℝ)*(nativeRationalCompactDiagonalScalar D L p χ).eval 1+
        ((M : ℝ)*scalarPolynomialBinomialCoefficient (nativeRationalCompactNonlinearScalar D L p hp χ) ℓ 2)*(h : ℝ) : ℝ) : UnitAddCircle)‖ ≤ B)).card : ℝ) by exact_mod_cast Finset.card_le_card hsub)
  obtain ⟨r,hr,hrA,hslope,hoffset⟩ := hinv _ _ N hTN hcount
  refine ⟨r,hr,hrA,?_,?_⟩
  · simpa only [Nat.cast_mul,mul_assoc] using hslope
  · simpa only [Nat.cast_mul,mul_assoc] using hoffset

end Hindman168
