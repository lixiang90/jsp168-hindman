import Hindman168.NativeRationalFirstLayerPolynomial
import Hindman168.NativeRationalCompactBracketParameters
import Hindman168.MvBinomialCoefficientModOne

/-! BOTH COMPLETE original raw coefficient tables for ANY actual lattice
character killing TRUE F_2, from its genuine compact first evaluation.
Normalization/integer transport is proved, not restricted to a named family. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_kills_two_original_first_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →L[ℝ] ℝ) (hf : L.layer 2 ≤ f.toLinearMap.ker)
    (hInt : ∀ g ∈ D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ)) :
    (((scalarUnitPolynomial (roughVectorMvProjection
      f.toLinearMap p)).coeff 1 : ℝ) : UnitAddCircle) =
      ((f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) : ℝ) : UnitAddCircle) := by
  have hkcomm := native_rational_kills_two_kills_commutator D L f.toLinearMap hf
  obtain ⟨z,hz⟩ := native_rational_compact_horizontal_nonconstant_coefficient D p f.toLinearMap hkcomm
    (fun g => hInt g g.property)
    (Finsupp.single () 1) (by simp)
  have he := native_rational_compact_kills_two_first_coefficient D L p hp f.toLinearMap hf
  rw [scalar_unit_polynomial_coefficient] at he
  rw [hz] at he
  change MvPolynomial.coeff (Finsupp.single () 1) (roughVectorMvProjection f.toLinearMap p)+(z : ℝ) =
    f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) at he
  have he' := congrArg (fun x : ℝ => (x : UnitAddCircle)) he
  rw [AddCircle.coe_add] at he'
  have hz0 : ((z : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z,by simp⟩
  rw [hz0,add_zero] at he'
  rw [scalar_unit_polynomial_coefficient]
  exact he'

theorem native_rational_kills_two_original_monomial_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →L[ℝ] ℝ) (hf : L.layer 2 ≤ f.toLinearMap.ker)
    (hInt : ∀ g ∈ D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ)) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : (N : ℝ)*‖((f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
        (roughVectorMvProjection f.toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ B := by
  intro J hJ
  have hsingle : Finsupp.equivFunOnFinite.symm J=Finsupp.single () (J ()) := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have hj : 0 < J () := by simpa using hJ
  have he : (N : ℝ)^(J ())*‖(((scalarUnitPolynomial (roughVectorMvProjection
      f.toLinearMap p)).coeff (J ()) : ℝ) : UnitAddCircle)‖ ≤ B := by
    by_cases h1 : J ()=1
    · rw [h1,pow_one,native_rational_kills_two_original_first_coefficient D L p hp f hf hInt]
      exact hsmall
    · rw [native_rational_kills_two_scalar_coefficient D L p hp _
        hf _ (by omega)]
      simpa only [AddCircle.coe_zero,norm_zero,mul_zero] using hB
  simpa only [Finset.univ_unique,Finset.sum_singleton,hsingle,scalar_unit_polynomial_coefficient] using he

theorem native_rational_kills_two_original_binomial_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (f : D.E →L[ℝ] ℝ) (hf : L.layer 2 ≤ f.toLinearMap.ker)
    (hInt : ∀ g ∈ D.Γ, ∃ z : ℤ, f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) = (z : ℝ)) (N : ℕ) (hN : 0 < N) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : (N : ℝ)*‖((f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
        (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
        (roughVectorMvProjection f.toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤
        (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B := by
  intro I hI
  by_cases hi : I ∈ mvBinomialBox Unit ℓ
  · have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := mv_binomial_coefficient_mod_one
      (roughVectorMvProjection f.toLinearMap p)
      ℓ 1 1 I hi hI (N : ℝ) B hn hB
      (fun J _ hJ => by simpa only [Nat.cast_one,one_mul] using
        native_rational_kills_two_original_monomial_bounds D L p hp f hf hInt N B hB hsmall J hJ)
    simpa only [Nat.cast_one,one_mul] using hb
  · have hil : ℓ < I () := by
      by_contra! h
      exact hi ((mv_binomial_box_mem ℓ I).mpr (fun u => by cases u; exact h))
    have hz : mvPolynomialBinomialCoefficient
        (roughVectorMvProjection f.toLinearMap p) ℓ I=0 := by
      unfold mvPolynomialBinomialCoefficient
      apply Finset.sum_eq_zero
      intro J hJ
      rw [mv_binomial_stirling_weight_zero_below I J ()
        (((mv_binomial_box_mem ℓ J).mp hJ ()).trans_lt hil),Nat.cast_zero,mul_zero]
    rw [hz,AddCircle.coe_zero,norm_zero,mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

end Hindman168
