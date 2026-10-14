import Hindman168.NativeRationalFirstLayerPolynomial
import Hindman168.NativeRationalCompactBracketParameters
import Hindman168.MvBinomialCoefficientModOne

/-! The actual small k dot gamma alternative gives BOTH COMPLETE original
raw coefficient tables, not just a normalized linear coefficient. The k
extraction itself is not assumed solved by these reconstruction lemmas. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

theorem native_rational_first_layer_original_first_coefficient {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : NativeRationalFirstLayerIndex D L → ℤ) :
    (((scalarUnitPolynomial (roughVectorMvProjection
      (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p)).coeff 1 : ℝ) : UnitAddCircle) =
      ((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle) := by
  let f := nativeRationalFirstLayerIntegerCharacter D L k
  have hk2 := native_rational_first_layer_integer_character_kills_two D L k
  have hkcomm := native_rational_kills_two_kills_commutator D L f.toLinearMap hk2
  obtain ⟨z,hz⟩ := native_rational_compact_horizontal_nonconstant_coefficient D p f.toLinearMap hkcomm
    (fun g => native_rational_first_layer_integer_character_lattice D L k g g.property)
    (Finsupp.single () 1) (by simp)
  have he := native_rational_compact_kills_two_first_coefficient D L p hp f.toLinearMap hk2
  rw [scalar_unit_polynomial_coefficient] at he
  rw [hz] at he
  change MvPolynomial.coeff (Finsupp.single () 1) (roughVectorMvProjection f.toLinearMap p)+(z : ℝ) =
    f (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
      (nativeIntegerLogPolynomialSequence D (nativeRationalCompactNormalizedPolynomial D p) 1)) at he
  rw [native_rational_first_layer_integer_character_apply] at he
  have he' := congrArg (fun x : ℝ => (x : UnitAddCircle)) he
  rw [AddCircle.coe_add] at he'
  have hz0 : ((z : ℝ) : UnitAddCircle)=0 :=
    (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr ⟨z,by simp⟩
  rw [hz0,add_zero] at he'
  rw [scalar_unit_polynomial_coefficient]
  exact he'

theorem native_rational_first_layer_original_monomial_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (N : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : (N : ℝ)*‖((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((MvPolynomial.coeff (Finsupp.equivFunOnFinite.symm J)
        (roughVectorMvProjection (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p) : ℝ) : UnitAddCircle)‖ ≤ B := by
  intro J hJ
  have hsingle : Finsupp.equivFunOnFinite.symm J=Finsupp.single () (J ()) := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have hj : 0 < J () := by simpa using hJ
  have he : (N : ℝ)^(J ())*‖(((scalarUnitPolynomial (roughVectorMvProjection
      (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p)).coeff (J ()) : ℝ) : UnitAddCircle)‖ ≤ B := by
    by_cases h1 : J ()=1
    · rw [h1,pow_one,native_rational_first_layer_original_first_coefficient D L p hp k]
      exact hsmall
    · rw [native_rational_kills_two_scalar_coefficient D L p hp _
        (native_rational_first_layer_integer_character_kills_two D L k) _ (by omega)]
      simpa only [AddCircle.coe_zero,norm_zero,mul_zero] using hB
  simpa only [Finset.univ_unique,Finset.sum_singleton,hsingle,scalar_unit_polynomial_coefficient] using he

theorem native_rational_first_layer_original_binomial_bounds {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : NativeRationalLieFiltration D ℓ)
    (p : RoughVectorMvPolynomial Unit D.E) (hp : RoughVectorMvWeightedDegree L.layer p 0)
    (k : NativeRationalFirstLayerIndex D L → ℤ) (N : ℕ) (hN : 0 < N) (B : ℝ) (hB : 0 ≤ B)
    (hsmall : (N : ℝ)*‖((∑ i, (k i : ℝ)*nativeRationalCompactBracketFrequency D L p i : ℝ) : UnitAddCircle)‖ ≤ B) :
    ∀ J : Unit → ℕ, 0 < (∑ i, J i) →
      (N : ℝ)^(∑ i, J i)*‖((mvPolynomialBinomialCoefficient
        (roughVectorMvProjection (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p) ℓ J : ℝ) : UnitAddCircle)‖ ≤
        (mvBinomialCoefficientBudget Unit ℓ : ℝ)*B := by
  intro I hI
  by_cases hi : I ∈ mvBinomialBox Unit ℓ
  · have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hb := mv_binomial_coefficient_mod_one
      (roughVectorMvProjection (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p)
      ℓ 1 1 I hi hI (N : ℝ) B hn hB
      (fun J _ hJ => by simpa only [Nat.cast_one,one_mul] using
        native_rational_first_layer_original_monomial_bounds D L p hp k N B hB hsmall J hJ)
    simpa only [Nat.cast_one,one_mul] using hb
  · have hil : ℓ < I () := by
      by_contra! h
      exact hi ((mv_binomial_box_mem ℓ I).mpr (fun u => by cases u; exact h))
    have hz : mvPolynomialBinomialCoefficient
        (roughVectorMvProjection (nativeRationalFirstLayerIntegerCharacter D L k).toLinearMap p) ℓ I=0 := by
      unfold mvPolynomialBinomialCoefficient
      apply Finset.sum_eq_zero
      intro J hJ
      rw [mv_binomial_stirling_weight_zero_below I J ()
        (((mv_binomial_box_mem ℓ J).mp hJ ()).trans_lt hil),Nat.cast_zero,mul_zero]
    rw [hz,AddCircle.coe_zero,norm_zero,mul_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

end Hindman168
