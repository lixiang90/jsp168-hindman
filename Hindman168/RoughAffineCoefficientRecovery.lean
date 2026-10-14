import Hindman168.RoughAffineCommonMultiplier

/-! FULL original-scale monomial coefficient recovery from the TRUE affine
child, using a common natural multiplier, retained length and signed integer
untranslation. The result covers every positive multiindex, including above
the degree. No unproved inverse or real smallness of circle coefficients. -/
namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem rough_affine_coefficient_recovery {κ : Type*} [Fintype κ]
    (p : MvPolynomial κ ℝ) (d P N T : ℕ) (b : κ → ℤ)
    (τ C A : ℝ) (hp : p.totalDegree ≤ d) (hP : 0 < P) (hN : 0 < N)
    (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hlen : τ*(N : ℝ) ≤ T) (hb : ∀ i, |(b i : ℝ)| ≤ C*(N : ℝ))
    (hChild : ∀ I : κ → ℕ, 0 < (∑ i, I i) →
      (T : ℝ)^(∑ i, I i)*‖((coeff (Finsupp.equivFunOnFinite.symm I)
        (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => (P : ℝ)) p) : ℝ) : UnitAddCircle)‖ ≤ A)
    (I : κ → ℕ) (hI : 0 < ∑ i, I i) :
    (N : ℝ)^(∑ i, I i)*‖((((P^d : ℕ) : ℝ)*coeff (Finsupp.equivFunOnFinite.symm I) p : ℝ) : UnitAddCircle)‖ ≤
      (((roughSpatialDegreeIndices κ d).card : ℝ)*(2 : ℝ)^d*(max 1 C)^d)*
        (((P^d : ℕ) : ℝ)*A*(τ⁻¹)^d) := by
  let r := MvPolynomial.C ((P^d : ℕ) : ℝ)*p
  let B := ((P^d : ℕ) : ℝ)*A*(τ⁻¹)^d
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast hN
  have hr : r.totalDegree ≤ d := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using hp)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hTranslated (J : κ → ℕ) (hJ : 0 < ∑ i, J i) :
      (N : ℝ)^(∑ i, J i)*‖((coeff (Finsupp.equivFunOnFinite.symm J)
        (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1) r) : ℝ) : UnitAddCircle)‖ ≤ B := by
    by_cases hjd : (∑ i, J i) ≤ d
    · have hScale := finite_coefficient_scale_transfer N T τ A
        ‖((coeff (Finsupp.equivFunOnFinite.symm J)
          (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => (P : ℝ)) p) : ℝ) : UnitAddCircle)‖
        d (∑ i, J i) hτ hτ1 hA (norm_nonneg _) hlen hjd (hChild J hJ)
      have hEq : coeff (Finsupp.equivFunOnFinite.symm J)
          (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1) r) =
          ((P^(d-∑ i, J i) : ℕ) : ℝ)*coeff (Finsupp.equivFunOnFinite.symm J)
            (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => (P : ℝ)) p) := by
        dsimp only [r]
        rw [map_mul]
        have hConst : roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1)
            (MvPolynomial.C ((P^d : ℕ) : ℝ)) = MvPolynomial.C ((P^d : ℕ) : ℝ) := eval₂Hom_C _ _ _
        rw [hConst,coeff_C_mul]
        exact rough_affine_common_multiplier_coefficient p (fun i => (b i : ℝ)) P d J hjd
      rw [hEq]
      have hPow : P^(d-∑ i, J i) ≤ P^d := Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _)
      calc
        _ ≤ (N : ℝ)^(∑ i, J i)*(((P^(d-∑ i, J i) : ℕ) : ℝ)*
            ‖((coeff (Finsupp.equivFunOnFinite.symm J)
              (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => (P : ℝ)) p) : ℝ) : UnitAddCircle)‖) :=
          mul_le_mul_of_nonneg_left (mod_one_natural_multiplier_norm_le _ _) (by positivity)
        _ ≤ ((P^(d-∑ i, J i) : ℕ) : ℝ)*(A*(τ⁻¹)^d) := by
          calc
            _ = ((P^(d-∑ i, J i) : ℕ) : ℝ)*((N : ℝ)^(∑ i, J i)*_) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hScale (by positivity)
        _ ≤ B := by
          dsimp only [B]
          have hPowR : ((P^(d-∑ i, J i) : ℕ) : ℝ) ≤ ((P^d : ℕ) : ℝ) := by exact_mod_cast hPow
          calc
            _ ≤ ((P^d : ℕ) : ℝ)*(A*(τ⁻¹)^d) := mul_le_mul_of_nonneg_right hPowR (by positivity)
            _ = _ := by ring
    · have hZero : coeff (Finsupp.equivFunOnFinite.symm J)
          (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1) r) = 0 := by
        apply coeff_eq_zero_of_totalDegree_lt
        change (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1) r).totalDegree <
          (Finsupp.equivFunOnFinite.symm J).sum (fun _ e => e)
        have hs : (Finsupp.equivFunOnFinite.symm J).sum (fun _ e => e)=∑ i, J i := by
          rw [Finsupp.sum_fintype _ _ (fun _ => rfl),Finsupp.coe_equivFunOnFinite_symm]
        rw [hs]
        exact ((roughMvAffineSubstitution_degree _ _ _).trans hr).trans_lt (Nat.lt_of_not_ge hjd)
      rw [hZero,AddCircle.coe_zero,norm_zero,mul_zero]
      exact hB
  have hTranslated' (J : κ → ℕ) (hJ : 0 < ∑ i, J i) :
      ‖((coeff (Finsupp.equivFunOnFinite.symm J)
        (roughMvAffineSubstitution (fun i => (b i : ℝ)) (fun _ => 1) r) : ℝ) : UnitAddCircle)‖ ≤
        B*(N : ℝ)⁻¹^(∑ i, J i) := by
    have h := hTranslated J hJ
    rw [inv_pow,← div_eq_mul_inv]
    exact (le_div_iff₀ (pow_pos hN0 _)).mpr (by simpa only [mul_comm] using h)
  have h := rough_box_character_untranslate r d hr b (N : ℝ) C B hN0 hC hB hb hTranslated' I hI
  rw [inv_pow,← div_eq_mul_inv] at h
  have hFinal := (le_div_iff₀ (pow_pos hN0 _)).mp h
  dsimp only [r,B] at hFinal
  rw [coeff_C_mul] at hFinal
  simpa only [mul_comm] using hFinal

end Hindman168
