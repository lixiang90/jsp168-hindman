import Hindman168.RoughAffineBinomialCoefficient

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

def roughSignedBinomialWeight {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (b : κ → ℤ) : ℤ := ∏ j, ((J j).choose (I j) : ℤ)*b j^(J j-I j)

theorem roughSignedBinomialWeight_eq_zero {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (b : κ → ℤ) (h : ¬ ∀ j, I j ≤ J j) :
    roughSignedBinomialWeight I J b = 0 := by
  push Not at h
  obtain ⟨j, hj⟩ := h
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]

theorem roughSignedBinomialWeight_real {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (b : κ → ℤ) :
    (roughSignedBinomialWeight I J b : ℝ) =
      roughAffinePowerCoefficient (fun j => (b j : ℝ)) (fun _ => 1) I J := by
  simp [roughSignedBinomialWeight, roughAffinePowerCoefficient]

theorem roughSignedBinomialWeight_bound {κ : Type*} [Fintype κ]
    (I J : κ → ℕ) (b : κ → ℤ) (q : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (hJ : (∑ j, J j) ≤ q) (hb : ∀ j, |(b j : ℝ)| ≤ T) :
    |(roughSignedBinomialWeight I J b : ℝ)| ≤
      (2 : ℝ)^q*T^((∑ j, J j)-(∑ j, I j)) := by
  by_cases hIJ : ∀ j, I j ≤ J j
  · have hprod : |(roughSignedBinomialWeight I J b : ℝ)| ≤
        (2 : ℝ)^(∑ j, J j)*T^(∑ j, (J j-I j)) := by
      simp only [roughSignedBinomialWeight, Int.cast_prod, Int.cast_mul, Int.cast_natCast,
        Int.cast_pow, Finset.abs_prod, abs_mul, abs_pow,
        abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ _)]
      calc
        _ ≤ ∏ j, (2 : ℝ)^(J j)*T^(J j-I j) := by
          apply Finset.prod_le_prod
          · intro j _; positivity
          · intro j _
            apply mul_le_mul
            · exact_mod_cast Nat.choose_le_two_pow (J j) (I j)
            · exact pow_le_pow_left₀ (abs_nonneg _) (hb j) _
            · positivity
            · positivity
        _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
            Finset.prod_pow_eq_pow_sum]
    rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => hIJ j)] at hprod
    exact hprod.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ) (by positivity))
  · rw [roughSignedBinomialWeight_eq_zero I J b hIJ, Int.cast_zero, abs_zero]
    positivity

theorem rough_affine_positive_signed_coefficient {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (θ : (κ → ℕ) → ℝ) (c : ℝ)
    (b : κ → ℤ) (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1)
        (C c+∑ J ∈ s, monomial (Finsupp.equivFunOnFinite.symm J) (θ J))) =
      ∑ J ∈ s, (roughSignedBinomialWeight I J b : ℝ)*θ J := by
  have hzero : Finsupp.equivFunOnFinite.symm I ≠ 0 := by
    intro he
    have hz : ∀ j, I j = 0 := fun j => by
      have hh := congrArg (fun f : κ →₀ ℕ => f j) he
      simpa using hh
    simp only [hz, Finset.sum_const_zero] at hI
    omega
  rw [map_add, coeff_add]
  have hc : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => 1) (C c) = C c :=
    eval₂Hom_C _ _ c
  rw [hc, coeff_C, if_neg (Ne.symm hzero), zero_add, map_sum, coeff_sum]
  apply Finset.sum_congr rfl
  intro J _
  rw [rough_mv_affine_monomial_coefficient, ← roughSignedBinomialWeight_real]
  rw [Finsupp.coe_equivFunOnFinite_symm]
  ring

end Hindman168
