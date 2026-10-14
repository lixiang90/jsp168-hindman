import Hindman168.RoughMvAffineCoefficient
import Hindman168.RoughTriangularBinomial

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

theorem roughAffinePowerCoefficient_uniform {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b : κ → R) (k : R) (I J : κ → ℕ) :
    roughAffinePowerCoefficient b (fun _ => k) I J =
      k^(∑ j, I j)*(∏ j, ((J j).choose (I j) : R)*b j^(J j-I j)) := by
  rw [roughAffinePowerCoefficient, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, mul_comm]

theorem roughAffinePowerCoefficient_nat {κ : Type*} [Fintype κ]
    (b : κ → ℕ) (p : ℕ) (I J : κ → ℕ) :
    roughAffinePowerCoefficient (fun j => (b j : ℝ)) (fun _ => (p : ℝ)) I J =
      (p : ℝ)^(∑ j, I j)*(roughBinomialWeight I J b : ℝ) := by
  rw [roughAffinePowerCoefficient_uniform]
  simp [roughBinomialWeight]

theorem rough_affine_binomial_coefficient {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (theta : (κ → ℕ) → ℝ) (b : κ → ℕ) (p : ℕ) (I : κ → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => (p : ℝ))
        (∑ J ∈ s, monomial (Finsupp.equivFunOnFinite.symm J) (theta J))) =
      (p : ℝ)^(∑ j, I j)*∑ J ∈ s, (roughBinomialWeight I J b : ℝ)*theta J := by
  rw [map_sum, coeff_sum]
  simp_rw [rough_mv_affine_monomial_coefficient, roughAffinePowerCoefficient_nat]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J _
  have he : (Finsupp.equivFunOnFinite.symm J : κ → ℕ) = J :=
    Finsupp.coe_equivFunOnFinite_symm J
  rw [he]
  ring

theorem rough_affine_positive_binomial_coefficient {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (theta : (κ → ℕ) → ℝ) (c : ℝ)
    (b : κ → ℕ) (p : ℕ) (I : κ → ℕ) (hI : 0 < ∑ j, I j) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => (p : ℝ))
        (C c+∑ J ∈ s, monomial (Finsupp.equivFunOnFinite.symm J) (theta J))) =
      (p : ℝ)^(∑ j, I j)*∑ J ∈ s, (roughBinomialWeight I J b : ℝ)*theta J := by
  have hzero : Finsupp.equivFunOnFinite.symm I ≠ 0 := by
    intro he
    have hz : ∀ j, I j = 0 := by
      intro j
      have hh := congrArg (fun f : κ →₀ ℕ => f j) he
      simpa using hh
    simp only [hz, Finset.sum_const_zero] at hI
    omega
  rw [map_add, coeff_add]
  have hc : roughMvAffineSubstitution (fun j => (b j : ℝ)) (fun _ => (p : ℝ)) (C c) = C c := by
    exact eval₂Hom_C _ _ c
  rw [hc, coeff_C, if_neg (Ne.symm hzero), zero_add]
  exact rough_affine_binomial_coefficient s theta b p I

end Hindman168
