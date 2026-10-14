import Hindman168.RoughMvAffineSubstitution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Choose.Sum

namespace Hindman168
open MvPolynomial
open scoped BigOperators Classical

def roughAffinePowerCoefficient {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b k : κ → R) (I J : κ → ℕ) : R :=
  ∏ j, ((J j).choose (I j) : R)*b j^(J j-I j)*k j^(I j)

theorem rough_affine_power_expansion {κ R : Type*} [CommSemiring R]
    (j : κ) (b k : R) (n : ℕ) :
    (C b+C k*X j : MvPolynomial κ R)^n =
      ∑ i ∈ Finset.range (n+1), C ((n.choose i : R)*b^(n-i)*k^i)*X j^i := by
  rw [add_comm, add_pow]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_pow, map_mul, map_pow, map_natCast]
  ring

theorem rough_affine_monomial_expansion {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b k : κ → R) (J : κ → ℕ) :
    (∏ j, (C (b j)+C (k j)*X j : MvPolynomial κ R)^(J j)) =
      ∑ I ∈ Fintype.piFinset (fun j => Finset.range (J j+1)),
        C (roughAffinePowerCoefficient b k I J)*∏ j, X j^(I j) := by
  simp_rw [rough_affine_power_expansion]
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.prod_mul_distrib, ← map_prod]
  rfl

theorem rough_affine_monomial_coefficient {κ R : Type*} [Fintype κ] [CommSemiring R]
    (b k : κ → R) (I J : κ → ℕ) :
    coeff (Finsupp.equivFunOnFinite.symm I)
      (∏ j, (C (b j)+C (k j)*X j : MvPolynomial κ R)^(J j)) =
      roughAffinePowerCoefficient b k I J := by
  classical
  rw [rough_affine_monomial_expansion, coeff_sum]
  simp only [coeff_C_mul, coeff_prod_X_pow]
  have hi : ∀ K : κ → ℕ, Finsupp.indicator Finset.univ (fun j _ => K j) =
      Finsupp.equivFunOnFinite.symm K := by
    intro K
    ext j
    simp
  simp_rw [hi, Finsupp.equivFunOnFinite.symm.injective.eq_iff]
  rw [Finset.sum_eq_single I]
  · simp only [ite_true, mul_one]
  · intro K _ hKI
    simp only [if_neg hKI.symm, mul_zero]
  · intro hI
    simp only [ite_true, mul_one]
    simp only [Fintype.mem_piFinset, Finset.mem_range, Nat.lt_succ_iff] at hI
    push Not at hI
    obtain ⟨j, hj⟩ := hI
    unfold roughAffinePowerCoefficient
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul, zero_mul]

end Hindman168
