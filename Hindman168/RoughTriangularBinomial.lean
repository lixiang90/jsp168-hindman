import Hindman168.RoughBinomialWeights
import Hindman168.RoughSimultaneousDescent

namespace Hindman168
open scoped BigOperators

def roughBinomialWeight {κ : Type*} [Fintype κ] (I J b : κ → ℕ) : ℤ :=
  (∏ j, (J j).choose (I j) * b j ^ (J j - I j) : ℕ)

theorem roughBinomialWeight_self {κ : Type*} [Fintype κ] (I b : κ → ℕ) :
    roughBinomialWeight I I b = 1 := by
  simp [roughBinomialWeight]

theorem roughBinomialWeight_eq_zero {κ : Type*} [Fintype κ] (I J b : κ → ℕ)
    (h : ¬ ∀ j, I j ≤ J j) : roughBinomialWeight I J b = 0 := by
  classical
  push Not at h
  obtain ⟨j, hj⟩ := h
  unfold roughBinomialWeight
  have hz : (∏ j, (J j).choose (I j) * b j ^ (J j - I j) : ℕ) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [Nat.choose_eq_zero_of_lt hj, zero_mul]
  rw [hz, Nat.cast_zero]

theorem roughBinomialWeight_bound {κ : Type*} [Fintype κ] (I J b : κ → ℕ)
    (D p : ℕ) (hJ : (∑ j, J j) ≤ D) (hb : ∀ j, b j ≤ p) :
    |(roughBinomialWeight I J b : ℝ)| ≤ (2 : ℝ) ^ D *
      (p : ℝ) ^ ((∑ j, J j) - ∑ j, I j) := by
  by_cases hIJ : ∀ j, I j ≤ J j
  · exact rough_binomial_weight_degree_bound Finset.univ I J b D (p : ℝ)
      (Nat.cast_nonneg p) (fun j _ => hIJ j) hJ (fun j _ => by exact_mod_cast hb j)
  · rw [roughBinomialWeight_eq_zero I J b hIJ, Int.cast_zero, abs_zero]
    positivity

theorem rough_binomial_sum_triangular {κ : Type*} [Fintype κ]
    (s : Finset (κ → ℕ)) (I b : κ → ℕ) (hI : I ∈ s) (u : (κ → ℕ) → ℝ) :
    (∑ J ∈ s, (roughBinomialWeight I J b : ℝ) * u J) =
      u I + ∑ J ∈ s.filter (fun J => (∑ j, I j) < ∑ j, J j),
        (roughBinomialWeight I J b : ℝ) * u J := by
  classical
  let v := s.filter (fun J => (∑ j, I j) < ∑ j, J j)
  have hv : v ⊆ s.erase I := by
    intro J hJ
    obtain ⟨hJs, hlt⟩ := Finset.mem_filter.mp hJ
    exact Finset.mem_erase.mpr ⟨by intro he; subst J; omega, hJs⟩
  have heq : (∑ J ∈ v, (roughBinomialWeight I J b : ℝ) * u J) =
      ∑ J ∈ s.erase I, (roughBinomialWeight I J b : ℝ) * u J := by
    apply Finset.sum_subset hv
    intro J hJ hn
    have hne : I ≠ J := (Finset.mem_erase.mp hJ).1.symm
    have hzero : roughBinomialWeight I J b = 0 := by
      apply roughBinomialWeight_eq_zero
      intro hIJ
      have hlt := rough_multiindex_strict_degree hIJ hne
      exact hn (Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hJ).2, hlt⟩)
    rw [hzero, Int.cast_zero, zero_mul]
  have hsplit := Finset.sum_erase_add s (fun J => (roughBinomialWeight I J b : ℝ) * u J) hI
  rw [roughBinomialWeight_self, Int.cast_one, one_mul, ← heq] at hsplit
  exact hsplit.symm.trans (add_comm _ _)

end Hindman168
