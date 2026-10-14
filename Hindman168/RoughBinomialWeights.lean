import Hindman168.RoughHorizontalInterpolation
import Mathlib.Data.Nat.Choose.Bounds

namespace Hindman168
open scoped BigOperators

theorem rough_binomial_weight_bound {ι : Type*} (s : Finset ι)
    (I J b : ι → ℕ) (p : ℝ)
    (hb : ∀ j ∈ s, (b j : ℝ) ≤ p) :
    |(((∏ j ∈ s, (J j).choose (I j) * b j ^ (J j - I j) : ℕ) : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ (∑ j ∈ s, J j) * p ^ (∑ j ∈ s, (J j - I j)) := by
  push_cast
  rw [abs_of_nonneg (by positivity)]
  calc
    ∏ j ∈ s, ((J j).choose (I j) : ℝ) * (b j : ℝ) ^ (J j - I j) ≤
        ∏ j ∈ s, (2 : ℝ) ^ J j * p ^ (J j - I j) := by
      apply Finset.prod_le_prod
      · intro j _; positivity
      · intro j hj
        apply mul_le_mul
        · exact_mod_cast Nat.choose_le_two_pow (J j) (I j)
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) (hb j hj) _
        · positivity
        · positivity
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finset.prod_pow_eq_pow_sum]

theorem rough_binomial_weight_degree_bound {ι : Type*} (s : Finset ι)
    (I J b : ι → ℕ) (q : ℕ) (p : ℝ) (hp : 0 ≤ p)
    (hIJ : ∀ j ∈ s, I j ≤ J j) (hJ : ∑ j ∈ s, J j ≤ q)
    (hb : ∀ j ∈ s, (b j : ℝ) ≤ p) :
    |(((∏ j ∈ s, (J j).choose (I j) * b j ^ (J j - I j) : ℕ) : ℤ) : ℝ)| ≤
      (2 : ℝ) ^ q * p ^ ((∑ j ∈ s, J j) - ∑ j ∈ s, I j) := by
  have hh := rough_binomial_weight_bound s I J b p hb
  rw [Finset.sum_tsub_distrib s hIJ] at hh
  apply hh.trans
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hJ) (by positivity)

theorem rough_multiindex_strict_degree {ι : Type*} [Fintype ι]
    {I J : ι → ℕ} (hIJ : ∀ j, I j ≤ J j) (hne : I ≠ J) :
    (∑ j, I j) < ∑ j, J j := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, I j ≠ J j := by
    by_contra h
    apply hne
    funext j
    exact not_not.mp (not_exists.mp h j)
  exact Finset.sum_lt_sum (fun j _ => hIJ j) ⟨j, Finset.mem_univ j, (hIJ j).lt_of_ne hj⟩

theorem rough_mod_one_multiindex_descent {ι κ : Type*} [Fintype κ]
    (s : Finset ι) (I : κ → ℕ) (J : ι → κ → ℕ) (b : κ → ℕ)
    (p D : ℕ) (theta Z A0 A : ℝ) (u : ι → ℝ) (k : ι → ℤ)
    (hZ : 0 < Z) (hpZ : (p : ℝ) ≤ Z) (hA : 0 ≤ A)
    (hIJ : ∀ i ∈ s, ∀ j, I j ≤ J i j) (hJ : ∀ i ∈ s, (∑ j, J i j) ≤ D)
    (hb : ∀ j, b j ≤ p)
    (hu : ∀ i ∈ s, |u i - (k i : ℝ)| ≤ A * Z⁻¹ ^ (∑ j, J i j))
    (hobs : ‖(((p : ℝ) ^ (∑ j, I j) *
      (theta + ∑ i ∈ s, ((∏ j, (J i j).choose (I j) * b j ^ (J i j - I j) : ℕ) : ℝ) * u i) : ℝ) : UnitAddCircle)‖ ≤
        A0 * ((p : ℝ) / Z) ^ (∑ j, I j)) :
    ‖(((p : ℝ) ^ (∑ j, I j) * theta : ℝ) : UnitAddCircle)‖ ≤
      (A0 + (s.card : ℝ) * (2 : ℝ) ^ D * A) * ((p : ℝ) / Z) ^ (∑ j, I j) := by
  classical
  let c : ι → ℤ := fun i => (∏ j, (J i j).choose (I j) * b j ^ (J i j - I j) : ℕ)
  have hc : ∀ i ∈ s, |(c i : ℝ)| ≤ (2 : ℝ) ^ D *
      (p : ℝ) ^ ((∑ j, J i j) - ∑ j, I j) := by
    intro i hi
    exact rough_binomial_weight_degree_bound Finset.univ I (J i) b D (p : ℝ)
      (Nat.cast_nonneg p) (fun j _ => hIJ i hi j) (hJ i hi)
      (fun j _ => by exact_mod_cast hb j)
  have he : ∀ i ∈ s, (∑ j, I j) + ((∑ j, J i j) - ∑ j, I j) = ∑ j, J i j := by
    intro i hi
    exact Nat.add_sub_cancel' (Finset.sum_le_sum fun j _ => hIJ i hi j)
  have ho : ‖(((p : ℝ) ^ (∑ j, I j) * (theta + ∑ i ∈ s, (c i : ℝ) * u i) : ℝ) : UnitAddCircle)‖ ≤
      A0 * ((p : ℝ) / Z) ^ (∑ j, I j) := by
    simpa only [c, Int.cast_natCast] using hobs
  have hh := rough_mod_one_descending_coefficient s p (∑ j, I j) theta Z A0 c k u
    (fun _ => A) (fun _ => (2 : ℝ) ^ D) (fun i => (∑ j, J i j) - ∑ j, I j)
    hZ hpZ (fun _ _ => hA) (fun _ _ => by positivity) hc
    (fun i hi => by simpa only [he i hi] using hu i hi) ho
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using hh

end Hindman168
