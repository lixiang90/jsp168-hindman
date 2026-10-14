import Hindman168.FiniteMass
import Mathlib.Tactic

namespace Hindman168
open scoped BigOperators

theorem rough_convex_piece_after_reweighting {ι : Type*} (s : Finset ι)
    (p q a b : ι → ℝ) (θ B η : ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (ht : ∑ i ∈ s, p i = 1)
    (hb : ∀ i ∈ s, |b i| ≤ B)
    (hgap : θ + B * (∑ i ∈ s, |p i - q i|) < η)
    (hbad : η ≤ |(∑ i ∈ s, p i * a i) - ∑ i ∈ s, q i * b i|) :
    ∃ i ∈ s, 0 < p i ∧ θ < |a i - b i| := by
  classical
  by_contra hn
  push Not at hn
  have hterm : ∀ i ∈ s, p i * |a i - b i| ≤ p i * θ := by
    intro i hi
    by_cases hpi : 0 < p i
    · exact mul_le_mul_of_nonneg_left (hn i hi hpi) (hp i hi)
    · have hz : p i = 0 := le_antisymm (le_of_not_gt hpi) (hp i hi)
      simp only [hz, zero_mul, le_refl]
  have hfirst : |∑ i ∈ s, p i * (a i - b i)| ≤ θ := by
    calc
      _ ≤ ∑ i ∈ s, |p i * (a i - b i)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ s, p i * |a i - b i| := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [abs_mul, abs_of_nonneg (hp i hi)]
      _ ≤ ∑ i ∈ s, p i * θ := Finset.sum_le_sum hterm
      _ = θ := by rw [← Finset.sum_mul, ht, one_mul]
  have hsecond : |∑ i ∈ s, (p i - q i) * b i| ≤ B * (∑ i ∈ s, |p i - q i|) := by
    calc
      _ ≤ ∑ i ∈ s, |(p i - q i) * b i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, |p i - q i| * B := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hb i hi) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul, mul_comm]
  have he : (∑ i ∈ s, p i * a i) - ∑ i ∈ s, q i * b i =
      (∑ i ∈ s, p i * (a i - b i)) + ∑ i ∈ s, (p i - q i) * b i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hbad
  have hle := (abs_add_le (∑ i ∈ s, p i * (a i - b i))
    (∑ i ∈ s, (p i - q i) * b i)).trans (add_le_add hfirst hsecond)
  linarith

end Hindman168
