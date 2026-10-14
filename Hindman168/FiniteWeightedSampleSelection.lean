import Hindman168.FiniteWeightedSamplingMoments
import Hindman168.HaarSamplingVariance

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

/-- A nonnegative finite probability has an actual sample, on its
support, whose test value does not exceed its original expectation. -/
theorem expectation_exists_support_le {A : Type*} (μ : Mass A)
    (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1) (f : A → ℝ) :
    ∃ a ∈ μ.support, f a ≤ expectation μ f := by
  have hne : μ ≠ 0 := by
    intro he
    simp only [he, total, Finsupp.sum_zero_index] at ht
    norm_num at ht
  have hS := Finsupp.support_nonempty_iff.mpr hne
  by_contra hn
  have hf : ∀ a ∈ μ.support, expectation μ f < f a := by
    simpa only [not_exists, not_and, not_le] using hn
  have hh := Finset.sum_lt_sum_of_nonempty hS (fun a ha =>
    mul_lt_mul_of_pos_left (hf a ha) (lt_of_le_of_ne (hμ a) (Ne.symm (Finsupp.mem_support_iff.mp ha))))
  have hc : (∑ a ∈ μ.support, μ a * expectation μ f) = expectation μ f := by
    rw [← Finset.sum_mul]
    change total μ * expectation μ f = _
    rw [ht, one_mul]
  rw [hc] at hh
  exact (lt_irrefl (expectation μ f)) hh

/-- One actual sample meets both nonnegative budgets within a factor
two. The test uses the original law and two fixed positive denominators. -/
theorem expectation_exists_two_budgets {A : Type*} (μ : Mass A)
    (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    (X Y : A → ℝ) (hX : ∀ a, 0 ≤ X a) (hY : ∀ a, 0 ≤ Y a)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hEX : expectation μ X ≤ a) (hEY : expectation μ Y ≤ b) :
    ∃ s ∈ μ.support, X s ≤ 2 * a ∧ Y s ≤ 2 * b := by
  obtain ⟨s, hs, hf⟩ := expectation_exists_support_le μ hμ ht (fun s => X s / a + Y s / b)
  have he : expectation μ (fun s => X s / a + Y s / b) ≤ 2 := by
    rw [expectation_add]
    have hx : expectation μ (fun s => X s / a) = expectation μ X / a := by
      simp only [div_eq_mul_inv, expectation, Finsupp.sum]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    have hy : expectation μ (fun s => Y s / b) = expectation μ Y / b := by
      simp only [div_eq_mul_inv, expectation, Finsupp.sum]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun _ _ => by ring)
    rw [hx, hy]
    have hxle := (div_le_one ha).mpr hEX
    have hyle := (div_le_one hb).mpr hEY
    linarith
  have hsum := hf.trans he
  have hx : X s / a ≤ 2 := by linarith [div_nonneg (hY s) hb.le]
  have hy : Y s / b ≤ 2 := by linarith [div_nonneg (hX s) ha.le]
  exact ⟨s, hs, (div_le_iff₀ ha).mp hx, (div_le_iff₀ hb).mp hy⟩

/-- The actual off-diagonal pair sum has expectation at most m squared
times the original independent pair mean. No diagonal term is tested. -/
theorem expectation_piMass_offDiagonal_sum_le {A : Type*}
    (μ : Mass A) (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    (f : A → A → ℝ) (hf : ∀ a b, 0 ≤ f a b) (m : ℕ) :
    expectation (piMass (fun _ : Fin m => μ))
      (fun s => ∑ i, ∑ j, if i = j then 0 else f (s i) (s j)) ≤
      (m : ℝ) ^ 2 * expectation μ (fun a => expectation μ (f a)) := by
  have hc : 0 ≤ expectation μ (fun a => expectation μ (f a)) :=
    expectation_nonneg μ _ hμ (fun a => expectation_nonneg μ _ hμ (hf a))
  simp only [expectation_finset_sum]
  calc
    _ ≤ ∑ _i : Fin m, ∑ _j : Fin m, expectation μ (fun a => expectation μ (f a)) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · simp only [if_pos hij, expectation_const, mul_zero]
        exact hc
      · simp only [if_neg hij]
        rw [expectation_piMass_distinct_pair _ (fun _ => ht) i j hij]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Fixed-size sampling simultaneously approximates the original
weighted mean and makes every off-diagonal total small when the
original pair mean is small. Arbitrary real probability weights remain. -/
theorem expectation_exists_bessel_sample {A : Type*}
    (μ : Mass A) (hμ : ∀ a, 0 ≤ μ a) (ht : total μ = 1)
    (h : A → ℝ) (hh : ∀ a, |h a| ≤ 1)
    (f : A → A → ℝ) (hf : ∀ a b, 0 ≤ f a b)
    (m : ℕ) (hm : 0 < m) (η : ℝ) (hη : 0 < η) :
    ∃ s : Fin m → A,
      (finiteHaarMean (fun i => h (s i)) - expectation μ h) ^ 2 ≤ 2 / (m : ℝ) ∧
      (∑ i, ∑ j, if i = j then 0 else f (s i) (s j)) ≤
        2 * ((m : ℝ) ^ 2 * expectation μ (fun a => expectation μ (f a)) + η) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hc : 0 ≤ expectation μ (fun a => expectation μ (f a)) :=
    expectation_nonneg μ _ hμ (fun a => expectation_nonneg μ _ hμ (hf a))
  obtain ⟨s, _, hx, hy⟩ := expectation_exists_two_budgets (piMass (fun _ : Fin m => μ))
    (piMass_nonneg _ (fun _ => hμ)) (piMass_total_one _ (fun _ => ht))
    (fun s => ((∑ i, h (s i)) / m - expectation μ h) ^ 2)
    (fun s => ∑ i, ∑ j, if i = j then 0 else f (s i) (s j))
    (fun _ => sq_nonneg _) (fun s => Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => by split_ifs; exact le_rfl; exact hf _ _)))
    (1 / (m : ℝ)) ((m : ℝ) ^ 2 * expectation μ (fun a => expectation μ (f a)) + η)
    (by positivity) (by positivity)
    (expectation_piMass_sample_variance_le μ hμ ht h hh m hm)
    ((expectation_piMass_offDiagonal_sum_le μ hμ ht f hf m).trans (le_add_of_nonneg_right hη.le))
  refine ⟨s, ?_, hy⟩
  simpa only [finiteHaarMean, Fintype.card_fin, mul_one_div] using hx

end Hindman168.FiniteMass
