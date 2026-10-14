import Hindman168.LocalExcessValuationWeights
import Hindman168.PolynomialGeometricBounds

/-!
# Finite covers by largest and second-largest valuations

The bad branch is grouped by its largest valuation. The other branch is
covered by a choice of the largest coordinate and the two largest values.
The cells retain the actual top-pair sum. Their cardinality and polynomial
weights are bounded without assuming finite support of the probability law.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem finite_nonnegative_sum_le_cover {α ι : Type*}
    (T : Finset α) (S : Finset ι) (C : ι → Finset α) (f : α → ℝ)
    (hf : ∀ a, 0 ≤ f a)
    (hcover : ∀ a ∈ T, f a ≠ 0 → ∃ i ∈ S, a ∈ C i) :
    (∑ a ∈ T, f a) ≤ ∑ i ∈ S, ∑ a ∈ C i, f a := by
  classical
  have hpoint (a : α) (ha : a ∈ T) :
      f a ≤ ∑ i ∈ S, if a ∈ C i then f a else 0 := by
    by_cases hz : f a = 0
    · rw [hz]
      exact Finset.sum_nonneg (fun i _ => by split_ifs <;> exact le_rfl)
    · obtain ⟨i, hi, hac⟩ := hcover a ha hz
      exact (by simp only [if_pos hac] :
        f a = if a ∈ C i then f a else 0).le.trans
        (Finset.single_le_sum (f := fun j => if a ∈ C j then f a else 0)
          (fun j _ => by split_ifs <;> first | exact hf a | exact le_rfl) hi)
  calc
    _ ≤ ∑ a ∈ T, ∑ i ∈ S, if a ∈ C i then f a else 0 :=
      Finset.sum_le_sum hpoint
    _ = ∑ i ∈ S, ∑ a ∈ T, if a ∈ C i then f a else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.sum_filter]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun a ha => (Finset.mem_filter.mp ha).2) (fun a _ _ => hf a)

noncomputable def maxValuationCell (q A : ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset (fun _ : Fin q => Finset.range (A + 1))).filter
    (fun a => rowMaxValuation a = A)

noncomputable def topValuationCell {q : ℕ} (u : Fin q) (A B : ℕ) : Finset (Fin q → ℕ) :=
  (Fintype.piFinset (fun i : Fin q => if i = u then {A} else Finset.range (B + 1))).filter
    (fun a => rowTopTwoSum a = A + B)

theorem mem_maxValuationCell {q A : ℕ} (a : Fin q → ℕ) :
    a ∈ maxValuationCell q A ↔ (∀ i, a i ≤ A) ∧ rowMaxValuation a = A := by
  simp only [maxValuationCell, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_range, Nat.lt_succ_iff]

theorem mem_topValuationCell {q A B : ℕ} (u : Fin q) (a : Fin q → ℕ) :
    a ∈ topValuationCell u A B ↔
      a u = A ∧ (∀ i, i ≠ u → a i ≤ B) ∧ rowTopTwoSum a = A + B := by
  simp only [topValuationCell, Finset.mem_filter, Fintype.mem_piFinset]
  constructor
  · rintro ⟨h, ht⟩
    exact ⟨by simpa using h u, fun i hi => by simpa [hi, Nat.lt_succ_iff] using h i, ht⟩
  · rintro ⟨hu, ho, ht⟩
    refine ⟨fun i => ?_, ht⟩
    by_cases hi : i = u
    · subst i; simpa using hu
    · simpa [hi, Nat.lt_succ_iff] using ho i hi

theorem maxValuationCell_card_le (q A : ℕ) :
    (maxValuationCell q A).card ≤ (A + 1) ^ q := by
  calc
    _ ≤ (Fintype.piFinset (fun _ : Fin q => Finset.range (A + 1))).card :=
      Finset.card_filter_le _ _
    _ = _ := by simp [Fintype.card_piFinset]

theorem topValuationCell_card_le {q : ℕ} (u : Fin q) (A B : ℕ) :
    (topValuationCell u A B).card ≤ (B + 1) ^ q := by
  calc
    _ ≤ (Fintype.piFinset (fun i : Fin q => if i = u then {A} else Finset.range (B + 1))).card :=
      Finset.card_filter_le _ _
    _ = ∏ i : Fin q, (if i = u then ({A} : Finset ℕ) else Finset.range (B + 1)).card :=
      Fintype.card_piFinset _
    _ ≤ ∏ _ : Fin q, (B + 1) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro i _
      split_ifs <;> simp
    _ = _ := by simp

theorem rowValuationPolynomial_le_max {q : ℕ} (b A : ℕ) (a : Fin q → ℕ)
    (ha : ∀ i, a i ≤ A) :
    rowValuationPolynomial b a ≤ ((A + 1 : ℕ) : ℝ) ^ (b * q) := by
  calc
    _ ≤ ∏ _ : Fin q, ((A + 1 : ℕ) : ℝ) ^ b := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.add_le_add_right (ha i) 1
    _ = _ := by simp [pow_mul]

theorem rowValuationPolynomial_le_top {q : ℕ} (b A B : ℕ) (u : Fin q) (a : Fin q → ℕ)
    (hu : a u = A) (ho : ∀ i, i ≠ u → a i ≤ B) :
    rowValuationPolynomial b a ≤
      ((A + 1 : ℕ) : ℝ) ^ b * ((B + 1 : ℕ) : ℝ) ^ (b * q) := by
  have hB : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) ^ b :=
    one_le_pow₀ (by exact_mod_cast (show 1 ≤ B + 1 by omega))
  calc
    _ ≤ ∏ i : Fin q, (((B + 1 : ℕ) : ℝ) ^ b *
        if i = u then ((A + 1 : ℕ) : ℝ) ^ b else 1) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro i _
      by_cases hi : i = u
      · subst i
        simp only [hu, if_true]
        nlinarith [pow_nonneg (show 0 ≤ ((A + 1 : ℕ) : ℝ) by positivity) b]
      · simp only [if_neg hi, mul_one]
        apply pow_le_pow_left₀ (by positivity)
        exact_mod_cast Nat.add_le_add_right (ho i hi) 1
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        Finset.prod_ite_eq', Finset.mem_univ, if_true, ← pow_mul]
      rw [mul_comm]

theorem maxValuationCell_bad_sum_le (p b q A : ℕ) [NeZero p] :
    (∑ a ∈ maxValuationCell q A, rowValuationWeight p b a * localExcessBeta p a True) ≤
      ((A + 1 : ℕ) : ℝ) ^ ((b + 1) * q) * ((p : ℝ) ^ A)⁻¹ := by
  calc
    _ ≤ ∑ _a ∈ maxValuationCell q A,
        ((A + 1 : ℕ) : ℝ) ^ (b * q) * ((p : ℝ) ^ A)⁻¹ := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hv, he⟩ := (mem_maxValuationCell a).mp ha
      have hb := localExcessBeta_bad_weight_le p b a
      rw [he] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        (rowValuationPolynomial_le_max b A a hv) (by positivity))
    _ ≤ ((A + 1 : ℕ) : ℝ) ^ q *
        (((A + 1 : ℕ) : ℝ) ^ (b * q) * ((p : ℝ) ^ A)⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast maxValuationCell_card_le q A
    _ = _ := by
      rw [← mul_assoc, ← pow_add]
      congr 2
      ring

theorem topValuationCell_good_sum_le {q : ℕ} (p b A B : ℕ) [NeZero p] (u : Fin q) :
    (∑ a ∈ topValuationCell u A B, rowValuationWeight p b a * localExcessBeta p a False) ≤
      (((A + 1 : ℕ) : ℝ) ^ b * ((B + 1 : ℕ) : ℝ) ^ ((b + 1) * q)) *
        ((p : ℝ) ^ (A + B))⁻¹ := by
  calc
    _ ≤ ∑ _a ∈ topValuationCell u A B,
        (((A + 1 : ℕ) : ℝ) ^ b * ((B + 1 : ℕ) : ℝ) ^ (b * q)) *
          ((p : ℝ) ^ (A + B))⁻¹ := by
      apply Finset.sum_le_sum
      intro a ha
      obtain ⟨hu, ho, ht⟩ := (mem_topValuationCell u a).mp ha
      have hb := localExcessBeta_good_weight_le p b a
      rw [ht] at hb
      exact hb.trans (mul_le_mul_of_nonneg_right
        (rowValuationPolynomial_le_top b A B u a hu ho) (by positivity))
    _ ≤ ((B + 1 : ℕ) : ℝ) ^ q *
        ((((A + 1 : ℕ) : ℝ) ^ b * ((B + 1 : ℕ) : ℝ) ^ (b * q)) *
          ((p : ℝ) ^ (A + B))⁻¹) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast topValuationCell_card_le u A B
    _ = _ := by
      have he : (b + 1) * q = q + b * q := by ring
      rw [he, pow_add]
      ring

end Hindman168
