import Hindman168.MaskInitialSubsetForms

/-! Separate the exact singleton center weights from all nonsingleton
sum-form factors. Positive coefficients are needed for c/c = 1. -/

namespace Hindman168
open scoped BigOperators Classical

def columnSingleton {n : ℕ} (k : Fin n) : NonemptyColumnSubset n :=
  ⟨{k}, Finset.singleton_nonempty k⟩

theorem columnSingleton_max {n : ℕ} (k : Fin n) :
    (columnSingleton k).val.max' (columnSingleton k).property = k := by
  simp [columnSingleton]

theorem smallColumnSubset_eq_singleton {n : ℕ} (U : NonemptyColumnSubset n)
    (hU : ¬2 ≤ U.val.card) : U = columnSingleton (U.val.max' U.property) := by
  have hc : U.val.card = 1 := by
    have hp := Finset.card_pos.mpr U.property
    omega
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hc
  apply Subtype.ext
  simp [columnSingleton, hk]

theorem nonemptySubset_singleton_product {n : ℕ} (f : Fin n → ℝ) :
    (∏ U : NonemptyColumnSubset n,
      if 2 ≤ U.val.card then 1 else f (U.val.max' U.property)) = ∏ k, f k := by
  let E : {U : NonemptyColumnSubset n // ¬2 ≤ U.val.card} ≃ Fin n :=
    { toFun := fun U => U.val.val.max' U.val.property
      invFun := fun k => ⟨columnSingleton k, by simp [columnSingleton]⟩
      left_inv := fun U => by
        apply Subtype.ext
        exact (smallColumnSubset_eq_singleton U.val U.property).symm
      right_inv := fun k => columnSingleton_max k }
  have h := Fintype.prod_subtype_mul_prod_subtype
    (fun U : NonemptyColumnSubset n => 2 ≤ U.val.card)
    (fun U => if 2 ≤ U.val.card then 1 else f (U.val.max' U.property))
  have hl : (fun U : {U : NonemptyColumnSubset n // 2 ≤ U.val.card} =>
      if 2 ≤ U.val.val.card then (1 : ℝ) else f (U.val.val.max' U.val.property)) =
      (fun _ => 1) := by
    funext U
    exact if_pos U.property
  have hs : (fun U : {U : NonemptyColumnSubset n // ¬2 ≤ U.val.card} =>
      if 2 ≤ U.val.val.card then (1 : ℝ) else f (U.val.val.max' U.val.property)) =
      (fun U => f (U.val.val.max' U.val.property)) := by
    funext U
    exact if_neg U.property
  change (∏ U : {U : NonemptyColumnSubset n // 2 ≤ U.val.card},
      if 2 ≤ U.val.val.card then (1 : ℝ) else f (U.val.val.max' U.val.property)) *
      (∏ U : {U : NonemptyColumnSubset n // ¬2 ≤ U.val.card},
        if 2 ≤ U.val.val.card then (1 : ℝ) else f (U.val.val.max' U.val.property)) = _ at h
  rw [hl, hs, Finset.prod_const_one, one_mul] at h
  rw [← h]
  exact Fintype.prod_equiv E _ _ (fun _ => rfl)

theorem maskSubsetIntegerForm_singleton {m : ℕ} (c : Fin (m+1) → ℕ)
    (hc : ∀ k, 0 < c k) (k : Fin (m+1)) (z : Fin (m+1) → ℤ) :
    maskSubsetIntegerForm c (columnSingleton k) z = z k := by
  simp [maskSubsetIntegerForm, columnSingleton, Nat.ne_of_gt (hc k)]

theorem subset_center_product {m : ℕ} (c : Fin (m+1) → ℕ)
    (hc : ∀ k, 0 < c k) (ν : Fin (m+1) → ℤ → ℝ) (z : Fin (m+1) → ℤ) :
    (∏ U : NonemptyColumnSubset (m+1), if 2 ≤ U.val.card then 1 else
      ν (U.val.max' U.property) (maskSubsetIntegerForm c U z)) = ∏ k, ν k (z k) := by
  rw [← nonemptySubset_singleton_product (fun k => ν k (z k))]
  apply Finset.prod_congr rfl
  intro U _
  by_cases hU : 2 ≤ U.val.card
  · simp only [if_pos hU]
  · simp only [if_neg hU]
    have he := smallColumnSubset_eq_singleton U hU
    rw [he, columnSingleton_max, maskSubsetIntegerForm_singleton c hc]

end Hindman168
