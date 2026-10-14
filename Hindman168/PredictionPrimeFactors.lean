import Hindman168.MasterPredictionVariableCubeLimit

/-!
# Bounded prime-only factors in the original variable-dimension product

A prime-only factor can be absorbed in any one nonroot row test. Its
absolute value at most one preserves that row's pointwise majorant, and
the product acquires exactly one copy of the factor. The root stays centered.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def oneRowPrimeFactor {α : Type*} (row0 : α) (ξ : ℝ)
    (G : α → ℤ → ℝ) (row : α) : ℤ → ℝ :=
  if row = row0 then fun t => ξ * G row t else G row

theorem oneRowPrimeFactor_other {α : Type*} (row0 row : α) (ξ : ℝ)
    (G : α → ℤ → ℝ) (hr : row ≠ row0) : oneRowPrimeFactor row0 ξ G row = G row :=
  if_neg hr

theorem oneRowPrimeFactor_bound {α : Type*} (row0 row : α) (ξ : ℝ)
    (G : α → ℤ → ℝ) (B : ℤ → ℝ) (hξ : |ξ| ≤ 1)
    (hG : ∀ t, |G row t| ≤ B t) (t : ℤ) : |oneRowPrimeFactor row0 ξ G row t| ≤ B t := by
  by_cases hr : row = row0
  · simp only [oneRowPrimeFactor, if_pos hr, abs_mul]
    exact ((mul_le_mul_of_nonneg_right hξ (abs_nonneg _))).trans (by simpa only [one_mul] using hG t)
  · rw [oneRowPrimeFactor_other row0 row ξ G hr]
    exact hG t

theorem oneRowPrimeFactor_product {α : Type*} [Fintype α] (row0 : α) (ξ : ℝ)
    (G : α → ℤ → ℝ) (z : α → ℤ) :
    (∏ row, oneRowPrimeFactor row0 ξ G row (z row)) = ξ * ∏ row, G row (z row) := by
  have ht (row : α) : oneRowPrimeFactor row0 ξ G row (z row) =
      (if row = row0 then ξ else 1) * G row (z row) := by
    by_cases hr : row = row0 <;> simp [oneRowPrimeFactor, hr]
  simp_rw [ht]
  rw [Finset.prod_mul_distrib]
  simp

end Hindman168
