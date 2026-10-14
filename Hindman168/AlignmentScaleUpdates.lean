import Hindman168.AlignmentBinaryWeights

/-! Exact positive rational compensating scales. The updated target's
block product is fixed, while arbitrary earlier products use their actual
binary exponents. Negative pivot exponents are genuine integer powers. -/

namespace Hindman168
open scoped BigOperators Classical

def alignmentMultiplier {n : ℕ} (i : Fin n) (T : Finset (Fin n)) (k : ℕ)
    (j : Fin n) : ℚ :=
  if j < i then (k : ℚ) ^ ((2 ^ (n - 1 - j.val) : ℕ) : ℤ)
  else if j = i then (k : ℚ) ^ (-(alignmentSubsetWeight T : ℤ)) else 1

def alignmentScaleUpdate {n : ℕ} (i : Fin n) (T : Finset (Fin n)) (k : ℕ)
    (b : Fin n → ℚ) (j : Fin n) : ℚ := b j * alignmentMultiplier i T k j

theorem alignmentMultiplier_positive {n : ℕ} (i : Fin n) (T : Finset (Fin n))
    (k : ℕ) (hk : 0 < k) (j : Fin n) : 0 < alignmentMultiplier i T k j := by
  have hkQ : (0 : ℚ) < k := by exact_mod_cast hk
  unfold alignmentMultiplier
  split_ifs <;> positivity

theorem alignmentScaleUpdate_positive {n : ℕ} (i : Fin n) (T : Finset (Fin n))
    (k : ℕ) (hk : 0 < k) (b : Fin n → ℚ) (hb : ∀ j, 0 < b j) :
    ∀ j, 0 < alignmentScaleUpdate i T k b j :=
  fun j => mul_pos (hb j) (alignmentMultiplier_positive i T k hk j)

theorem alignmentScaleUpdate_product {n : ℕ} (i : Fin n) (T S : Finset (Fin n))
    (k : ℕ) (b : Fin n → ℚ) :
    finiteScaleBlockProduct (alignmentScaleUpdate i T k b) S =
      finiteScaleBlockProduct b S * finiteScaleBlockProduct (alignmentMultiplier i T k) S := by
  unfold finiteScaleBlockProduct alignmentScaleUpdate
  exact Finset.prod_mul_distrib

theorem alignmentMultiplier_before_product {n : ℕ} (i : Fin n)
    (T S : Finset (Fin n)) (k : ℕ) (hk : 0 < k) (hS : ∀ j ∈ S, j < i) :
    finiteScaleBlockProduct (alignmentMultiplier i T k) S =
      (k : ℚ) ^ (alignmentSubsetWeight S : ℤ) := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  revert hS
  induction S using Finset.induction_on with
  | empty => intro _; simp [finiteScaleBlockProduct, alignmentSubsetWeight]
  | @insert j S hj ih =>
    intro hS
    have hji := hS j (Finset.mem_insert_self _ _)
    have hS' : ∀ a ∈ S, a < i := fun a ha => hS a (Finset.mem_insert_of_mem ha)
    rw [finiteScaleBlockProduct, Finset.prod_insert hj]
    change alignmentMultiplier i T k j * finiteScaleBlockProduct (alignmentMultiplier i T k) S = _
    rw [ih hS']
    simp only [alignmentMultiplier, if_pos hji, alignmentSubsetWeight,
      Finset.sum_insert hj, Nat.cast_add, zpow_add₀ hkQ]

theorem alignmentMultiplier_pivot_product {n : ℕ} (i : Fin n)
    (T C : Finset (Fin n)) (k : ℕ) (hk : 0 < k) (hC : ∀ j ∈ C, j < i) :
    finiteScaleBlockProduct (alignmentMultiplier i T k) (insert i C) =
      (k : ℚ) ^ ((alignmentSubsetWeight C : ℤ) - alignmentSubsetWeight T) := by
  have hi : i ∉ C := fun hi => (lt_irrefl i) (hC i hi)
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  unfold finiteScaleBlockProduct at ⊢
  rw [Finset.prod_insert hi]
  change alignmentMultiplier i T k i * finiteScaleBlockProduct (alignmentMultiplier i T k) C = _
  rw [alignmentMultiplier_before_product i T C k hk hC]
  unfold alignmentMultiplier
  rw [if_neg (lt_irrefl i), if_pos rfl, ← zpow_add₀ hkQ]
  congr 1
  ring

theorem alignmentScaleUpdate_target_fixed {n : ℕ} (i : Fin n) (T : Finset (Fin n))
    (k : ℕ) (hk : 0 < k) (hT : ∀ j ∈ T, j < i) (b : Fin n → ℚ) :
    finiteScaleBlockProduct (alignmentScaleUpdate i T k b) (insert i T) =
      finiteScaleBlockProduct b (insert i T) := by
  rw [alignmentScaleUpdate_product, alignmentMultiplier_pivot_product i T T k hk hT,
    sub_self, zpow_zero, mul_one]

end Hindman168
