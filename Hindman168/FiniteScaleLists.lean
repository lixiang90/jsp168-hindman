import Hindman168.PrincipalPredictionLimitData

/-! Finite positive rational scale lists can be closed under all block
products before parameters, models or thresholds are selected. -/

namespace Hindman168
open scoped BigOperators Classical

def finiteScaleBlockProduct {n : ℕ} (b : Fin n → ℚ) (S : Finset (Fin n)) : ℚ :=
  ∏ k ∈ S, b k

def FiniteScaleClosure {n : ℕ} (B : Finset (Fin n → ℚ)) (A : Finset ℚ) : Prop :=
  ∀ b ∈ B, ∀ S : Finset (Fin n), S.Nonempty → finiteScaleBlockProduct b S ∈ A

noncomputable def finiteScaleProductClosure {n : ℕ}
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) : Finset ℚ :=
  A ∪ B.biUnion (fun b => (Finset.univ : Finset (Fin n)).powerset.image
    (finiteScaleBlockProduct b))

theorem finiteScaleBlockProduct_positive {n : ℕ} (b : Fin n → ℚ)
    (hb : ∀ k, 0 < b k) (S : Finset (Fin n)) : 0 < finiteScaleBlockProduct b S :=
  Finset.prod_pos (fun k _ => hb k)

theorem finiteScaleProductClosure_contains {n : ℕ}
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) : A ⊆ finiteScaleProductClosure B A :=
  Finset.subset_union_left

theorem finiteScaleProductClosure_block_mem {n : ℕ}
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) (b : Fin n → ℚ) (hb : b ∈ B)
    (S : Finset (Fin n)) : finiteScaleBlockProduct b S ∈ finiteScaleProductClosure B A := by
  apply Finset.mem_union_right
  apply Finset.mem_biUnion.mpr
  refine ⟨b, hb, Finset.mem_image.mpr ⟨S, ?_, rfl⟩⟩
  exact Finset.mem_powerset.mpr (Finset.subset_univ S)

theorem finiteScaleProductClosure_positive {n : ℕ}
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ)
    (hB : ∀ b ∈ B, ∀ k, 0 < b k) (hA : ∀ a ∈ A, 0 < a) :
    ∀ a ∈ finiteScaleProductClosure B A, 0 < a := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · exact hA a ha
  · obtain ⟨b, hb, ha⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp ha
    exact finiteScaleBlockProduct_positive b (hB b hb) S

theorem finiteScaleProductClosure_closed {n : ℕ}
    (B : Finset (Fin n → ℚ)) (A : Finset ℚ) :
    FiniteScaleClosure B (finiteScaleProductClosure B A) := by
  intro b hb S _
  exact finiteScaleProductClosure_block_mem B A b hb S

end Hindman168
