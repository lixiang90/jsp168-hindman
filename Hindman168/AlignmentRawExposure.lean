import Hindman168.AlignmentResidueRepresentative
import Hindman168.AlignmentIntegerNumerators

namespace Hindman168
open scoped BigOperators Classical

/-- Only earlier coordinates are exposed; coordinates at and after the
pivot are not frozen by this predicate. -/
def alignmentRawExposure {n : ℕ} (i : Fin n) (L : ℕ) (T : Finset (Fin n))
    (t t' : Fin n → ℕ) : Prop :=
  (∀ j, j < i → j ∉ T → t j = t' j) ∧
    (∀ j ∈ T, Nat.ModEq L (t j) (t' j))

theorem alignmentPair_source_disjoint_tail {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) : Disjoint (alignmentPairSourceBlock e) e.targetTail := by
  apply Finset.disjoint_left.mpr
  intro j hj hc
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact (lt_irrefl _ (e.target_before_sourcePivot _ hc))
  · exact (lt_irrefl _ (e.source_before_target _ hj _ hc))

theorem alignmentNaturalBlockProduct_congr {n : ℕ} (t t' : Fin n → ℕ)
    (S : Finset (Fin n)) (h : ∀ j ∈ S, t j = t' j) :
    alignmentNaturalBlockProduct t S = alignmentNaturalBlockProduct t' S := by
  exact Finset.prod_congr rfl h

theorem alignmentNaturalBlockProduct_modEq {n : ℕ} (t t' : Fin n → ℕ)
    (S : Finset (Fin n)) (L : ℕ) (h : ∀ j ∈ S, Nat.ModEq L (t j) (t' j)) :
    Nat.ModEq L (alignmentNaturalBlockProduct t S) (alignmentNaturalBlockProduct t' S) := by
  induction S using Finset.induction_on with
  | empty =>
    change Nat.ModEq L 1 1
    exact Nat.ModEq.rfl
  | @insert j S hj ih =>
    rw [alignmentNaturalBlockProduct, alignmentNaturalBlockProduct,
      Finset.prod_insert hj, Finset.prod_insert hj]
    exact (h j (Finset.mem_insert_self j S)).mul
      (ih (fun k hk => h k (Finset.mem_insert_of_mem hk)))

theorem alignmentRawExposure_earlier_modEq {n : ℕ} {i : Fin n} {L : ℕ}
    {T : Finset (Fin n)} {t t' : Fin n → ℕ}
    (h : alignmentRawExposure i L T t t') (j : Fin n) (hj : j < i) :
    Nat.ModEq L (t j) (t' j) := by
  by_cases hjT : j ∈ T
  · exact h.2 j hjT
  · rw [h.1 j hj hjT]

theorem alignmentRawExposure_numerator_modEq {n : ℕ} {i : Fin n} {L : ℕ}
    {T : Finset (Fin n)} {t t' : Fin n → ℕ} (q₀ w : ℕ)
    (h : alignmentRawExposure i L T t t') (e : AlignmentAddingPair n i) :
    Nat.ModEq L (alignmentIntegerNumerator q₀ w e t) (alignmentIntegerNumerator q₀ w e t') := by
  exact (alignmentNaturalBlockProduct_modEq t t' (alignmentPairSourceBlock e) L
    (fun j hj => alignmentRawExposure_earlier_modEq h j (alignmentPair_source_before e j hj))).mul_left _

theorem alignmentRawExposure_own_numerator_eq {n : ℕ} {i : Fin n} {L : ℕ}
    {T : Finset (Fin n)} {t t' : Fin n → ℕ} (q₀ w : ℕ)
    (h : alignmentRawExposure i L T t t') (e : AlignmentAddingPair n i)
    (he : e.targetTail = T) :
    alignmentIntegerNumerator q₀ w e t = alignmentIntegerNumerator q₀ w e t' := by
  have hsource : alignmentNaturalBlockProduct t (alignmentPairSourceBlock e) =
      alignmentNaturalBlockProduct t' (alignmentPairSourceBlock e) := by
    apply alignmentNaturalBlockProduct_congr
    intro j hj
    apply h.1 j (alignmentPair_source_before e j hj)
    rw [← he]
    exact Finset.disjoint_left.mp (alignmentPair_source_disjoint_tail e) hj
  simp only [alignmentIntegerNumerator, hsource]

end Hindman168
