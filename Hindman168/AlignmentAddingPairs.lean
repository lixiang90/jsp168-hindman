import Hindman168.AlignmentScaleUpdates

/-! Actual ordered pairs P<C<{j}<{i}. Every pair at the pivot has a
strictly positive inflation exponent, even when C differs from the
update tail T. Its rational scale ratio is transported exactly. -/

namespace Hindman168
open scoped Classical

structure AlignmentAddingPair (n : ℕ) (i : Fin n) where
  sourceTail : Finset (Fin n)
  targetTail : Finset (Fin n)
  sourcePivot : Fin n
  source_nonempty : sourceTail.Nonempty
  target_nonempty : targetTail.Nonempty
  source_before_target : ∀ p ∈ sourceTail, ∀ c ∈ targetTail, p < c
  target_before_sourcePivot : ∀ c ∈ targetTail, c < sourcePivot
  sourcePivot_before : sourcePivot < i

def alignmentPairSourceBlock {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    Finset (Fin n) := insert e.sourcePivot e.sourceTail

def alignmentPairTargetBlock {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    Finset (Fin n) := insert i e.targetTail

def alignmentPairInflationExponent {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) (T : Finset (Fin n)) : ℤ :=
  (alignmentSubsetWeight (alignmentPairSourceBlock e) : ℤ) -
    alignmentSubsetWeight e.targetTail + alignmentSubsetWeight T

theorem alignmentPair_source_before {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    ∀ a ∈ alignmentPairSourceBlock e, a < i := by
  intro a ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact e.sourcePivot_before
  · obtain ⟨c, hc⟩ := e.target_nonempty
    exact (e.source_before_target a ha c hc).trans
      ((e.target_before_sourcePivot c hc).trans e.sourcePivot_before)

theorem alignmentPair_target_before {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i) :
    ∀ c ∈ e.targetTail, c < i :=
  fun c hc => (e.target_before_sourcePivot c hc).trans e.sourcePivot_before

theorem alignmentPairInflationExponent_positive {n : ℕ} {i : Fin n}
    (e : AlignmentAddingPair n i) (T : Finset (Fin n)) :
    0 < alignmentPairInflationExponent e T := by
  obtain ⟨p, hp⟩ := e.source_nonempty
  have hweight := alignmentSubsetWeight_separation (alignmentPairSourceBlock e)
    e.targetTail p (Finset.mem_insert_of_mem hp) (e.source_before_target p hp)
  unfold alignmentPairInflationExponent
  omega

theorem alignmentPair_ratio_update {n : ℕ} {i : Fin n} (e : AlignmentAddingPair n i)
    (T : Finset (Fin n)) (k : ℕ) (hk : 0 < k) (b : Fin n → ℚ) :
    finiteScaleBlockProduct (alignmentScaleUpdate i T k b) (alignmentPairSourceBlock e) /
      finiteScaleBlockProduct (alignmentScaleUpdate i T k b) (alignmentPairTargetBlock e) =
    (finiteScaleBlockProduct b (alignmentPairSourceBlock e) /
      finiteScaleBlockProduct b (alignmentPairTargetBlock e)) *
      (k : ℚ) ^ alignmentPairInflationExponent e T := by
  have hkQ : (k : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  rw [alignmentScaleUpdate_product, alignmentScaleUpdate_product]
  rw [alignmentMultiplier_before_product i T _ k hk (alignmentPair_source_before e)]
  rw [alignmentPairTargetBlock,
    alignmentMultiplier_pivot_product i T e.targetTail k hk (alignmentPair_target_before e)]
  rw [mul_div_mul_comm, ← zpow_sub₀ hkQ]
  congr 1
  unfold alignmentPairInflationExponent
  congr 1
  ring

end Hindman168
