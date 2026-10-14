import Hindman168.CopiedReplicaCubeEvaluations

/-!
# Concrete prediction row copies at every duplication stage

A stage records which directions have already been duplicated. All other
branches are false. The row's own zero-response branch is still false.
Inserting that direction leaves its outside copies unchanged. For every
other base row, the new true branches are produced by updating exactly
that direction; old copies are recovered by resetting it to false.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def predictionStageCopies {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) : Finset (CopiedReplicaCubeRow dir) :=
  Finset.univ.filter (fun r => ∀ i, i ∉ K → r.val.2 i = false)

noncomputable def predictionStageRowCopies {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (base : ReplicaCubeRow b d) :
    Finset (CopiedReplicaCubeRow dir) :=
  (predictionStageCopies dir K).filter (fun r => r.val.1 = base)

theorem mem_predictionStageCopies {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (r : CopiedReplicaCubeRow dir) :
    r ∈ predictionStageCopies dir K ↔ ∀ i, i ∉ K → r.val.2 i = false := by
  simp only [predictionStageCopies, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_predictionStageRowCopies {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (base : ReplicaCubeRow b d)
    (r : CopiedReplicaCubeRow dir) :
    r ∈ predictionStageRowCopies dir K base ↔
      (∀ i, i ∉ K → r.val.2 i = false) ∧ r.val.1 = base := by
  simp only [predictionStageRowCopies, Finset.mem_filter, mem_predictionStageCopies]

theorem predictionStageCopies_univ {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) : predictionStageCopies dir Finset.univ = Finset.univ := by
  ext r
  simp only [mem_predictionStageCopies, Finset.mem_univ, not_true_eq_false,
    IsEmpty.forall_iff, implies_true]

theorem predictionStageCopies_mono {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) {K L : Finset (Fin h)} (hKL : K ⊆ L) :
    predictionStageCopies dir K ⊆ predictionStageCopies dir L := by
  intro r hr
  apply (mem_predictionStageCopies dir L r).mpr
  intro i hi
  exact (mem_predictionStageCopies dir K r).mp hr i (fun hk => hi (hKL hk))

theorem predictionStageRowCopies_insert_own {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h) :
    predictionStageRowCopies dir (insert k K) (some (dir k)) =
      predictionStageRowCopies dir K (some (dir k)) := by
  ext r
  simp only [mem_predictionStageRowCopies]
  constructor
  · rintro ⟨hstage, hbase⟩
    refine ⟨?_, hbase⟩
    intro i hi
    by_cases hik : i = k
    · subst i
      exact r.property k hbase
    · exact hstage i (by simp only [Finset.mem_insert, not_or]; exact ⟨hik, hi⟩)
  · rintro ⟨hstage, hbase⟩
    refine ⟨?_, hbase⟩
    intro i hi
    exact hstage i (fun hK => hi (Finset.mem_insert_of_mem hK))

noncomputable def predictionSetCopyBranch {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k)) : CopiedReplicaCubeRow dir :=
  ⟨(r.val.1, Function.update r.val.2 k bit), by
    intro i hi
    by_cases hik : i = k
    · subst i
      exact False.elim (ha hi)
    · simpa only [Function.update_of_ne hik] using r.property i hi⟩

theorem predictionSetCopyBranch_base {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k)) :
    (predictionSetCopyBranch dir k bit r ha).val.1 = r.val.1 := rfl

theorem predictionSetCopyBranch_choice {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k)) :
    (predictionSetCopyBranch dir k bit r ha).val.2 k = bit := by
  simp only [predictionSetCopyBranch, Function.update_self]

theorem predictionSetCopyBranch_choice_ne {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k i : Fin h) (hik : i ≠ k) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k)) :
    (predictionSetCopyBranch dir k bit r ha).val.2 i = r.val.2 i := by
  simp only [predictionSetCopyBranch, Function.update_of_ne hik]

theorem predictionSetCopyBranch_id {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (r : CopiedReplicaCubeRow dir)
    (ha : r.val.1 ≠ some (dir k)) : predictionSetCopyBranch dir k (r.val.2 k) r ha = r := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  exact Function.update_eq_self k r.val.2

theorem predictionSetCopyBranch_twice {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (bit bit' : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k)) :
    predictionSetCopyBranch dir k bit'
      (predictionSetCopyBranch dir k bit r ha) ha = predictionSetCopyBranch dir k bit' r ha := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  change Function.update (Function.update r.val.2 k bit) k bit' =
    Function.update r.val.2 k bit'
  funext i
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hi]

theorem predictionSetCopyBranch_stage {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k))
    (hr : r ∈ predictionStageCopies dir K) :
    predictionSetCopyBranch dir k bit r ha ∈ predictionStageCopies dir (insert k K) := by
  apply (mem_predictionStageCopies dir _ _).mpr
  intro i hi
  have hik : i ≠ k := fun he => hi (he.symm ▸ Finset.mem_insert_self k K)
  rw [predictionSetCopyBranch_choice_ne dir k i hik bit r ha]
  exact (mem_predictionStageCopies dir K r).mp hr i (fun hK => hi (Finset.mem_insert_of_mem hK))

theorem predictionResetCopyBranch_stage {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k))
    (hr : r ∈ predictionStageCopies dir (insert k K)) :
    predictionSetCopyBranch dir k false r ha ∈ predictionStageCopies dir K := by
  apply (mem_predictionStageCopies dir _ _).mpr
  intro i hi
  by_cases hik : i = k
  · subst i
    exact predictionSetCopyBranch_choice dir k false r ha
  · rw [predictionSetCopyBranch_choice_ne dir k i hik false r ha]
    exact (mem_predictionStageCopies dir _ r).mp hr i (by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hik, hi⟩)

end Hindman168
