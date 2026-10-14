import Hindman168.PredictionStageDuplication

/-!
# Actual prediction forms at a fresh duplication stage

The assigned base row is independent of both fresh direction samples.
Every old responsive copy uses the false sample. Replacing that sample
by the true sample is exactly the explicit branch-lift operation. Thus
the new stage product is the product of the two old inner factors.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem copiedReplicaCubeForm_update_own {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (η : Fin h → Bool)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) (t : Bool → ℤ) :
    copiedReplicaCubeForm M dir (some (dir k)) η z (Function.update v k t) =
      copiedReplicaCubeForm M dir (some (dir k)) η z v := by
  unfold copiedReplicaCubeForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    have hz := replicaCubeResponseConstant_selected (dir k).1 (dir k).2
    rw [Prod.eta] at hz
    simp only [hz, zero_mul]
  · simp only [Function.update_of_ne hi]

theorem copiedReplicaCubeForm_update_branch {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (k : Fin h) (bit : Bool)
    (r : CopiedReplicaCubeRow dir) (ha : r.val.1 ≠ some (dir k))
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) :
    copiedReplicaCubeForm M dir r.val.1 r.val.2 z
      (Function.update v k (fun _ => v k bit)) =
      copiedReplicaCubeForm M dir (predictionSetCopyBranch dir k bit r ha).val.1
        (predictionSetCopyBranch dir k bit r ha).val.2 z v := by
  unfold copiedReplicaCubeForm
  rw [predictionSetCopyBranch_base]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    rw [Function.update_self, predictionSetCopyBranch_choice]
  · rw [Function.update_of_ne hi, predictionSetCopyBranch_choice_ne dir k i hi]

theorem copiedReplicaCubeForm_stage_false {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (hk : k ∉ K) (r : CopiedReplicaCubeRow dir) (hr : r ∈ predictionStageCopies dir K)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) :
    copiedReplicaCubeForm M dir r.val.1 r.val.2 z
      (Function.update v k (fun _ => v k false)) =
      copiedReplicaCubeForm M dir r.val.1 r.val.2 z v := by
  have he : r.val.2 k = false := (mem_predictionStageCopies dir K r).mp hr k hk
  unfold copiedReplicaCubeForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self, he]
  · simp only [Function.update_of_ne hi]

noncomputable def predictionStageFactorProduct {b d h : ℕ} {R : Type*} [CommMonoid R]
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (base : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ)
    (v : Fin h → Bool → ℤ) (F : ℤ → R) : R :=
  ∏ r : ↥(predictionStageRowCopies dir K base),
    F (copiedReplicaCubeForm M dir r.val.val.1 r.val.val.2 z v)

theorem predictionStageFactorProduct_update_own {b d h : ℕ} {R : Type*} [CommMonoid R]
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ)
    (t : Bool → ℤ) (F : ℤ → R) :
    predictionStageFactorProduct M dir K (some (dir k)) z (Function.update v k t) F =
      predictionStageFactorProduct M dir K (some (dir k)) z v F := by
  unfold predictionStageFactorProduct
  apply Fintype.prod_congr
  intro r
  have hb := ((mem_predictionStageRowCopies dir K _ r.val).mp r.property).2
  rw [hb, copiedReplicaCubeForm_update_own]

theorem predictionStageFactorProduct_stage_false {b d h : ℕ} {R : Type*} [CommMonoid R]
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (hk : k ∉ K) (base : ReplicaCubeRow b d)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) (F : ℤ → R) :
    predictionStageFactorProduct M dir K base z (Function.update v k (fun _ => v k false)) F =
      predictionStageFactorProduct M dir K base z v F := by
  unfold predictionStageFactorProduct
  apply Fintype.prod_congr
  intro r
  rw [copiedReplicaCubeForm_stage_false M dir K k hk r.val
    ((mem_predictionStageCopies dir K r.val).mpr
      ((mem_predictionStageRowCopies dir K base r.val).mp r.property).1)]

theorem predictionStageFactorProduct_insert_active {b d h : ℕ} {R : Type*} [CommMonoid R]
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (hk : k ∉ K) (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k))
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) (F : ℤ → R) :
    predictionStageFactorProduct M dir (insert k K) base z v F =
      predictionStageFactorProduct M dir K base z (Function.update v k (fun _ => v k false)) F *
      predictionStageFactorProduct M dir K base z (Function.update v k (fun _ => v k true)) F := by
  rw [predictionStageFactorProduct_stage_false M dir K k hk]
  unfold predictionStageFactorProduct
  rw [predictionStageRowCopies_product_insert_active dir K k hk base ha
    (fun r => F (copiedReplicaCubeForm M dir r.val.1 r.val.2 z v))]
  congr 1
  apply Fintype.prod_congr
  intro r
  dsimp only [predictionStageBranchLift]
  rw [← copiedReplicaCubeForm_update_branch]

end Hindman168
