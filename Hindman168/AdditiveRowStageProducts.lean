import Hindman168.AdditiveRowTranslations

/-! Exact canonical products at each actual integer-row duplication stage. -/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical

variable {b c : ℕ}

theorem translatedForm_update_own (D : AdditiveRowData b c) (k : Fin b) (η : Fin b → Bool)
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) (t : Bool → ℤ) :
    D.translatedForm (some (additiveRowAssigned b k)) η z (Function.update v k t) =
      D.translatedForm (some (additiveRowAssigned b k)) η z v := by
  unfold translatedForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    simp only [D.response_own, zero_mul]
  · simp only [Function.update_of_ne hi]

theorem translatedForm_update_branch (D : AdditiveRowData b c) (k : Fin b) (bit : Bool)
    (r : CopiedReplicaCubeRow (additiveRowAssigned b)) (ha : r.val.1 ≠ some (additiveRowAssigned b k))
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) :
    D.translatedForm r.val.1 r.val.2 z (Function.update v k (fun _ => v k bit)) =
      D.translatedForm (predictionSetCopyBranch (additiveRowAssigned b) k bit r ha).val.1
        (predictionSetCopyBranch (additiveRowAssigned b) k bit r ha).val.2 z v := by
  unfold translatedForm
  rw [predictionSetCopyBranch_base]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    rw [Function.update_self, predictionSetCopyBranch_choice]
  · rw [Function.update_of_ne hi, predictionSetCopyBranch_choice_ne _ k i hi]

theorem translatedForm_stage_false (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (r : CopiedReplicaCubeRow (additiveRowAssigned b))
    (hr : r ∈ predictionStageCopies (additiveRowAssigned b) K)
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) :
    D.translatedForm r.val.1 r.val.2 z (Function.update v k (fun _ => v k false)) =
      D.translatedForm r.val.1 r.val.2 z v := by
  have he := (mem_predictionStageCopies (additiveRowAssigned b) K r).mp hr k hk
  unfold translatedForm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i = k
  · subst i
    simp only [Function.update_self, he]
  · simp only [Function.update_of_ne hi]

noncomputable def stageFactorProduct {R : Type*} [CommMonoid R] (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (i : ReplicaCubeRow b 1) (z : Fin c → ℤ)
    (v : Fin b → Bool → ℤ) (F : ℤ → R) : R :=
  ∏ r : ↥(predictionStageRowCopies (additiveRowAssigned b) K i),
    F (D.translatedForm r.val.val.1 r.val.val.2 z v)

theorem stageFactorProduct_eq_prod {R : Type*} [CommMonoid R] (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (i : ReplicaCubeRow b 1) (z : Fin c → ℤ)
    (v : Fin b → Bool → ℤ) (F : ℤ → R) :
    D.stageFactorProduct K i z v F =
      ∏ r ∈ predictionStageRowCopies (additiveRowAssigned b) K i,
        F (D.translatedForm r.val.1 r.val.2 z v) :=
  Finset.prod_coe_sort (predictionStageRowCopies (additiveRowAssigned b) K i)
    (fun r => F (D.translatedForm r.val.1 r.val.2 z v))

theorem stageFactorProduct_update_own {R : Type*} [CommMonoid R] (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ)
    (t : Bool → ℤ) (F : ℤ → R) :
    D.stageFactorProduct K (some (additiveRowAssigned b k)) z (Function.update v k t) F =
      D.stageFactorProduct K (some (additiveRowAssigned b k)) z v F := by
  unfold stageFactorProduct
  apply Fintype.prod_congr
  intro r
  have hb := ((mem_predictionStageRowCopies _ K _ r.val).mp r.property).2
  rw [hb, D.translatedForm_update_own]

theorem stageFactorProduct_stage_false {R : Type*} [CommMonoid R] (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (hk : k ∉ K) (i : ReplicaCubeRow b 1)
    (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) (F : ℤ → R) :
    D.stageFactorProduct K i z (Function.update v k (fun _ => v k false)) F =
      D.stageFactorProduct K i z v F := by
  unfold stageFactorProduct
  apply Fintype.prod_congr
  intro r
  exact congrArg F (D.translatedForm_stage_false K k hk r.val
    ((mem_predictionStageCopies _ K r.val).mpr
      ((mem_predictionStageRowCopies _ K i r.val).mp r.property).1) z v)

theorem stageFactorProduct_insert_active {R : Type*} [CommMonoid R] (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (hk : k ∉ K) (i : ReplicaCubeRow b 1)
    (hi : i ≠ some (additiveRowAssigned b k)) (z : Fin c → ℤ)
    (v : Fin b → Bool → ℤ) (F : ℤ → R) :
    D.stageFactorProduct (insert k K) i z v F =
      D.stageFactorProduct K i z (Function.update v k (fun _ => v k false)) F *
      D.stageFactorProduct K i z (Function.update v k (fun _ => v k true)) F := by
  rw [D.stageFactorProduct_stage_false K k hk]
  unfold stageFactorProduct
  rw [predictionStageRowCopies_product_insert_active (additiveRowAssigned b) K k hk i hi
    (fun r => F (D.translatedForm r.val.1 r.val.2 z v))]
  congr 1
  apply Fintype.prod_congr
  intro r
  dsimp only [predictionStageBranchLift]
  rw [← D.translatedForm_update_branch]

theorem stageFactorProduct_insert_own (D : AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct (insert k K) (some (additiveRowAssigned b k)) z v F =
      D.stageFactorProduct K (some (additiveRowAssigned b k)) z v F := by
  unfold stageFactorProduct
  rw [predictionStageRowCopies_insert_own]

theorem stageFactorProduct_abs_le (D : AdditiveRowData b c) (K : Finset (Fin b))
    (i : ReplicaCubeRow b 1) (z : Fin c → ℤ) (v : Fin b → Bool → ℤ)
    (F Ω : ℤ → ℝ) (hbound : ∀ t, |F t| ≤ Ω t) :
    |D.stageFactorProduct K i z v F| ≤ D.stageFactorProduct K i z v Ω := by
  unfold stageFactorProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hbound _)

end Hindman168.AdditiveRowData
