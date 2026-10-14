import Hindman168.PredictionStageCopies

/-!
# Exact duplication of every responsive prediction row

For a fresh direction, its own copies remain outside. Every other base row
has exactly two new copies for each old copy. The bijection is explicit:
set the fresh branch to the Boolean label, and invert by reading that label
and resetting the branch to false. This also identifies products of actual
row factors, without counting a zero-response duplicate twice.
-/

namespace Hindman168

open scoped BigOperators Classical

noncomputable def predictionStageBranchLift {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k)) (bit : Bool)
    (r : ↥(predictionStageRowCopies dir K base)) :
    ↥(predictionStageRowCopies dir (insert k K) base) := by
  have hr := (mem_predictionStageRowCopies dir K base r.val).mp r.property
  have har : r.val.val.1 ≠ some (dir k) := fun he => ha (hr.2.symm.trans he)
  refine ⟨predictionSetCopyBranch dir k bit r.val har, ?_⟩
  apply (mem_predictionStageRowCopies dir _ base _).mpr
  exact ⟨(mem_predictionStageCopies dir _ _).mp
    (predictionSetCopyBranch_stage dir K k bit r.val har
      ((mem_predictionStageCopies dir K r.val).mpr hr.1)), hr.2⟩

noncomputable def predictionStageBranchReset {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k))
    (r : ↥(predictionStageRowCopies dir (insert k K) base)) :
    ↥(predictionStageRowCopies dir K base) := by
  have hr := (mem_predictionStageRowCopies dir _ base r.val).mp r.property
  have har : r.val.val.1 ≠ some (dir k) := fun he => ha (hr.2.symm.trans he)
  refine ⟨predictionSetCopyBranch dir k false r.val har, ?_⟩
  apply (mem_predictionStageRowCopies dir K base _).mpr
  exact ⟨(mem_predictionStageCopies dir K _).mp
    (predictionResetCopyBranch_stage dir K k r.val har
      ((mem_predictionStageCopies dir _ r.val).mpr hr.1)), hr.2⟩

noncomputable def predictionStageDuplicationEquiv {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (hk : k ∉ K) (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k)) :
    (Bool × ↥(predictionStageRowCopies dir K base)) ≃
      ↥(predictionStageRowCopies dir (insert k K) base) where
  toFun br := predictionStageBranchLift dir K k base ha br.1 br.2
  invFun r := (r.val.val.2 k, predictionStageBranchReset dir K k base ha r)
  left_inv br := by
    rcases br with ⟨bit, r⟩
    apply Prod.ext
    · exact predictionSetCopyBranch_choice dir k bit r.val
        (fun he => ha (((mem_predictionStageRowCopies dir K base r.val).mp r.property).2.symm.trans he))
    · apply Subtype.ext
      dsimp only [predictionStageBranchReset, predictionStageBranchLift]
      rw [predictionSetCopyBranch_twice]
      have hr := (mem_predictionStageRowCopies dir K base r.val).mp r.property
      have he : r.val.val.2 k = false := hr.1 k hk
      rw [← he]
      exact predictionSetCopyBranch_id dir k r.val _
  right_inv r := by
    apply Subtype.ext
    dsimp only [predictionStageBranchReset, predictionStageBranchLift]
    rw [predictionSetCopyBranch_twice]
    exact predictionSetCopyBranch_id dir k r.val _

theorem predictionStageRowCopies_card_insert_active {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (hk : k ∉ K) (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k)) :
    (predictionStageRowCopies dir (insert k K) base).card =
      2 * (predictionStageRowCopies dir K base).card := by
  have he := Fintype.card_congr (predictionStageDuplicationEquiv dir K k hk base ha)
  simpa only [Fintype.card_prod, Fintype.card_bool, Fintype.card_coe] using he.symm

theorem predictionStageBranchLift_false {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (hk : k ∉ K) (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k))
    (r : ↥(predictionStageRowCopies dir K base)) :
    (predictionStageBranchLift dir K k base ha false r).val = r.val := by
  have he := ((mem_predictionStageRowCopies dir K base r.val).mp r.property).1 k hk
  dsimp only [predictionStageBranchLift]
  rw [← he]
  exact predictionSetCopyBranch_id dir k r.val _

theorem predictionStageRowCopies_product_insert_active {b d h : ℕ}
    {R : Type*} [CommMonoid R]
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (hk : k ∉ K) (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k))
    (f : CopiedReplicaCubeRow dir → R) :
    (∏ r : ↥(predictionStageRowCopies dir (insert k K) base), f r.val) =
      (∏ r : ↥(predictionStageRowCopies dir K base), f r.val) *
      (∏ r : ↥(predictionStageRowCopies dir K base),
        f (predictionStageBranchLift dir K k base ha true r).val) := by
  rw [← Fintype.prod_equiv (predictionStageDuplicationEquiv dir K k hk base ha)
    (fun br => f (predictionStageBranchLift dir K k base ha br.1 br.2).val)
    (fun r => f r.val) (fun _ => rfl)]
  simp only [Fintype.prod_prod_type, Fintype.prod_bool,
    predictionStageBranchLift_false dir K k hk base ha]
  exact mul_comm _ _

end Hindman168
