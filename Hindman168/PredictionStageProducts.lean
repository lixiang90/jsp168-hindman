import Hindman168.PredictionEliminationStages
import Hindman168.PredictionTerminalCopies

/-!
# Flat canonical products and the actual ordered terminal stage

Grouping row copies by their original base row is exactly a finite fiber
product. At the terminal stage every canonical copy is present. The
surjective direction list changes every nonroot test to its retained
majorant while leaving every root difference centered.
-/

namespace Hindman168

open scoped BigOperators Classical

theorem predictionStageFactorProduct_eq_prod {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (base : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ)
    (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir K base z (predictionPairValues v) F =
      ∏ r ∈ predictionStageRowCopies dir K base,
        F (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)) :=
  Finset.prod_coe_sort (predictionStageRowCopies dir K base)
    (fun r => F (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)))

theorem predictionEliminationIntegrand_flat {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationIntegrand M dir K z v F Ω =
      ∏ r ∈ predictionStageCopies dir K,
        predictionEliminationTest dir K F Ω r.val.1
          (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)) := by
  unfold predictionEliminationIntegrand
  simp_rw [predictionStageFactorProduct_eq_prod]
  rw [← Finset.prod_fiberwise (predictionStageCopies dir K) (fun r => r.val.1)
    (fun r => predictionEliminationTest dir K F Ω r.val.1
      (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)))]
  apply Fintype.prod_congr
  intro base
  unfold predictionStageRowCopies
  apply Finset.prod_congr rfl
  intro r hr
  rw [(Finset.mem_filter.mp hr).2]

theorem predictionEliminationTest_full_nonroot {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Surjective dir)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) (base : Fin b × CubeVertex d) :
    predictionEliminationTest dir Finset.univ F Ω (some base) = Ω (some base) := by
  unfold predictionEliminationTest
  apply if_pos
  obtain ⟨i, hi⟩ := hdir base
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg some hi⟩

theorem predictionEliminationIntegrand_terminal_flat {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Surjective dir)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (ν : ReplicaCubeRow b d → ℤ → ℝ) (F : ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : F none = fun t => ν none t - 1) :
    predictionEliminationIntegrand M dir Finset.univ z v F (fun base t => 1 + ν base t) =
      ∏ r : CopiedReplicaCubeRow dir,
        if r.val.1 = none then
          ν r.val.1 (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)) - 1
        else 1 + ν r.val.1 (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)) := by
  rw [predictionEliminationIntegrand_flat, predictionStageCopies_univ]
  apply Fintype.prod_congr
  intro r
  cases hb : r.val.1 with
  | none => simp only [predictionEliminationTest_root, hroot, ite_true]
  | some base => simp only [predictionEliminationTest_full_nonroot dir hdir,
      Option.some_ne_none, ite_false]

noncomputable def copiedPredictionStageRowIndices {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (base : ReplicaCubeRow b d) :
    Finset (Fin (Fintype.card (CopiedReplicaCubeRow dir))) :=
  Finset.univ.filter (fun u => copiedPredictionRowEnumeration dir u ∈ predictionStageRowCopies dir K base)

theorem predictionStageFactorProduct_enumerated {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (base : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ)
    (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir K base z (predictionPairValues v) F =
      ∏ u ∈ copiedPredictionStageRowIndices dir K base,
        F (copiedReplicaCubeForm M dir (copiedPredictionRowEnumeration dir u).val.1
          (copiedPredictionRowEnumeration dir u).val.2 z (predictionPairValues v)) := by
  rw [predictionStageFactorProduct_eq_prod]
  apply Finset.prod_bij (fun r _ => Fintype.equivFin (CopiedReplicaCubeRow dir) r)
  · intro r hr
    simp only [copiedPredictionStageRowIndices, Finset.mem_filter, Finset.mem_univ, true_and,
      copiedPredictionRowEnumeration, Equiv.symm_apply_apply]
    exact hr
  · intro r _ s _ he
    exact (Fintype.equivFin (CopiedReplicaCubeRow dir)).injective he
  · intro u hu
    refine ⟨copiedPredictionRowEnumeration dir u, (Finset.mem_filter.mp hu).2, ?_⟩
    exact (Fintype.equivFin (CopiedReplicaCubeRow dir)).apply_symm_apply u
  · intro r _
    simp only [copiedPredictionRowEnumeration, Equiv.symm_apply_apply]

end Hindman168
