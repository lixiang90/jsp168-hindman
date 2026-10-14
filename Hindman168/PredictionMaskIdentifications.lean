import Hindman168.PredictionStageProducts
import Hindman168.MasterPredictionSampling

/-!
# Exact original divisor-mask factors at every prediction stage

The full coordinate encoding evaluates each canonical copied form exactly.
A prefactor is precisely the subset of its assigned base row's stage
copies. The terminal integrand is precisely the full enumerated root-
difference times retained-majorant product, with the original per-base
row divisor masses.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionEnumeratedMask {b d h : ℕ}
    (D : ReplicaCubeRow b d → Mass ℕ) (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d)
    (u : Fin (Fintype.card (CopiedReplicaCubeRow dir)))
    (y : Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ) : ℝ :=
  integerDivisorMask (D (copiedPredictionRowEnumeration dir u).val.1)
    (∑ j, copiedReplicaCubeFinCoefficient M dir (copiedPredictionRowEnumeration dir u) j * y j)

theorem prediction_prefactor_mask_identification {b d h : ℕ}
    (D : ReplicaCubeRow b d → Mass ℕ) (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (base : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) :
    predictionStageFactorProduct M dir K base z (predictionPairValues v)
      (fun t => 1 + integerDivisorMask (D base) t) =
      ∏ u ∈ copiedPredictionStageRowIndices dir K base,
        (1 + predictionEnumeratedMask D M dir u (predictionSampleCoordinates z v)) := by
  rw [predictionStageFactorProduct_enumerated]
  apply Finset.prod_congr rfl
  intro u hu
  have hb := ((mem_predictionStageRowCopies dir K base _).mp (Finset.mem_filter.mp hu).2).2
  unfold predictionEnumeratedMask
  rw [predictionSampleCoordinates_eval, hb]

theorem copiedPredictionRootIndices_eq_filter {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) :
    copiedPredictionRootIndices dir = Finset.univ.filter
      (fun u => (copiedPredictionRowEnumeration dir u).val.1 = none) := by
  ext u
  simp only [mem_copiedPredictionRootIndices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem prediction_terminal_mask_identification {b d h : ℕ}
    (D : ReplicaCubeRow b d → Mass ℕ) (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Surjective dir)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F : ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : F none = fun t => integerDivisorMask (D none) t - 1) :
    predictionEliminationIntegrand M dir Finset.univ z v F
      (fun base t => 1 + integerDivisorMask (D base) t) =
      (∏ u ∈ copiedPredictionRootIndices dir,
        (predictionEnumeratedMask D M dir u (predictionSampleCoordinates z v) - 1)) *
      ∏ u ∈ copiedPredictionRetainedIndices dir,
        (1 + predictionEnumeratedMask D M dir u (predictionSampleCoordinates z v)) := by
  rw [predictionEliminationIntegrand_terminal_flat M dir hdir z v _ F hroot]
  have he := Fintype.prod_equiv (Fintype.equivFin (CopiedReplicaCubeRow dir)).symm
    (fun u => if (copiedPredictionRowEnumeration dir u).val.1 = none then
      predictionEnumeratedMask D M dir u (predictionSampleCoordinates z v) - 1
      else 1 + predictionEnumeratedMask D M dir u (predictionSampleCoordinates z v))
    (fun r => if r.val.1 = none then
      integerDivisorMask (D r.val.1)
        (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)) - 1
      else 1 + integerDivisorMask (D r.val.1)
        (copiedReplicaCubeForm M dir r.val.1 r.val.2 z (predictionPairValues v)))
    (fun _ => by simp only [predictionEnumeratedMask, predictionSampleCoordinates_eval]; rfl)
  rw [← he, Finset.prod_ite, copiedPredictionRootIndices_eq_filter]
  rfl

end Hindman168
