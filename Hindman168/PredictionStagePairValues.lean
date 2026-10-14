import Hindman168.PredictionStageEvaluations
import Hindman168.FinitePivotCoordinates

/-!
# Direction pairs and the concrete stage factors

The first component is the false branch, the second the true branch.
At a fresh stage the old product uses only the first component. The new
responsive product uses the two independently evaluated old products.
The outside assigned product depends on neither component.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

def predictionPairValues {h : ℕ} (v : Fin h → ℤ × ℤ) (i : Fin h) (bit : Bool) : ℤ :=
  if bit then (v i).2 else (v i).1

theorem predictionPairValues_insert_constant {h : ℕ} (k : Fin h)
    (v : Fin h → ℤ × ℤ) (t : ℤ) :
    predictionPairValues (insertPivotCoordinate k (fun i => v i.val) (t, t)) =
      Function.update (predictionPairValues v) k (fun _ => t) := by
  funext i bit
  by_cases hi : i = k
  · subst i
    rw [Function.update_self]
    simp [predictionPairValues, insertPivotCoordinate_self]
  · rw [Function.update_of_ne hi]
    simp only [predictionPairValues, insertPivotCoordinate, dif_neg hi]

theorem predictionStagePairProduct_own {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir K (some (dir k)) z
      (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) (0, 0))) F =
      predictionStageFactorProduct M dir K (some (dir k)) z (predictionPairValues v) F := by
  rw [predictionPairValues_insert_constant, predictionStageFactorProduct_update_own]

theorem predictionStagePairProduct_old {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K)
    (base : ReplicaCubeRow b d) (z : ReplicaCubeColumn b d → ℤ)
    (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir K base z
      (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1))) F =
      predictionStageFactorProduct M dir K base z (predictionPairValues v) F := by
  rw [predictionPairValues_insert_constant]
  exact predictionStageFactorProduct_stage_false M dir K k hk base z (predictionPairValues v) F

theorem predictionStagePairProduct_new {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K)
    (base : ReplicaCubeRow b d) (ha : base ≠ some (dir k))
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir (insert k K) base z (predictionPairValues v) F =
      predictionStageFactorProduct M dir K base z
        (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1))) F *
      predictionStageFactorProduct M dir K base z
        (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2))) F := by
  simp only [predictionPairValues_insert_constant]
  exact predictionStageFactorProduct_insert_active M dir K k hk base ha z
    (predictionPairValues v) F

theorem predictionStageFactorProduct_abs_le {b d h : ℕ} (M : Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (base : ReplicaCubeRow b d)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ)
    (F Ω : ℤ → ℝ) (hbound : ∀ t, |F t| ≤ Ω t) :
    |predictionStageFactorProduct M dir K base z v F| ≤
      predictionStageFactorProduct M dir K base z v Ω := by
  unfold predictionStageFactorProduct
  rw [Finset.abs_prod]
  exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun _ _ => hbound _)

end Hindman168
