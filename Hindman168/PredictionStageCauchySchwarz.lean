import Hindman168.PredictionStagePairValues
import Hindman168.FinitePivotCauchySchwarz

/-!
# A concrete prediction stage Cauchy--Schwarz step

The assigned row factors are bounded by their actual outside majorants.
Every other base row, including earlier retained weights and the root,
is duplicated by its explicit canonical copy bijection. Both stages and
the prefactor are averaged under the same full independent pair law,
conditional on the original outside parameters.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionStageOtherProduct {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (G : ReplicaCubeRow b d → ℤ → ℝ) : ℝ :=
  ∏ base : {r : ReplicaCubeRow b d // r ≠ some (dir k)},
    predictionStageFactorProduct M dir K base.val z (predictionPairValues v) (G base.val)

theorem predictionStageOtherProduct_old {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (hk : k ∉ K) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (G : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionStageOtherProduct M dir K k z
      (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) G =
      predictionStageOtherProduct M dir K k z v G := by
  unfold predictionStageOtherProduct
  apply Fintype.prod_congr
  intro base
  exact predictionStagePairProduct_old M dir K k hk base.val z v (G base.val)

theorem predictionStageOtherProduct_new {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (hk : k ∉ K) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (G : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionStageOtherProduct M dir (insert k K) k z v G =
      predictionStageOtherProduct M dir K k z
        (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) G *
      predictionStageOtherProduct M dir K k z
        (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2)) G := by
  unfold predictionStageOtherProduct
  rw [← Finset.prod_mul_distrib]
  apply Fintype.prod_congr
  intro base
  exact predictionStagePairProduct_new M dir K k hk base.val base.property z v (G base.val)

theorem predictionStageFactorProduct_insert_own {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (k : Fin h) (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → Bool → ℤ) (F : ℤ → ℝ) :
    predictionStageFactorProduct M dir (insert k K) (some (dir k)) z v F =
      predictionStageFactorProduct M dir K (some (dir k)) z v F := by
  unfold predictionStageFactorProduct
  rw [predictionStageRowCopies_insert_own]

theorem prediction_stage_weighted_cauchy_schwarz {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t)
    (M : α → Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K) (ht : ∀ x, total (ν x k) = 1)
    (z : α → ReplicaCubeColumn b d → ℤ) (F Ω : α → ℤ → ℝ)
    (G : α → ReplicaCubeRow b d → ℤ → ℝ) (hbound : ∀ x t, |F x t| ≤ Ω x t) :
    |expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
      (fun v => predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
        (predictionPairValues v) (F x) * predictionStageOtherProduct (M x) dir K k (z x) v (G x)))| ^ 2 ≤
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
          (predictionPairValues v) (Ω x))) *
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => predictionStageFactorProduct (M x) dir (insert k K) (some (dir k)) (z x)
          (predictionPairValues v) (Ω x) *
          predictionStageOtherProduct (M x) dir (insert k K) k (z x) v (G x))) := by
  have hcs := full_pair_pivot_weighted_cauchy_schwarz ρ hρ ν hν k ht
    (fun x rest => predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (F x))
    (fun x rest => predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (Ω x))
    (fun x rest t => predictionStageOtherProduct (M x) dir K k (z x)
      (insertPivotCoordinate k rest (t, t)) (G x))
    (fun x rest => predictionStageFactorProduct_abs_le (M x) dir K (some (dir k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (F x) (Ω x) (hbound x))
  have he (x : α) (v : Fin h → ℤ × ℤ) :
      predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
          (predictionPairValues v) (Ω x) *
        predictionStageOtherProduct (M x) dir K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) (G x) *
        predictionStageOtherProduct (M x) dir K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2)) (G x) =
      predictionStageFactorProduct (M x) dir (insert k K) (some (dir k)) (z x)
          (predictionPairValues v) (Ω x) *
        predictionStageOtherProduct (M x) dir (insert k K) k (z x) v (G x) := by
    rw [predictionStageFactorProduct_insert_own, predictionStageOtherProduct_new (M x) dir K k hk]
    exact mul_assoc _ _ _
  simp only [predictionStagePairProduct_own, he] at hcs
  have hold (x : α) (v : Fin h → ℤ × ℤ) :
      predictionStageFactorProduct (M x) dir K (some (dir k)) (z x) (predictionPairValues v) (F x) *
        predictionStageOtherProduct (M x) dir K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) (G x) =
      predictionStageFactorProduct (M x) dir K (some (dir k)) (z x) (predictionPairValues v) (F x) *
        predictionStageOtherProduct (M x) dir K k (z x) v (G x) := by
    rw [predictionStageOtherProduct_old (M x) dir K k hk]
  simpa only [hold] using hcs

end Hindman168
