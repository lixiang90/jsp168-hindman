import Hindman168.AdditiveRowStageProducts

/-! Exact weighted squaring for the actual integer-row evaluations. -/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical
open FiniteMass

variable {b c : ℕ}

theorem stagePairProduct_own (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct K (some (additiveRowAssigned b k)) z
      (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) (0, 0))) F =
      D.stageFactorProduct K (some (additiveRowAssigned b k)) z (predictionPairValues v) F := by
  rw [predictionPairValues_insert_constant, D.stageFactorProduct_update_own]

theorem stagePairProduct_old (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (i : ReplicaCubeRow b 1)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct K i z
      (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1))) F =
      D.stageFactorProduct K i z (predictionPairValues v) F := by
  rw [predictionPairValues_insert_constant]
  exact D.stageFactorProduct_stage_false K k hk i z (predictionPairValues v) F

theorem stagePairProduct_new (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (i : ReplicaCubeRow b 1) (hi : i ≠ some (additiveRowAssigned b k))
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F : ℤ → ℝ) :
    D.stageFactorProduct (insert k K) i z (predictionPairValues v) F =
      D.stageFactorProduct K i z
        (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1))) F *
      D.stageFactorProduct K i z
        (predictionPairValues (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2))) F := by
  simp only [predictionPairValues_insert_constant]
  exact D.stageFactorProduct_insert_active K k hk i hi z (predictionPairValues v) F

noncomputable def stageOtherProduct (D : AdditiveRowData b c) (K : Finset (Fin b)) (k : Fin b)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (G : ReplicaCubeRow b 1 → ℤ → ℝ) : ℝ :=
  ∏ i : {r : ReplicaCubeRow b 1 // r ≠ some (additiveRowAssigned b k)},
    D.stageFactorProduct K i.val z (predictionPairValues v) (G i.val)

theorem stageOtherProduct_old (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ)
    (G : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.stageOtherProduct K k z (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) G =
      D.stageOtherProduct K k z v G := by
  unfold stageOtherProduct
  exact Fintype.prod_congr _ _ (fun i => D.stagePairProduct_old K k hk i.val z v (G i.val))

theorem stageOtherProduct_new (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ)
    (G : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.stageOtherProduct (insert k K) k z v G =
      D.stageOtherProduct K k z (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) G *
      D.stageOtherProduct K k z (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2)) G := by
  unfold stageOtherProduct
  rw [← Finset.prod_mul_distrib]
  exact Fintype.prod_congr _ _ (fun i => D.stagePairProduct_new K k hk i.val i.property z v (G i.val))

theorem stage_weighted_cauchy_schwarz {α : Type*}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin b → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t) (D : α → AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (hk : k ∉ K) (ht : ∀ x, total (ν x k) = 1)
    (z : α → Fin c → ℤ) (F Ω : α → ℤ → ℝ) (G : α → ReplicaCubeRow b 1 → ℤ → ℝ)
    (hbound : ∀ x t, |F x t| ≤ Ω x t) :
    |expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
      (fun v => (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x)
        (predictionPairValues v) (F x) * (D x).stageOtherProduct K k (z x) v (G x)))| ^ 2 ≤
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x)
          (predictionPairValues v) (Ω x))) *
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => (D x).stageFactorProduct (insert k K) (some (additiveRowAssigned b k)) (z x)
          (predictionPairValues v) (Ω x) * (D x).stageOtherProduct (insert k K) k (z x) v (G x))) := by
  have hcs := full_pair_pivot_weighted_cauchy_schwarz ρ hρ ν hν k ht
    (fun x rest => (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (F x))
    (fun x rest => (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (Ω x))
    (fun x rest t => (D x).stageOtherProduct K k (z x) (insertPivotCoordinate k rest (t, t)) (G x))
    (fun x rest => (D x).stageFactorProduct_abs_le K (some (additiveRowAssigned b k)) (z x)
      (predictionPairValues (insertPivotCoordinate k rest (0, 0))) (F x) (Ω x) (hbound x))
  have he (x : α) (v : Fin b → ℤ × ℤ) :
      (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x) (predictionPairValues v) (Ω x) *
        (D x).stageOtherProduct K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) (G x) *
        (D x).stageOtherProduct K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).2, (v k).2)) (G x) =
      (D x).stageFactorProduct (insert k K) (some (additiveRowAssigned b k)) (z x)
        (predictionPairValues v) (Ω x) * (D x).stageOtherProduct (insert k K) k (z x) v (G x) := by
    rw [(D x).stageFactorProduct_insert_own, (D x).stageOtherProduct_new K k hk]
    exact mul_assoc _ _ _
  simp only [stagePairProduct_own, he] at hcs
  have hold (x : α) (v : Fin b → ℤ × ℤ) :
      (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x) (predictionPairValues v) (F x) *
        (D x).stageOtherProduct K k (z x)
          (insertPivotCoordinate k (fun i => v i.val) ((v k).1, (v k).1)) (G x) =
      (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x) (predictionPairValues v) (F x) *
        (D x).stageOtherProduct K k (z x) v (G x) := by
    rw [(D x).stageOtherProduct_old K k hk]
  simpa only [hold] using hcs

end Hindman168.AdditiveRowData
