import Hindman168.PredictionStageCauchySchwarz

/-!
# Ordered prediction elimination stages

A processed nonroot row uses its retained majorant, and every other row
still uses its original test. A fresh direction changes only its assigned
row's test. Consequently the concrete duplication step compares the full
old stage and full next stage, with earlier weights retained exactly once
per canonical copy.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionEliminationTest {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) (base : ReplicaCubeRow b d) : ℤ → ℝ :=
  if base ∈ K.image (fun i => some (dir i)) then Ω base else F base

theorem predictionEliminationTest_fresh {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Injective dir)
    (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationTest dir K F Ω (some (dir k)) = F (some (dir k)) := by
  unfold predictionEliminationTest
  apply if_neg
  rintro hmem
  obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hmem
  have hik : i = k := hdir (Option.some.inj he)
  exact hk (hik ▸ hi)

theorem predictionEliminationTest_insert_own {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationTest dir (insert k K) F Ω (some (dir k)) = Ω (some (dir k)) := by
  unfold predictionEliminationTest
  apply if_pos
  exact Finset.mem_image.mpr ⟨k, Finset.mem_insert_self k K, rfl⟩

theorem predictionEliminationTest_insert_ne {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h)) (k : Fin h)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) (base : ReplicaCubeRow b d)
    (hb : base ≠ some (dir k)) :
    predictionEliminationTest dir (insert k K) F Ω base =
      predictionEliminationTest dir K F Ω base := by
  unfold predictionEliminationTest
  simp only [Finset.image_insert, Finset.mem_insert, hb, false_or]

theorem predictionEliminationTest_root {b d h : ℕ}
    (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationTest dir K F Ω none = F none := by
  unfold predictionEliminationTest
  apply if_neg
  simp only [Finset.mem_image, Option.some_ne_none, and_false, exists_false, not_false_eq_true]

noncomputable def predictionEliminationIntegrand {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (K : Finset (Fin h))
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) : ℝ :=
  ∏ base : ReplicaCubeRow b d, predictionStageFactorProduct M dir K base z
    (predictionPairValues v) (predictionEliminationTest dir K F Ω base)

theorem predictionEliminationIntegrand_fresh {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Injective dir)
    (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationIntegrand M dir K z v F Ω =
      predictionStageFactorProduct M dir K (some (dir k)) z (predictionPairValues v)
        (F (some (dir k))) *
      predictionStageOtherProduct M dir K k z v (predictionEliminationTest dir K F Ω) := by
  unfold predictionEliminationIntegrand predictionStageOtherProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (some (dir k)),
    predictionEliminationTest_fresh dir hdir K k hk]

theorem predictionEliminationIntegrand_next {b d h : ℕ}
    (M : Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (K : Finset (Fin h)) (k : Fin h)
    (z : ReplicaCubeColumn b d → ℤ) (v : Fin h → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b d → ℤ → ℝ) :
    predictionEliminationIntegrand M dir (insert k K) z v F Ω =
      predictionStageFactorProduct M dir (insert k K) (some (dir k)) z (predictionPairValues v)
        (Ω (some (dir k))) *
      predictionStageOtherProduct M dir (insert k K) k z v (predictionEliminationTest dir K F Ω) := by
  unfold predictionEliminationIntegrand predictionStageOtherProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (some (dir k)), predictionEliminationTest_insert_own]
  congr 1
  apply Fintype.prod_congr
  intro base
  rw [predictionEliminationTest_insert_ne dir K k F Ω base.val base.property]

theorem prediction_elimination_stage_step {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t)
    (M : α → Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Injective dir)
    (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K) (ht : ∀ x, total (ν x k) = 1)
    (z : α → ReplicaCubeColumn b d → ℤ)
    (F Ω : α → ReplicaCubeRow b d → ℤ → ℝ)
    (hbound : ∀ x t, |F x (some (dir k)) t| ≤ Ω x (some (dir k)) t) :
    |expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
      (fun v => predictionEliminationIntegrand (M x) dir K (z x) v (F x) (Ω x)))| ^ 2 ≤
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => predictionStageFactorProduct (M x) dir K (some (dir k)) (z x)
          (predictionPairValues v) (Ω x (some (dir k))))) *
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => predictionEliminationIntegrand (M x) dir (insert k K) (z x) v (F x) (Ω x))) := by
  simp only [predictionEliminationIntegrand_fresh _ dir hdir K k hk,
    predictionEliminationIntegrand_next]
  exact prediction_stage_weighted_cauchy_schwarz ρ hρ ν hν M dir K k hk ht z
    (fun x => F x (some (dir k))) (fun x => Ω x (some (dir k)))
    (fun x => predictionEliminationTest dir K (F x) (Ω x)) hbound

end Hindman168
