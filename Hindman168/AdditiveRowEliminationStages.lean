import Hindman168.AdditiveRowStageCauchySchwarz

/-!
Each eliminated function is replaced by its majorant. All other factors,
including earlier majorants and the target, are duplicated by actual copies.
-/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical
open FiniteMass

variable {b c : ℕ}

noncomputable def eliminationIntegrand (D : AdditiveRowData b c) (K : Finset (Fin b))
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) : ℝ :=
  ∏ i : ReplicaCubeRow b 1, D.stageFactorProduct K i z (predictionPairValues v)
    (predictionEliminationTest (additiveRowAssigned b) K F Ω i)

theorem eliminationIntegrand_fresh (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (hk : k ∉ K) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand K z v F Ω =
      D.stageFactorProduct K (some (additiveRowAssigned b k)) z (predictionPairValues v)
        (F (some (additiveRowAssigned b k))) *
      D.stageOtherProduct K k z v (predictionEliminationTest (additiveRowAssigned b) K F Ω) := by
  unfold eliminationIntegrand stageOtherProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (some (additiveRowAssigned b k)),
    predictionEliminationTest_fresh _ (additiveRowAssigned_injective b) K k hk]

theorem eliminationIntegrand_next (D : AdditiveRowData b c) (K : Finset (Fin b))
    (k : Fin b) (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ)
    (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand (insert k K) z v F Ω =
      D.stageFactorProduct (insert k K) (some (additiveRowAssigned b k)) z (predictionPairValues v)
        (Ω (some (additiveRowAssigned b k))) *
      D.stageOtherProduct (insert k K) k z v (predictionEliminationTest (additiveRowAssigned b) K F Ω) := by
  unfold eliminationIntegrand stageOtherProduct
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ (some (additiveRowAssigned b k)),
    predictionEliminationTest_insert_own]
  congr 1
  apply Fintype.prod_congr
  intro i
  rw [predictionEliminationTest_insert_ne _ K k F Ω i.val i.property]

theorem elimination_stage_step {α : Type*}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin b → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t) (D : α → AdditiveRowData b c)
    (K : Finset (Fin b)) (k : Fin b) (hk : k ∉ K) (ht : ∀ x, total (ν x k) = 1)
    (z : α → Fin c → ℤ) (F Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ)
    (hbound : ∀ x t, |F x (some (additiveRowAssigned b k)) t| ≤ Ω x (some (additiveRowAssigned b k)) t) :
    |expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
      (fun v => (D x).eliminationIntegrand K (z x) v (F x) (Ω x)))| ^ 2 ≤
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => (D x).stageFactorProduct K (some (additiveRowAssigned b k)) (z x)
          (predictionPairValues v) (Ω x (some (additiveRowAssigned b k))))) *
      expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
        (fun v => (D x).eliminationIntegrand (insert k K) (z x) v (F x) (Ω x))) := by
  simp only [eliminationIntegrand_fresh _ K k hk, eliminationIntegrand_next]
  exact stage_weighted_cauchy_schwarz ρ hρ ν hν D K k hk ht z
    (fun x => F x (some (additiveRowAssigned b k)))
    (fun x => Ω x (some (additiveRowAssigned b k)))
    (fun x => predictionEliminationTest (additiveRowAssigned b) K (F x) (Ω x)) hbound

theorem eliminationIntegrand_flat (D : AdditiveRowData b c) (K : Finset (Fin b))
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand K z v F Ω =
      ∏ r ∈ predictionStageCopies (additiveRowAssigned b) K,
        predictionEliminationTest (additiveRowAssigned b) K F Ω r.val.1
          (D.translatedForm r.val.1 r.val.2 z (predictionPairValues v)) := by
  unfold eliminationIntegrand
  simp_rw [D.stageFactorProduct_eq_prod]
  rw [← Finset.prod_fiberwise (predictionStageCopies (additiveRowAssigned b) K) (fun r => r.val.1)
    (fun r => predictionEliminationTest (additiveRowAssigned b) K F Ω r.val.1
      (D.translatedForm r.val.1 r.val.2 z (predictionPairValues v)))]
  apply Fintype.prod_congr
  intro i
  unfold predictionStageRowCopies
  apply Finset.prod_congr rfl
  intro r hr
  rw [(Finset.mem_filter.mp hr).2]

theorem eliminationIntegrand_terminal_flat (D : AdditiveRowData b c)
    (z : Fin c → ℤ) (v : Fin b → ℤ × ℤ) (F Ω : ReplicaCubeRow b 1 → ℤ → ℝ) :
    D.eliminationIntegrand Finset.univ z v F Ω =
      ∏ r : CopiedReplicaCubeRow (additiveRowAssigned b),
        if r.val.1 = none then F none (D.translatedForm r.val.1 r.val.2 z (predictionPairValues v))
        else Ω r.val.1 (D.translatedForm r.val.1 r.val.2 z (predictionPairValues v)) := by
  rw [D.eliminationIntegrand_flat, predictionStageCopies_univ]
  apply Finset.prod_congr (by ext r; simp)
  intro r _
  cases hb : r.val.1 with
  | none => simp only [predictionEliminationTest_root, ite_true]
  | some i => simp only [predictionEliminationTest_full_nonroot _ (additiveRowAssigned_surjective b),
      Option.some_ne_none, ite_false]

end Hindman168.AdditiveRowData
