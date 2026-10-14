import Hindman168.AdditiveRowEliminationStages
import Hindman168.PredictionOrderedRecurrence

/-!
Actual ordered stages give a proved recurrence under one original law.
The finite prefactor cap below is computed from the actual prefactors;
its uniform asymptotic bound must still be supplied by linear-forms limits.
-/

namespace Hindman168.AdditiveRowData

open scoped BigOperators Classical
open FiniteMass

variable {b c : ℕ}

noncomputable def orderedAverage {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (F Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) (j : ℕ) : ℝ :=
  expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
    (fun v => (D x).eliminationIntegrand (predictionDirectionPrefix b j) (z x) v (F x) (Ω x)))

noncomputable def orderedPrefactor {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) (k : Fin b) : ℝ :=
  expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
    (fun v => (D x).stageFactorProduct (predictionDirectionPrefix b k.val)
      (some (additiveRowAssigned b k)) (z x) (predictionPairValues v) (Ω x (some (additiveRowAssigned b k)))))

noncomputable def orderedPrefactorCap {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) : ℝ :=
  1 + ∑ k, |orderedPrefactor ρ ν D z Ω k|

theorem ordered_average_step {α : Type*} (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x)
    (ν : α → Fin b → Mass ℤ) (hν : ∀ x i t, 0 ≤ ν x i t)
    (ht : ∀ x i, total (ν x i) = 1) (D : α → AdditiveRowData b c)
    (z : α → Fin c → ℤ) (F Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ)
    (hbound : ∀ x i t, |F x (some (additiveRowAssigned b i)) t| ≤ Ω x (some (additiveRowAssigned b i)) t)
    (k : Fin b) :
    |orderedAverage ρ ν D z F Ω k.val| ^ 2 ≤
      orderedPrefactor ρ ν D z Ω k * orderedAverage ρ ν D z F Ω (k.val + 1) := by
  unfold orderedAverage orderedPrefactor
  rw [predictionDirectionPrefix_succ]
  exact elimination_stage_step ρ hρ ν hν D (predictionDirectionPrefix b k.val) k
    (predictionDirectionPrefix_fresh k) (fun x => ht x k) z F Ω (fun x t => hbound x k t)

theorem orderedPrefactor_nonneg {α : Type*} (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x)
    (ν : α → Fin b → Mass ℤ) (hν : ∀ x i t, 0 ≤ ν x i t)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ)
    (hΩ : ∀ x i t, 0 ≤ Ω x (some (additiveRowAssigned b i)) t) (k : Fin b) :
    0 ≤ orderedPrefactor ρ ν D z Ω k := by
  unfold orderedPrefactor
  apply expectation_nonneg_support ρ _ hρ
  intro x _
  apply expectation_nonneg_support _ _ (piMass_nonneg _ (fun i t => by
    rw [tensor_apply]
    exact mul_nonneg (hν x i t.1) (hν x i t.2)))
  intro v _
  unfold stageFactorProduct
  exact Finset.prod_nonneg (fun _ _ => hΩ x k _)

theorem orderedPrefactorCap_nonneg {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) : 0 ≤ orderedPrefactorCap ρ ν D z Ω := by
  unfold orderedPrefactorCap
  exact add_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => abs_nonneg _))

theorem orderedPrefactor_le_cap {α : Type*} (ρ : Mass α) (ν : α → Fin b → Mass ℤ)
    (D : α → AdditiveRowData b c) (z : α → Fin c → ℤ)
    (Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ) (k : Fin b) :
    orderedPrefactor ρ ν D z Ω k ≤ orderedPrefactorCap ρ ν D z Ω := by
  have h := Finset.single_le_sum (fun i _ => abs_nonneg (orderedPrefactor ρ ν D z Ω i))
    (Finset.mem_univ k)
  exact (le_abs_self _).trans (h.trans (by unfold orderedPrefactorCap; linarith))

theorem ordered_average_power_bound {α : Type*} (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x)
    (ν : α → Fin b → Mass ℤ) (hν : ∀ x i t, 0 ≤ ν x i t)
    (ht : ∀ x i, total (ν x i) = 1) (D : α → AdditiveRowData b c)
    (z : α → Fin c → ℤ) (F Ω : α → ReplicaCubeRow b 1 → ℤ → ℝ)
    (hbound : ∀ x i t, |F x (some (additiveRowAssigned b i)) t| ≤ Ω x (some (additiveRowAssigned b i)) t) :
    |orderedAverage ρ ν D z F Ω 0| ^ (2 ^ b) ≤
      (orderedPrefactorCap ρ ν D z Ω) ^ (2 ^ b - 1) * |orderedAverage ρ ν D z F Ω b| := by
  apply iterated_squared_bound b _ _ (orderedPrefactorCap_nonneg ρ ν D z Ω)
  intro j hj
  let k : Fin b := ⟨j, hj⟩
  have hp := orderedPrefactor_nonneg ρ hρ ν hν D z Ω
    (fun x i t => (abs_nonneg (F x (some (additiveRowAssigned b i)) t)).trans (hbound x i t)) k
  calc
    _ ≤ orderedPrefactor ρ ν D z Ω k * orderedAverage ρ ν D z F Ω (j + 1) :=
      ordered_average_step ρ hρ ν hν ht D z F Ω hbound k
    _ ≤ orderedPrefactor ρ ν D z Ω k * |orderedAverage ρ ν D z F Ω (j + 1)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hp
    _ ≤ _ := mul_le_mul_of_nonneg_right (orderedPrefactor_le_cap ρ ν D z Ω k) (abs_nonneg _)

end Hindman168.AdditiveRowData
