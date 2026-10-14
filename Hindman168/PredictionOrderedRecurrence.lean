import Hindman168.PredictionEliminationStages
import Hindman168.IteratedWeightedSquares

/-!
# The actual ordered prediction recurrence

A prefix consists of exactly the earlier enumerated directions. At each
fresh direction the full next integrand is the next prefix stage. Thus
the concrete finite laws give an ordered squaring recurrence, rather than
an assumed list of abstract Cauchy--Schwarz applications.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def predictionDirectionPrefix (h j : ℕ) : Finset (Fin h) :=
  Finset.univ.filter (fun i => i.val < j)

theorem mem_predictionDirectionPrefix (h j : ℕ) (i : Fin h) :
    i ∈ predictionDirectionPrefix h j ↔ i.val < j := by
  simp only [predictionDirectionPrefix, Finset.mem_filter, Finset.mem_univ, true_and]

theorem predictionDirectionPrefix_zero (h : ℕ) : predictionDirectionPrefix h 0 = ∅ := by
  ext i
  simp [mem_predictionDirectionPrefix]

theorem predictionDirectionPrefix_full (h : ℕ) : predictionDirectionPrefix h h = Finset.univ := by
  ext i
  simp only [mem_predictionDirectionPrefix, Finset.mem_univ, iff_true]
  exact i.isLt

theorem predictionDirectionPrefix_fresh {h : ℕ} (k : Fin h) :
    k ∉ predictionDirectionPrefix h k.val := by
  simp only [mem_predictionDirectionPrefix, lt_self_iff_false, not_false_eq_true]

theorem predictionDirectionPrefix_succ {h : ℕ} (k : Fin h) :
    predictionDirectionPrefix h (k.val + 1) = insert k (predictionDirectionPrefix h k.val) := by
  ext i
  simp only [mem_predictionDirectionPrefix, Finset.mem_insert, Fin.ext_iff]
  omega

noncomputable def predictionOrderedAverage {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (ν : α → Fin h → Mass ℤ) (M : α → Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (z : α → ReplicaCubeColumn b d → ℤ)
    (F Ω : α → ReplicaCubeRow b d → ℤ → ℝ) (j : ℕ) : ℝ :=
  expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
    (fun v => predictionEliminationIntegrand (M x) dir (predictionDirectionPrefix h j)
      (z x) v (F x) (Ω x)))

noncomputable def predictionOrderedPrefactor {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (ν : α → Fin h → Mass ℤ) (M : α → Fin b → ℤ)
    (dir : Fin h → Fin b × CubeVertex d) (z : α → ReplicaCubeColumn b d → ℤ)
    (Ω : α → ReplicaCubeRow b d → ℤ → ℝ) (k : Fin h) : ℝ :=
  expectation ρ (fun x => expectation (piMass (fun i => tensor (ν x i) (ν x i)))
    (fun v => predictionStageFactorProduct (M x) dir (predictionDirectionPrefix h k.val)
      (some (dir k)) (z x) (predictionPairValues v) (Ω x (some (dir k)))))

theorem prediction_ordered_average_step {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t) (ht : ∀ x i, total (ν x i) = 1)
    (M : α → Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Injective dir)
    (z : α → ReplicaCubeColumn b d → ℤ)
    (F Ω : α → ReplicaCubeRow b d → ℤ → ℝ)
    (hbound : ∀ x i t, |F x (some (dir i)) t| ≤ Ω x (some (dir i)) t) (k : Fin h) :
    |predictionOrderedAverage ρ ν M dir z F Ω k.val| ^ 2 ≤
      predictionOrderedPrefactor ρ ν M dir z Ω k *
      predictionOrderedAverage ρ ν M dir z F Ω (k.val + 1) := by
  unfold predictionOrderedAverage predictionOrderedPrefactor
  rw [predictionDirectionPrefix_succ]
  exact prediction_elimination_stage_step ρ hρ ν hν M dir hdir
    (predictionDirectionPrefix h k.val) k (predictionDirectionPrefix_fresh k)
    (fun x => ht x k) z F Ω (fun x t => hbound x k t)


theorem predictionOrderedPrefactor_nonneg {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t)
    (M : α → Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (z : α → ReplicaCubeColumn b d → ℤ)
    (Ω : α → ReplicaCubeRow b d → ℤ → ℝ) (hΩ : ∀ x i t, 0 ≤ Ω x (some (dir i)) t)
    (k : Fin h) : 0 ≤ predictionOrderedPrefactor ρ ν M dir z Ω k := by
  unfold predictionOrderedPrefactor
  apply expectation_nonneg_support ρ _ hρ
  intro x _
  apply expectation_nonneg_support _ _ (piMass_nonneg _ (fun i t => by
    rw [tensor_apply]
    exact mul_nonneg (hν x i t.1) (hν x i t.2)))
  intro v _
  unfold predictionStageFactorProduct
  exact Finset.prod_nonneg (fun _ _ => hΩ x k _)

theorem prediction_ordered_average_power_bound {α : Type*} {b d h : ℕ}
    (ρ : Mass α) (hρ : ∀ x, 0 ≤ ρ x) (ν : α → Fin h → Mass ℤ)
    (hν : ∀ x i t, 0 ≤ ν x i t) (ht : ∀ x i, total (ν x i) = 1)
    (M : α → Fin b → ℤ) (dir : Fin h → Fin b × CubeVertex d) (hdir : Function.Injective dir)
    (z : α → ReplicaCubeColumn b d → ℤ)
    (F Ω : α → ReplicaCubeRow b d → ℤ → ℝ)
    (hbound : ∀ x i t, |F x (some (dir i)) t| ≤ Ω x (some (dir i)) t)
    (C : ℝ) (hC : 0 ≤ C)
    (hcap : ∀ k, predictionOrderedPrefactor ρ ν M dir z Ω k ≤ C) :
    |predictionOrderedAverage ρ ν M dir z F Ω 0| ^ (2 ^ h) ≤
      C ^ (2 ^ h - 1) * |predictionOrderedAverage ρ ν M dir z F Ω h| := by
  apply iterated_squared_bound h _ C hC
  intro i hi
  let k : Fin h := ⟨i, hi⟩
  have hp := predictionOrderedPrefactor_nonneg ρ hρ ν hν M dir z Ω
    (fun x j t => (abs_nonneg (F x (some (dir j)) t)).trans (hbound x j t)) k
  calc
    _ ≤ predictionOrderedPrefactor ρ ν M dir z Ω k *
        predictionOrderedAverage ρ ν M dir z F Ω (i + 1) :=
      prediction_ordered_average_step ρ hρ ν hν ht M dir hdir z F Ω hbound k
    _ ≤ predictionOrderedPrefactor ρ ν M dir z Ω k *
        |predictionOrderedAverage ρ ν M dir z F Ω (i + 1)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hp
    _ ≤ C * |predictionOrderedAverage ρ ν M dir z F Ω (i + 1)| :=
      mul_le_mul_of_nonneg_right (hcap k) (abs_nonneg _)

end Hindman168
