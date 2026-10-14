import Hindman168.MasterPredictionStageMoments
import Hindman168.FiniteEventPairLaw

/-!
# Concrete master-stage squaring under the original prime event

The original prime event is retained with its original mass. Auxiliary
intervals need positive lengths only there. Exact outside-event completion
makes the inside laws probability laws everywhere, without changing any
retained stage average or prefactor.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

theorem master_prediction_stage_step
    {N m r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (gap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (w : ℕ) (K : Finset (Fin h)) (k : Fin h) (hk : k ∉ K)
    (hdir : Function.Injective dir)
    (hprime : ∀ x, 0 ≤ masterPrimeSlotsMass F w (gap w) x)
    (hbase : ∀ x, E w x → ∀ z,
      0 ≤ piMass (masterPredictionOriginalCoordinateMass H F index loc len w x) z)
    (hpos : ∀ x, E w x → ∀ i, 0 < len w x (predictionColumnIndex (.inr (i, false))))
    (hbound : ∀ x t, |G w x (some (dir k)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir k))) t) :
    |masterPredictionStageAverage F C label gap s f dir H index loc len E G w K| ^ 2 ≤
      masterPredictionStagePrefactor F C label gap s f dir H index loc len E w K (some (dir k)) *
      masterPredictionStageAverage F C label gap s f dir H index loc len E G w (insert k K) := by
  let μ := masterPrimeSlotsMass F w (gap w)
  let base (x : Fin r → ℕ) := piMass (masterPredictionOriginalCoordinateMass H F index loc len w x)
  let τ := masterPredictionDirectionMass loc len w
  let χ := conditionalJoint (restrictedMass μ (E w)) base
  have hχ : ∀ p, 0 ≤ χ p := conditionalJoint_nonneg _ base
    (restrictedMass_nonneg μ (E w) hprime) (fun x hx =>
      hbase x ((mem_restrictedMass_support μ (E w) x).mp hx).2)
  have hτ : ∀ x i t, 0 ≤ eventCompletedDirectionMass (E w) τ x i t :=
    eventCompletedDirectionMass_nonneg (E w) τ (fun x _ i t =>
      masterPredictionDirectionMass_nonneg loc len w x i t)
  have ht : ∀ x i, total (eventCompletedDirectionMass (E w) τ x i) = 1 :=
    eventCompletedDirectionMass_total (E w) τ (fun x hx i =>
      masterPredictionDirectionMass_total loc len w x i (hpos x hx i))
  have hcs := prediction_elimination_stage_step χ hχ
    (fun p => eventCompletedDirectionMass (E w) τ p.1)
    (fun p i t => hτ p.1 i t)
    (fun p a => predictionCubeModulus w (s w a) (f a) p.1) dir hdir K k hk
    (fun p => ht p.1 k) (fun p => p.2) (fun p => G w p.1)
    (fun _ base t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t)
    (fun p t => hbound p.1 t)
  change |expectation (conditionalJoint (restrictedMass μ (E w)) base) _| ^ 2 ≤
    expectation (conditionalJoint (restrictedMass μ (E w)) base) _ *
    expectation (conditionalJoint (restrictedMass μ (E w)) base) _ at hcs
  have hold := event_joint_pair_expectation μ base (E w) τ
    (fun x z v => predictionEliminationIntegrand
      (fun a => predictionCubeModulus w (s w a) (f a) x) dir K z v (G w x)
      (fun row t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w row) t))
  have hpref := event_joint_pair_expectation μ base (E w) τ
    (fun x z v => predictionStageFactorProduct
      (fun a => predictionCubeModulus w (s w a) (f a) x) dir K (some (dir k)) z
      (predictionPairValues v)
      (fun t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir k))) t))
  have hnext := event_joint_pair_expectation μ base (E w) τ
    (fun x z v => predictionEliminationIntegrand
      (fun a => predictionCubeModulus w (s w a) (f a) x) dir (insert k K) z v (G w x)
      (fun row t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w row) t))
  rw [hold, hpref, hnext] at hcs
  exact hcs

theorem master_prediction_stage_prefactor_nonneg
    {N m r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (gap : ℕ → Fin r → ℕ)
    (s : ℕ → Fin b → ℕ) (f : Fin b → MvPolynomial (Fin r) ℤ)
    (dir : Fin h → Fin b × CubeVertex d)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (w : ℕ) (K : Finset (Fin h)) (row : ReplicaCubeRow b d)
    (hprime : ∀ x, 0 ≤ masterPrimeSlotsMass F w (gap w) x)
    (hbase : ∀ x, E w x → ∀ z,
      0 ≤ piMass (masterPredictionOriginalCoordinateMass H F index loc len w x) z)
    (hmajorant : ∀ t, 0 ≤ 1 +
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w row) t) :
    0 ≤ masterPredictionStagePrefactor F C label gap s f dir H index loc len E w K row := by
  unfold masterPredictionStagePrefactor conditionalFiniteAverage
  apply expectation_nonneg_support _ _ hprime
  intro x _
  by_cases hx : E w x
  · rw [if_pos hx]
    apply expectation_nonneg_support _ _ (hbase x hx)
    intro z _
    apply expectation_nonneg_support _ _ (piMass_nonneg _ (fun i t => by
      rw [tensor_apply]
      exact mul_nonneg (masterPredictionDirectionMass_nonneg loc len w x i t.1)
        (masterPredictionDirectionMass_nonneg loc len w x i t.2)))
    intro v _
    unfold predictionStageFactorProduct
    exact Finset.prod_nonneg (fun _ _ => hmajorant _)
  · simp only [if_neg hx, le_refl]

end Hindman168
