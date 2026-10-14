import Hindman168.PredictionMaskIdentifications

/-!
# Original master averages identify every ordered stage moment

The original per-base tail divisor masses are used at all canonical copies.
Exact integer evaluation and exact mixed-law factorization identify the
assigned prefactor and the full terminal stage with the previously proved
master subset majorants and canonical terminal expression.
-/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def masterPredictionBaseDivisorMass {m b d : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (w : ℕ) (base : ReplicaCubeRow b d) : Mass ℕ :=
  tailMass (primorial w) ((C w).tailCutoffs (F.cutoff w) (label w base))

theorem masterPredictionEnumeratedMask_eq {m r b d h : ℕ}
    (F : MasterParameterFamily) (C : ℕ → Chain m)
    (label : ℕ → ReplicaCubeRow b d → Fin m) (s : ℕ → Fin b → ℕ)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (dir : Fin h → Fin b × CubeVertex d)
    (w : ℕ) (u : Fin (Fintype.card (CopiedReplicaCubeRow dir))) (x : Fin r → ℕ)
    (y : Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ) :
    masterCopiedPredictionCubeWeight F C
      (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1)
      s f dir (fun _ => copiedPredictionRowEnumeration dir) w u x y =
    predictionEnumeratedMask (masterPredictionBaseDivisorMass F C label w)
      (fun v => predictionCubeModulus w (s w v) (f v) x) dir u y := rfl

noncomputable def masterPredictionStagePrefactor
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
    (w : ℕ) (K : Finset (Fin h)) (base : ReplicaCubeRow b d) : ℝ :=
  conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w))
    (fun x => piMass (masterPredictionOriginalCoordinateMass H F index loc len w x)) (E w)
    (fun x z => expectation (piMass (fun i => tensor (masterPredictionDirectionMass loc len w x i)
      (masterPredictionDirectionMass loc len w x i))) (fun v =>
        predictionStageFactorProduct (fun a => predictionCubeModulus w (s w a) (f a) x)
          dir K base z (predictionPairValues v)
          (fun t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t)))

noncomputable def masterPredictionStageAverage
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
    (w : ℕ) (K : Finset (Fin h)) : ℝ :=
  conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w))
    (fun x => piMass (masterPredictionOriginalCoordinateMass H F index loc len w x)) (E w)
    (fun x z => expectation (piMass (fun i => tensor (masterPredictionDirectionMass loc len w x i)
      (masterPredictionDirectionMass loc len w x i))) (fun v =>
        predictionEliminationIntegrand (fun a => predictionCubeModulus w (s w a) (f a) x)
          dir K z v (G w x)
          (fun base t => 1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w base) t)))

theorem masterPredictionStagePrefactor_eq
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
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (w : ℕ) (K : Finset (Fin h)) (base : ReplicaCubeRow b d) :
    masterPredictionStagePrefactor F C label gap s f dir H index loc len E w K base =
    conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => ∏ u ∈ copiedPredictionStageRowIndices dir K base,
        (1 + masterCopiedPredictionCubeWeight F C
          (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1)
          s f dir (fun _ => copiedPredictionRowEnumeration dir) w u x y)) := by
  unfold masterPredictionStagePrefactor conditionalFiniteAverage
  congr 1
  funext x
  split_ifs
  · rw [master_prediction_sampling_law H F index loc len w x haux (hloc w x) (hpair w x)]
    apply expectation_congr_support
    intro z _
    apply expectation_congr_support
    intro v _
    simp only [masterPredictionEnumeratedMask_eq]
    exact prediction_prefactor_mask_identification _ _ dir K base z v
  · rfl

theorem masterPredictionStageTerminal_eq
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
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (hdir : Function.Surjective dir)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (w : ℕ) :
    masterPredictionStageAverage F C label gap s f dir H index loc len E G w Finset.univ =
    conditionalFiniteAverage (masterPrimeSlotsMass F w (gap w))
      (masterMixedBaseMass H F index loc len w) (E w)
      (fun x y => (∏ u ∈ copiedPredictionRootIndices dir,
        (masterCopiedPredictionCubeWeight F C
          (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1)
          s f dir (fun _ => copiedPredictionRowEnumeration dir) w u x y - 1)) *
        ∏ u ∈ copiedPredictionRetainedIndices dir,
          (1 + masterCopiedPredictionCubeWeight F C
            (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1)
            s f dir (fun _ => copiedPredictionRowEnumeration dir) w u x y)) := by
  unfold masterPredictionStageAverage conditionalFiniteAverage
  congr 1
  funext x
  split_ifs
  · rw [master_prediction_sampling_law H F index loc len w x haux (hloc w x) (hpair w x)]
    apply expectation_congr_support
    intro z _
    apply expectation_congr_support
    intro v _
    simp only [masterPredictionEnumeratedMask_eq]
    exact prediction_terminal_mask_identification _ _ dir hdir z v (G w x) (hroot w x)
  · rfl

end Hindman168
