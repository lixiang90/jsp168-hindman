import Hindman168.MasterPredictionStageIdentifications

/-!
# Derived actual master bounds for every ordered prediction stage

Every prefactor is identified with a concrete subset of the canonical
copied-row family. Its eventual bound is proved from the original master
linear-forms conditions. The full terminal stage tends to zero by the
same exact law identification and the proved common-event cancellation.
No stage moment convergence or prefactor bound is supplied as a premise.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.prediction_stage_prefactor_eventually_le
    {n N m r b d h L : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → ReplicaCubeRow b d → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ base, tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (K : Finset (Fin h)) (base : ReplicaCubeRow b d) :
    ∀ᶠ w in atTop,
      masterPredictionStagePrefactor F C label (fun w j => gap w j) s f dir H index loc len E w K base ≤
        ((2 ^ (copiedPredictionStageRowIndices dir K base).card : ℕ) : ℝ) + 1 := by
  have hm := hF.copied_replica_cube_majorant_eventually_le C hN
    (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1) gap V hV
    (hdivbudget.mono (fun w hw u => hw (copiedPredictionRowEnumeration dir u).val.1))
    hprimebudget T hT s e hs f hf dir (fun _ => copiedPredictionRowEnumeration dir)
    (Eventually.of_forall (fun _ => copiedPredictionRowEnumeration_injective dir))
    H index Tmin loc len E hharmbudget hlengthgrowth hlen
    (copiedPredictionStageRowIndices dir K base)
  simpa only [masterPredictionStagePrefactor_eq F C label (fun w j => gap w j)
    s f dir H index loc len E haux hloc hpair] using hm

theorem MasterParameterConditions.prediction_stage_terminal_tendsto
    {n N m r b d h L : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → ReplicaCubeRow b d → Fin m)
    (gap : ℕ → Fin r → Fin L) (V : ℕ → ℕ) (hV : ∀ᶠ w in atTop, 1 ≤ V w)
    (hdivbudget : ∀ᶠ w in atTop, ∀ base, tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w)
    (hprimebudget : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j))
    (T : Finset (MvPolynomial (Fin r) ℤ)) (hT : ∀ f ∈ T, f ≠ 0)
    (s : ℕ → Fin b → ℕ) (e : ℕ → Fin b → ℕ)
    (hs : ∀ᶠ w in atTop, ∀ v, s w v ∣ primorial w ^ e w v)
    (f : Fin b → MvPolynomial (Fin r) ℤ) (hf : ∀ v, f v ∈ T)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (hharmbudget : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (hdir : Function.Surjective dir)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1) :
    Tendsto (fun w => masterPredictionStageAverage F C label (fun w j => gap w j)
      s f dir H index loc len E G w Finset.univ) atTop (𝓝 0) := by
  have hm := hF.all_copied_prediction_terminal_tendsto dir C hN
    (fun w u => label w (copiedPredictionRowEnumeration dir u).val.1) gap V hV
    (hdivbudget.mono (fun w hw u => hw (copiedPredictionRowEnumeration dir u).val.1))
    hprimebudget T hT s e hs f hf H index Tmin loc len E hharmbudget hlengthgrowth hlen
  simpa only [masterPredictionStageTerminal_eq F C label (fun w j => gap w j)
    s f dir H index loc len E haux hloc hpair hdir G hroot] using hm

end Hindman168
