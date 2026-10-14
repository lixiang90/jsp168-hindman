import Hindman168.MasterCommonTailBudgets

/-!
# Actual common-tail budget in translated prediction elimination

All divisor, prime and harmonic budgets are derived from the geometry of
actual tails. Prime gaps need only occur after that tail; they are not
required to occur after the pivot. No coarse pivot auxiliary cap remains.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem MasterParameterConditions.prediction_common_tail_translated_tendsto
    {n N m r b d h L : ℕ}
    (dir : Fin h → Fin b × CubeVertex d)
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A D F) (C : ℕ → Chain m)
    (hN : ∀ w i, (C w).block i ⊆ Finset.range N) (label : ℕ → ReplicaCubeRow b d → Fin m)
    (gap : ℕ → Fin r → Fin L) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, ∀ base, (C w).tail (label w base) ⊆ tail w)
    (htailprime : ∀ᶠ w in atTop, ∀ j, tail w ⊆ Finset.range (gap w j))
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
    (htailharm : ∀ᶠ w in atTop, ∀ j ∈ H, tail w ⊆ Finset.range (index w j).val)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (masterCommonTailBudget F w (tail w)) 0 (masterCommonTailBudget F w (tail w)) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hloc : ∀ w x i bit, loc w x (predictionColumnIndex (.inr (i, bit))) =
      loc w x (predictionColumnIndex (.inr (i, false))))
    (hpair : ∀ w x i bit, len w x (predictionColumnIndex (.inr (i, bit))) =
      len w x (predictionColumnIndex (.inr (i, false))))
    (hdir : Function.Bijective dir)
    (G : ℕ → (Fin r → ℕ) → ReplicaCubeRow b d → ℤ → ℝ)
    (hroot : ∀ w x, G w x none = fun t =>
      integerDivisorMask (masterPredictionBaseDivisorMass F C label w none) t - 1)
    (hbound : ∀ᶠ w in atTop, ∀ x i t, |G w x (some (dir i)) t| ≤
      1 + integerDivisorMask (masterPredictionBaseDivisorMass F C label w (some (dir i))) t) :
    Tendsto (fun w => masterPredictionStageAverage F C label (fun w j => gap w j)
      s f dir H index loc len E G w ∅) atTop (𝓝 0) := by
  let V w := masterCommonTailBudget F w (tail w)
  have hV : ∀ᶠ w in atTop, 1 ≤ V w := Eventually.of_forall (fun w =>
    Nat.le_trans (by decide : 1 ≤ 2) (masterCommonTailBudget_ge_two F w (tail w)))
  have hdiv : ∀ᶠ w in atTop, ∀ base,
      tailBound ((C w).tailCutoffs (F.cutoff w) (label w base)) ≤ V w :=
    htail.mono (fun w hw base => hF.common_tail_divisor_budget (C w) w
      (label w base) (tail w) (hw base))
  have hp : ∀ᶠ w in atTop, ∀ j, V w ≤ F.auxiliary w (gap w j) :=
    htailprime.mono (fun w hw j => hF.common_tail_budget_le_auxiliary w (gap w j) (tail w) (hw j))
  have hh : ∀ᶠ w in atTop, ∀ j ∈ H, V w ≤ F.auxiliary w (index w j).val :=
    htailharm.mono (fun w hw j hj => hF.common_tail_budget_le_auxiliary
      w (index w j).val (tail w) (hw j hj))
  exact hF.prediction_translated_product_tendsto dir C hN label gap V hV hdiv hp
    T hT s e hs f hf H index Tmin loc len E hh hlengthgrowth hlen haux hloc hpair hdir
    G hroot hbound

end Hindman168
