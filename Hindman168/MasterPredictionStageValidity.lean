import Hindman168.MasterPredictionStageCauchySchwarz

/-!
# Sampling validity derived from the actual master growth conditions

The original harmonic cutoffs give nonnegative original-column laws.
Every auxiliary direction length is eventually positive on the original
prime event by its fixed-power lower growth scale and actual length bound.
-/

namespace Hindman168

open Filter Asymptotics
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.prediction_original_base_eventually_nonneg
    {n N r b d h : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (index : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → Fin N)
    (loc : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℤ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ) :
    ∀ᶠ w in atTop, ∀ x z,
      0 ≤ piMass (masterPredictionOriginalCoordinateMass H F index loc len w x) z := by
  filter_upwards [hF.raw_cutoffs_valid] with w hw
  intro x z
  apply piMass_nonneg
  intro col t
  unfold masterPredictionOriginalCoordinateMass
  dsimp only
  split_ifs with hc
  · exact integerMass_nonneg
      (hw (index w (predictionColumnIndex (.inl col))).val
        (Finset.mem_range.mpr (index w (predictionColumnIndex (.inl col))).isLt)).2.2 t
  · exact uniformIntervalMass_nonneg _ _ t

theorem prediction_direction_lengths_eventually_positive {r b d h : ℕ}
    (H : Finset (Fin (Fintype.card (CopiedReplicaCubeColumn b d h))))
    (Tmin : ℕ → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ) (V : ℕ → ℕ)
    (len : ℕ → (Fin r → ℕ) → Fin (Fintype.card (CopiedReplicaCubeColumn b d h)) → ℕ)
    (E : ℕ → (Fin r → ℕ) → Prop)
    (haux : ∀ i bit, predictionColumnIndex (.inr (i, bit) : CopiedReplicaCubeColumn b d h) ∉ H)
    (hlengthgrowth : ∀ j, j ∉ H → PowerDominates atTop (fun w => (Tmin w j : ℝ))
      (fun w => (samplingSize 0 (V w) 0 (V w) : ℝ)))
    (hlen : ∀ᶠ w in atTop, ∀ x, E w x → ∀ j, j ∉ H → Tmin w j ≤ len w x j) :
    ∀ᶠ w in atTop, ∀ x, E w x → ∀ i,
      0 < len w x (predictionColumnIndex (.inr (i, false))) := by
  have hp : ∀ᶠ w in atTop, ∀ i : Fin h, 0 < Tmin w (predictionColumnIndex (.inr (i, false))) := by
    apply eventually_all.mpr
    intro i
    exact uniform_interval_eventually_positive
      (hlengthgrowth (predictionColumnIndex (.inr (i, false))) (haux i false))
  filter_upwards [hp, hlen] with w hw hl
  intro x hx i
  exact lt_of_lt_of_le (hw i) (hl x hx _ (haux i false))

end Hindman168
