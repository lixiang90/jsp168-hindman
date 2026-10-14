import Hindman168.MasterDualMoments
import Hindman168.PredictionClippingMoments

/-!
# Clipping of the actual original normalized local dual

Every fixed moment bound is derived with one unchanged master family.
Choosing the moment order after the desired error, then letting w tend
to infinity, proves weighted positive-integer Lp clipping loss zero at
every strict cut above the dimension threshold.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.normalized_single_dual_clipping_tendsto
    {n a N m d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (ε : ℕ → (Fin a → ℕ) → ℝ) (hε : ∀ᶠ w in atTop, ∀ x, |ε w x| ≤ 1)
    (g : ℕ → (Fin a → ℕ) → CubeVertex d → ℤ → ℝ)
    (hg : ∀ᶠ w in atTop, ∀ x S y, |g w x S y| ≤ 1 + masterPredictionBlockMask F C label w y)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) (p : ℕ) (hp : 0 < p) :
    Tendsto (fun w => expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (1 + masterPredictionBlockMask F C label w y) *
        |masterSingleGoodDualTest F d gap J choice tests den ε g w y -
          predictionClip cut (masterSingleGoodDualTest F d gap J choice tests den ε g w y)| ^ p))
      atTop (𝓝 0) := by
  have hA := predictionDualThreshold_ge_one d
  have hApos : 0 < predictionDualThreshold d := lt_of_lt_of_le zero_lt_one hA
  have hμ : ∀ᶠ w in atTop, ∀ y, 0 ≤ integerMass (F.cutoff w (root w).val) (primorial w) y :=
    hF.raw_cutoffs_valid.mono (fun w hw => integerMass_nonneg
      (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
  have hH : ∀ᶠ w in atTop, ∀ y, 0 ≤ 1 + masterPredictionBlockMask F C label w y :=
    (hF.block_mask_eventually_nonneg C hN label).mono (fun _ hw y => add_nonneg zero_le_one (hw y))
  have hMom (b : ℕ) : ∀ᶠ w in atTop,
      expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (1 + masterPredictionBlockMask F C label w y) *
          |masterSingleGoodDualTest F d gap J choice tests den ε g w y| ^ b) ≤
          3 * predictionDualThreshold d ^ b := by
    have hm := hF.normalized_single_dual_moment_eventually_le (b := b) hD C hN label
      tail htail root gap htailroot htailgap J hJ choice tests den hden masterSlot hmasterSlot
      hinclude ε hε g hg (predictionDualThreshold d ^ b) (pow_pos hApos b)
    exact hm.mono (fun _ hw => by linarith)
  exact prediction_clip_error_tendsto_of_moments
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => 1 + masterPredictionBlockMask F C label w y)
    (fun w y => masterSingleGoodDualTest F d gap J choice tests den ε g w y)
    hμ hH (predictionDualThreshold d) 3 cut hApos.le (hApos.trans hcut) hcut hMom p hp

end Hindman168
