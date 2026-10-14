import Hindman168.MasterSingleClippedDenseModel

/-!
# Uniform original-law clipping and bounded models for original dual tests

The uniform clipping limit is derived for arbitrary admissible input
sequences, then the same selected bounded model works for every input of
one fixed original local template, without clipping in the final pairing.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.uniform_single_dual_clipping_error
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
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ u : OriginalSingleDualInput a d,
      u.Admissible F C label w →
      expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (1 + masterPredictionBlockMask F C label w y) *
          |masterSingleGoodDualTest F d gap J choice tests den
            (fun _ => u.epsilon) (fun _ => u.vertexTest) w y - predictionClip cut
              (masterSingleGoodDualTest F d gap J choice tests den
                (fun _ => u.epsilon) (fun _ => u.vertexTest) w y)|) < η := by
  let base (_w : ℕ) : OriginalSingleDualInput a d := ⟨fun _ => 0, fun _ _ _ => 0⟩
  let err (w : ℕ) (u : OriginalSingleDualInput a d) :=
    expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (1 + masterPredictionBlockMask F C label w y) *
        |masterSingleGoodDualTest F d gap J choice tests den
          (fun _ => u.epsilon) (fun _ => u.vertexTest) w y - predictionClip cut
            (masterSingleGoodDualTest F d gap J choice tests den
              (fun _ => u.epsilon) (fun _ => u.vertexTest) w y)|)
  have hbase : ∀ᶠ w in atTop, (base w).Admissible F C label w := by
    filter_upwards [hF.block_mask_eventually_nonneg C hN label] with w hw
    constructor
    · intro x; norm_num [base]
    · intro x S y
      change |(0 : ℝ)| ≤ 1 + masterPredictionBlockMask F C label w y
      rw [abs_zero]
      exact add_nonneg zero_le_one (hw y)
  have hseq (input : ℕ → OriginalSingleDualInput a d)
      (hi : ∀ᶠ w in atTop, (input w).Admissible F C label w) :
      Tendsto (fun w => err w (input w)) atTop (𝓝 0) := by
    have heps : ∀ᶠ w in atTop, ∀ x, |(input w).epsilon x| ≤ 1 := hi.mono (fun _ hw => hw.1)
    have hg : ∀ᶠ w in atTop, ∀ x S y,
        |(input w).vertexTest x S y| ≤ 1 + masterPredictionBlockMask F C label w y :=
      hi.mono (fun _ hw => hw.2)
    simpa only [err, pow_one, masterSingleGoodDualTest] using hF.normalized_single_dual_clipping_tendsto hD C hN label
      tail htail root gap htailroot htailgap J hJ choice tests den hden masterSlot
      hmasterSlot hinclude (fun w => (input w).epsilon) heps
      (fun w => (input w).vertexTest) hg cut hcut 1 (by norm_num)
  have hu := uniform_zero_of_admissible_sequences
    (fun w (u : OriginalSingleDualInput a d) => u.Admissible F C label w) err base hbase hseq
  intro η hη
  exact (hu η hη).mono (fun _ hw u hc => (le_abs_self _).trans_lt (hw u hc))

theorem MasterParameterConditions.uniform_single_original_dense_models
    {n a N m d K : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0) (hd : 0 < d)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root gap : ℕ → Fin N)
    (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (htailgap : ∀ᶠ w in atTop, tail w ⊆ Finset.range (gap w).val)
    (hgap : ∀ᶠ w in atTop, (gap w).val ≤ (root w).val)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k) (choice : ℕ → Fin K)
    (tests : Finset (MvPolynomial (Fin a) ℤ))
    (den : MvPolynomial (Fin a) ℤ) (hden : den ∈ tests)
    (masterSlot : Fin a → Fin n) (hmasterSlot : Function.Injective masterSlot)
    (hinclude : ∀ f ∈ tests, MvPolynomial.rename masterSlot f ∈ D)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ ρ : ℤ → ℝ,
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ masterPredictionBlockMask F C label w y) →
      ∃ model : ℤ → ℝ, (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
        ∀ u : OriginalSingleDualInput a d, u.Admissible F C label w →
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ y - model y) * masterSingleGoodDualTest F d gap J choice tests den
              (fun _ => u.epsilon) (fun _ => u.vertexTest) w y)| < η := by
  intro η hη
  have hmodel := hF.uniform_single_clipped_dense_models hD hd C hN label tail htail root gap
    htailroot htailgap hgap J hJ choice tests den hden masterSlot hmasterSlot hinclude cut hcut
    (η / 2) (by positivity)
  have hclip := hF.uniform_single_dual_clipping_error hD C hN label tail htail root gap
    htailroot htailgap J hJ choice tests den hden masterSlot hmasterSlot hinclude cut hcut
    (η / 2) (by positivity)
  filter_upwards [hmodel, hclip, hF.raw_cutoffs_valid] with w hmw hcw hrw
  intro ρ hρ
  obtain ⟨model, hm, he⟩ := hmw ρ hρ
  refine ⟨model, hm, ?_⟩
  intro u hu
  let dual y := masterSingleGoodDualTest F d gap J choice tests den
    (fun _ => u.epsilon) (fun _ => u.vertexTest) w y
  have hs : (fun y => predictionClip cut (dual y)) ∈
      signedOriginalSingleClippedClass (a := a) (d := d) F C label gap J choice tests den cut w := by
    refine ⟨1, u, abs_one, hu, ?_⟩
    funext y
    exact (one_mul _).symm
  have hp := he (fun y => predictionClip cut (dual y)) hs
  have hμ := integerMass_nonneg (hrw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2
  have hc (y : ℤ) : |ρ y - model y| ≤ 1 + masterPredictionBlockMask F C label w y := by
    apply abs_le.mpr
    constructor <;> linarith [(hρ y).1, (hρ y).2, (hm y).1, (hm y).2]
  have hdif := weighted_centered_difference_bound
    (integerMass (F.cutoff w (root w).val) (primorial w)) hμ
    (fun y => ρ y - model y) (fun y => 1 + masterPredictionBlockMask F C label w y)
    dual (fun y => predictionClip cut (dual y)) hc
  have hdif' := hdif.trans_lt (hcw u hu)
  have ht := abs_add_le
    (expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (ρ y - model y) * dual y) -
      expectation (integerMass (F.cutoff w (root w).val) (primorial w))
        (fun y => (ρ y - model y) * predictionClip cut (dual y)))
    (expectation (integerMass (F.cutoff w (root w).val) (primorial w))
      (fun y => (ρ y - model y) * predictionClip cut (dual y)))
  simp only [sub_add_cancel] at ht
  exact ht.trans_lt (by linarith)

end Hindman168
