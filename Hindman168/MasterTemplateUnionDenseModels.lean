import Hindman168.MasterTemplateUnionProducts

/-!
# One bounded dense model for the heterogeneous original template union

The positive-part argument and minimax use the whole signed union at once.
Uniform original clipping then transfers the same model to every original
test in every template, preserving all local laws and dependent arities.
-/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

theorem MasterParameterConditions.uniform_template_union_positive_part
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ G ∈ closedConvexHull ℝ (signedOriginalClippedUnion T F C label J cut w),
        |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (masterPredictionBlockMask F C label w y - 1) * max (G y) 0)| < η := by
  have hμ : ∀ᶠ w in atTop, ∀ y, 0 ≤ integerMass (F.cutoff w (root w).val) (primorial w) y :=
    hF.raw_cutoffs_valid.mono (fun w hw => integerMass_nonneg
      (hw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
  have hc : ∀ᶠ w in atTop, ∀ y, |masterPredictionBlockMask F C label w y - 1| ≤
      1 + masterPredictionBlockMask F C label w y :=
    (hF.block_mask_eventually_nonneg C hN label).mono
      (fun _ hw y => centered_mask_abs_le_one_add (hw y))
  have hcut0 : 0 ≤ cut := (zero_le_one.trans (predictionDualThreshold_ge_one d)).trans hcut.le
  exact uniform_positive_part_closedConvexHull
    (fun w => integerMass (F.cutoff w (root w).val) (primorial w))
    (fun w y => masterPredictionBlockMask F C label w y - 1)
    (fun w y => 1 + masterPredictionBlockMask F C label w y)
    (fun w => signedOriginalClippedUnion T F C label J cut w) cut 3 hμ hc (by norm_num)
    (hF.dual_weighted_root_mass_eventually_le C hN label tail htail root htailroot)
    (Eventually.of_forall (fun w _ hg => signedOriginalClippedUnion_abs_le T F C label J cut hcut0 w hg))
    (hF.uniform_template_union_hull_polynomial hD T C hN label tail htail root htailroot hT J hJ cut hcut)

theorem MasterParameterConditions.uniform_template_union_clipped_dense_models
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ ρ : ℤ → ℝ,
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ masterPredictionBlockMask F C label w y) →
      ∃ model : ℤ → ℝ, (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
        ∀ g ∈ signedOriginalClippedUnion T F C label J cut w,
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ y - model y) * g y)| < η := by
  rcases Nat.eq_zero_or_pos L with hz | hL
  · subst L
    intro η _
    exact Eventually.of_forall (fun _ _ _ => ⟨0, fun _ => by norm_num, fun _ hg => by
      obtain ⟨t, _⟩ := Set.mem_iUnion.mp hg
      exact Fin.elim0 t⟩)
  · intro η hη
    have hpos := hF.uniform_template_union_positive_part hD T C hN label tail htail root
      htailroot hT J hJ cut hcut (η / 2) (by positivity)
    filter_upwards [hpos, hF.block_mask_eventually_nonneg C hN label, hF.raw_cutoffs_valid]
      with w hpw hnw hrw
    intro ρ hρ
    let S := signedOriginalClippedUnion T F C label J cut w
    have hcut0 : 0 ≤ cut := (zero_le_one.trans (predictionDualThreshold_ge_one d)).trans hcut.le
    obtain ⟨model, hm, he⟩ := bounded_dense_model_of_positive_part
      (integerMass (F.cutoff w (root w).val) (primorial w))
      (integerMass_nonneg (hrw (root w).val (Finset.mem_range.mpr (root w).isLt)).2.2)
      ρ (masterPredictionBlockMask F C label w) hρ S
      (signedOriginalClippedUnion_nonempty T hL F C label J cut w hnw) cut
      (fun _ hg => signedOriginalClippedUnion_abs_le T F C label J cut hcut0 w hg)
      (fun _ hg => signedOriginalClippedUnion_neg T F C label J cut w hg)
      (η / 2) (fun G hG => (le_abs_self _).trans (hpw G hG).le)
    exact ⟨model, hm, fun g hg => (he g hg).trans_lt (by linarith)⟩

theorem MasterParameterConditions.uniform_template_union_clipping_error
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ t : Fin L,
      ∀ u : OriginalSingleDualInput (T t).arity (T t).dimension, u.Admissible F C label w →
        expectation (integerMass (F.cutoff w (root w).val) (primorial w))
          (fun y => (1 + masterPredictionBlockMask F C label w y) *
            |(T t).dual F J u w y - predictionClip cut ((T t).dual F J u w y)|) < η := by
  intro η hη
  apply eventually_all.mpr
  intro t
  exact hF.uniform_single_dual_clipping_error hD C hN label tail htail root (T t).gap
    htailroot (hT t).tail_gap J hJ (T t).choice (T t).tests (T t).denominator
    (T t).denominator_mem (T t).masterSlot (T t).masterSlot_injective
    (hT t).polynomial_inclusion cut
    ((predictionDualThreshold_mono (hT t).dimension_le).trans_lt hcut) η hη

theorem MasterParameterConditions.uniform_template_union_original_dense_models
    {n N m d K L : ℕ}
    {A₀ : Finset ℚ} {D : Finset (MvPolynomial (Fin n) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions N A₀ D F) (hD : ∀ f ∈ D, f ≠ 0)
    (T : Fin L → OriginalDualTemplate n N K)
    (C : ℕ → Chain m) (hN : ∀ w i, (C w).block i ⊆ Finset.range N)
    (label : ℕ → Fin m) (tail : ℕ → Finset ℕ)
    (htail : ∀ᶠ w in atTop, (C w).tail (label w) ⊆ tail w)
    (root : ℕ → Fin N) (htailroot : ∀ᶠ w in atTop, tail w ⊆ Finset.range (root w).val)
    (hT : ∀ t, OriginalDualTemplateConditions (T t) D d tail root)
    (J : Fin K → ℕ) (hJ : ∀ k, 1 ≤ J k)
    (cut : ℝ) (hcut : predictionDualThreshold d < cut) :
    ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop, ∀ ρ : ℤ → ℝ,
      (∀ y, 0 ≤ ρ y ∧ ρ y ≤ masterPredictionBlockMask F C label w y) →
      ∃ model : ℤ → ℝ, (∀ y, 0 ≤ model y ∧ model y ≤ 1) ∧
        ∀ t : Fin L, ∀ u : OriginalSingleDualInput (T t).arity (T t).dimension,
          u.Admissible F C label w →
          |expectation (integerMass (F.cutoff w (root w).val) (primorial w))
            (fun y => (ρ y - model y) * (T t).dual F J u w y)| < η := by
  intro η hη
  have hmodel := hF.uniform_template_union_clipped_dense_models hD T C hN label tail htail root
    htailroot hT J hJ cut hcut (η / 2) (by positivity)
  have hclip := hF.uniform_template_union_clipping_error hD T C hN label tail htail root
    htailroot hT J hJ cut hcut (η / 2) (by positivity)
  filter_upwards [hmodel, hclip, hF.raw_cutoffs_valid] with w hmw hcw hrw
  intro ρ hρ
  obtain ⟨model, hm, he⟩ := hmw ρ hρ
  refine ⟨model, hm, ?_⟩
  intro t u hu
  let dual y := (T t).dual F J u w y
  have hs : (fun y => predictionClip cut (dual y)) ∈ signedOriginalClippedUnion T F C label J cut w := by
    apply Set.mem_iUnion.mpr
    refine ⟨t, 1, u, abs_one, hu, ?_⟩
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
  have hdif' := hdif.trans_lt (hcw t u hu)
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
