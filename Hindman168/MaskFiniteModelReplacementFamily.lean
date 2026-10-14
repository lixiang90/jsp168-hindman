import Hindman168.MaskSubsetModelTelescoping

/-! A genuinely constructed finite family of block models replaces every
nonsingleton factor, uniformly over the finite coefficient/color data and
all admissible remaining factors. One newly chosen slow stage coordinates
the replacement errors with arbitrary countable companion requirements. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (C : ℕ → Chain (m+1))

noncomputable def maskModelReplacementQuality (ρ model : Fin (m+1) → ℕ → ℤ → ℝ)
    (ε : ℝ) (w : ℕ) : Prop :=
  ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
    maskOriginalSubsetAdmissible gap C w f b →
    (∀ U : NonemptyColumnSubset (m+1), 2 ≤ U.val.card → f U = ρ (U.val.max' U.property) w) →
    |maskOriginalSubsetCorrelation gap a C w f b -
      maskOriginalSubsetCorrelation gap a C w (maskSubsetModelReplacement f (fun col => model col w)) b| ≤ ε

theorem maskModelReplacementQuality_mono (ρ model : Fin (m+1) → ℕ → ℤ → ℝ)
    {ε η : ℝ} (h : ε ≤ η) (w : ℕ) (hq : maskModelReplacementQuality gap a C ρ model ε w) :
    maskModelReplacementQuality gap a C ρ model η w := by
  intro f b hf ht
  exact (hq f b hf ht).trans h

noncomputable def maskBlockModelDualControl (d₀ : ℕ) (ρ model : ℕ → ℤ → ℝ) (col : Fin (m+1)) : Prop :=
  ∀ t : Fin (Fintype.card (LargeColumnSubset m)+1), ∀ J : ℕ, 0 < J → ∀ η : ℝ, 0 < η →
    ∀ᶠ w in atTop, ∀ u : OriginalSingleDualInput
      (maskGeneratedDualTemplates m gap d₀ gap t).arity (maskGeneratedDualTemplates m gap d₀ gap t).dimension,
      u.Admissible (maskGeneratedMaster m gap) C (fun _ => col) w →
      |FiniteMass.expectation (integerMass
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) * (maskGeneratedDualTemplates m gap d₀ gap t).dual
          (maskGeneratedMaster m gap) (fun _ => J) u w y)| < η

noncomputable def maskBlockModelDualPrefix (d₀ q : ℕ) (ρ model : ℕ → ℤ → ℝ) (col : Fin (m+1)) (w : ℕ) : Prop :=
  ∀ t : Fin (Fintype.card (LargeColumnSubset m)+1), ∀ J : ℕ, J ≤ q → 0 < J → ∀ u : OriginalSingleDualInput
      (maskGeneratedDualTemplates m gap d₀ gap t).arity (maskGeneratedDualTemplates m gap d₀ gap t).dimension,
      u.Admissible (maskGeneratedMaster m gap) C (fun _ => col) w →
      |FiniteMass.expectation (integerMass
        ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
        (fun y => (ρ w y - model w y) * (maskGeneratedDualTemplates m gap d₀ gap t).dual
          (maskGeneratedMaster m gap) (fun _ => J) u w y)| ≤ 1 / ((q : ℝ)+1)

theorem maskBlockModelDualControl_prefix_eventually (d₀ q : ℕ)
    (ρ model : ℕ → ℤ → ℝ) (col : Fin (m+1))
    (hdual : maskBlockModelDualControl gap C d₀ ρ model col) :
    ∀ᶠ w in atTop, maskBlockModelDualPrefix gap C d₀ q ρ model col w := by
  have hs (t : Fin (Fintype.card (LargeColumnSubset m)+1)) (j : Fin (q+1)) :
      ∀ᶠ w in atTop, 0 < j.val → ∀ u : OriginalSingleDualInput
        (maskGeneratedDualTemplates m gap d₀ gap t).arity (maskGeneratedDualTemplates m gap d₀ gap t).dimension,
        u.Admissible (maskGeneratedMaster m gap) C (fun _ => col) w →
        |FiniteMass.expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col)) (primorial w))
          (fun y => (ρ w y - model w y) * (maskGeneratedDualTemplates m gap d₀ gap t).dual
            (maskGeneratedMaster m gap) (fun _ => j.val) u w y)| ≤ 1 / ((q : ℝ)+1) := by
    by_cases hj : 0 < j.val
    · exact (hdual t j.val hj (1 / ((q : ℝ)+1)) (by positivity)).mono
        (fun w hw _ u hu => (hw u hu).le)
    · exact Eventually.of_forall (fun _ h => False.elim (hj h))
  have hall := eventually_all.mpr (fun t => eventually_all.mpr (hs t))
  filter_upwards [hall] with w hw
  intro t J hJ hpos u hu
  exact hw t ⟨J, by omega⟩ hpos u hu

theorem maskBlockModelDualControl_targetCubes (d₀ : ℕ) (ρ model : ℕ → ℤ → ℝ) (col : Fin (m+1))
    (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (hdual : maskBlockModelDualControl gap C d₀ ρ model col)
    (t : Fin (Fintype.card (LargeColumnSubset m))) (ht : targetRootAnchor gap t = col)
    (J : ℕ) (hJ : 0 < J) :
    Tendsto (fun w => maskEndpointTargetCube gap C t J w (fun y => ρ w y - model w y)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [hρ, hdual t.succ J hJ ε hε] with w hr hw
    have hu := maskTargetRepeatedDualInput_admissible gap C t (fun _ => col) w
      (fun y => ρ w y - model w y) (fun y => model_error_abs_bound (hr y) (hm w y))
    have he := hw (maskTargetRepeatedDualInput gap t (fun y => ρ w y - model w y)) hu
    rw [maskEndpointTargetCube_eq_original_template_pairing, ht]
    exact he

theorem maskGenerated_finite_model_replacement_family {ι : Type*} [Fintype ι]
    (d₀ : ℕ) (hd₀ : 0 < d₀)
    (coeff : ι → Fin (m+1) → ℚ) (hcoeff : ∀ i col, 0 < coeff i col)
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ : ι → Fin (m+1) → ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ i col y, 0 ≤ ρ i col w y ∧
      ρ i col w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => col) w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ι → Fin (m+1) → ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ i col w y, 0 ≤ model i col w y ∧ model i col w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      (∀ i col, maskBlockModelDualControl gap C d₀ (ρ i col) (model i col) col) ∧
      (∀ i, ∀ t : Fin (Fintype.card (LargeColumnSubset m)), ∀ J : ℕ, 0 < J →
        Tendsto (fun w => maskEndpointTargetCube gap C t J w
          (fun y => ρ i (targetRootAnchor gap t) w y - model i (targetRootAnchor gap t) w y)) atTop (𝓝 0)) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ i,
        maskModelReplacementQuality gap (coeff i) C (ρ i) (model i) ε w) ∧
      (∀ᶠ w in atTop, ∀ i col, maskBlockModelDualPrefix gap C d₀ (stage w) (ρ i col) (model i col) col w) ∧
      (∀ᶠ w in atTop, ∀ i, maskModelReplacementQuality gap (coeff i) C (ρ i) (model i)
        (1 / ((stage w : ℝ)+1)) w) := by
  let A : Finset ℚ := Finset.univ.biUnion (fun i => Finset.univ.image (coeff i))
  have hA : ∀ r ∈ A, 0 < r := by
    intro r hr
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hr
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hi
    exact hcoeff i col
  have hblock (i : ι) (col : Fin (m+1)) :
      ∃ g : ℕ → ℤ → ℝ, (∀ w y, 0 ≤ g w y ∧ g w y ≤ 1) ∧
        maskBlockModelDualControl gap C d₀ (ρ i col) g col := by
    have hroot : ∀ᶠ w in atTop, (gap w).val ≤ (maskPredictionBlockRoot C hC col w).val :=
      hgap.mono (fun w hw => hw col)
    have htailroot : ∀ᶠ w in atTop, Finset.range (gap w).val ⊆
        Finset.range (maskPredictionBlockRoot C hC col w).val :=
      hroot.mono (fun _ hw => Finset.range_mono hw)
    obtain ⟨_, g, _, _, hg, _, hd⟩ :=
      maskGenerated_all_positive_scales_models m gap A hA d₀ (max d₀ (maskRowCountBound m))
        hd₀ (le_max_left _ _) (le_max_right _ _) gap C hC (fun _ => col)
        (fun w => Finset.range (gap w).val) (htail.mono (fun _ hw => hw col))
        (maskPredictionBlockRoot C hC col) htailroot
        (Eventually.of_forall (fun _ => Finset.Subset.refl _)) hroot
        (Eventually.of_forall (fun _ => Finset.Subset.refl _)) hroot (ρ i col)
        (hρ.mono (fun _ hw y => hw i col y)) (fun _ _ => True)
        (fun _ => Eventually.of_forall (fun _ => True.intro))
    refine ⟨g, hg, ?_⟩
    intro t J hJ η hη
    exact hd t J (Nat.succ_le_iff.mpr hJ) η hη
  choose model hm hdual using hblock
  have hactual (i : ι) (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J) :=
    maskBlockModelDualControl_targetCubes gap C d₀ (ρ i (targetRootAnchor gap t))
      (model i (targetRootAnchor gap t)) (targetRootAnchor gap t) (hm i _)
      (hρ.mono (fun _ hw y => hw i (targetRootAnchor gap t) y)) (hdual i _) t rfl J hJ
  have hquality (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ w in atTop, ∀ i, maskModelReplacementQuality gap (coeff i) C (ρ i) (model i) ε w := by
    apply eventually_all.mpr
    intro i
    exact maskOriginalSubset_all_model_replacements_uniform gap (coeff i) (hcoeff i) C hC 1
      (by decide) hgap htail (ρ i) (model i) (hm i) (hρ.mono (fun _ hw => hw i))
      (fun t => hactual i t 1 (by decide)) ε hε
  have hprefix (q : ℕ) : ∀ᶠ w in atTop, ∀ i col,
      maskBlockModelDualPrefix gap C d₀ q (ρ i col) (model i col) col w :=
    eventually_all.mpr (fun i => eventually_all.mpr (fun col =>
      maskBlockModelDualControl_prefix_eventually gap C d₀ q (ρ i col) (model i col) col (hdual i col)))
  let R (q w : ℕ) : Prop := P q w ∧
    (∀ i, maskModelReplacementQuality gap (coeff i) C (ρ i) (model i) (1 / ((q : ℝ)+1)) w) ∧
    ∀ i col, maskBlockModelDualPrefix gap C d₀ q (ρ i col) (model i col) col w
  have hR (q : ℕ) : ∀ᶠ w in atTop, R q w :=
    (hP q).and ((hquality (1 / ((q : ℝ)+1)) (by positivity)).and (hprefix q))
  obtain ⟨stage, hs, hsw, hr⟩ := exists_slow_stage R hR
  exact ⟨stage, model, hs, hsw, hm, hr.mono (fun _ hw => hw.1), hdual, hactual, hquality,
    hr.mono (fun _ hw => hw.2.2), hr.mono (fun _ hw => hw.2.1)⟩

end Hindman168
