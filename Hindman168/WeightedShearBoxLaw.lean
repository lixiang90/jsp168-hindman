import Hindman168.WeightedShearBoxVariation

/-!
Normalized Lebesgue laws on the original weighted boxes.  Their pushforwards
under any fixed shear converge uniformly over all measurable events to the
original laws.  This is the probabilistic total-variation assertion (7.20).
-/

namespace Hindman168
open Set MeasureTheory Filter
open scoped ENNReal BigOperators Topology symmDiff

variable {σ : Type*} [Fintype σ]

/-- The genuine normalized Lebesgue measure on the box (7.19). -/
noncomputable def weightedShearBoxLaw (w : σ → ℕ) (E : ℝ) : Measure (σ → ℝ) :=
  (volume (weightedShearBox w E))⁻¹ • volume.restrict (weightedShearBox w E)

theorem weightedShearBoxLaw_probability (w : σ → ℕ) {E : ℝ} (hE : 0 < E) :
    IsProbabilityMeasure (weightedShearBoxLaw w E) := by
  have hpos := (ENNReal.toReal_pos_iff.mp (weightedShearBox_volume_pos w hE)).1
  have hfin : volume (weightedShearBox w E) ≠ ∞ := (weightedShearBox_isCompact w E).measure_lt_top.ne
  constructor
  simp only [weightedShearBoxLaw, Measure.smul_apply, Measure.restrict_apply_univ, smul_eq_mul]
  exact ENNReal.inv_mul_cancel hpos.ne' hfin

/-- The pushed law is the normalized restriction to the actual shear image. -/
theorem weightedShearBoxLaw_map (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (f : weightedShearGroup (R := ℝ) w) (E : ℝ) :
    (weightedShearBoxLaw w E).map (fun x : σ → ℝ => f • x) =
      (volume (weightedShearBox w E))⁻¹ •
        volume.restrict ((fun x : σ → ℝ => f • x) '' weightedShearBox w E) := by
  have hpres := weightedShearPoint_measurePreserving w s hw f
  have himage : MeasurableSet ((fun x : σ → ℝ => f • x) '' weightedShearBox w E) :=
    ((weightedShearBox_isCompact w E).image (weightedShearPoint_continuous f.val)).measurableSet
  have h := Measure.restrict_map (μ := volume) hpres.measurable himage
  rw [hpres.map_eq, preimage_image_eq _ (MulAction.injective f)] at h
  rw [weightedShearBoxLaw, Measure.map_smul, h]

/-- Uniform control of every measurable event by the relative symmetric difference. -/
theorem weightedShearBoxLaw_event_bound (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) (f : weightedShearGroup (R := ℝ) w)
    (E : ℝ) (A : Set (σ → ℝ)) (hA : MeasurableSet A) :
    |((weightedShearBoxLaw w E).map (fun x : σ → ℝ => f • x)).real A -
      (weightedShearBoxLaw w E).real A| ≤
      volume.real (weightedShearBox w E ∆ ((fun x : σ → ℝ => f • x) '' weightedShearBox w E)) /
        volume.real (weightedShearBox w E) := by
  let B := weightedShearBox w E
  let T := (fun x : σ → ℝ => f • x) '' B
  have hBc := weightedShearBox_isCompact w E
  have hTc := hBc.image (weightedShearPoint_continuous f.val)
  have hBfin : volume B ≠ ∞ := hBc.measure_lt_top.ne
  have hTfin : volume T ≠ ∞ := hTc.measure_lt_top.ne
  have h₁ := abs_measureReal_sub_le_measureReal_symmDiff' (μ := volume)
    (hA.inter hTc.measurableSet).nullMeasurableSet
    (hA.inter hBc.measurableSet).nullMeasurableSet
    (measure_ne_top_of_subset inter_subset_right hTfin)
    (measure_ne_top_of_subset inter_subset_right hBfin)
  have hsub : (A ∩ T) ∆ (A ∩ B) ⊆ T ∆ B := by
    intro x hx
    simp only [mem_symmDiff, mem_inter_iff] at hx ⊢
    tauto
  have h₂ : volume.real ((A ∩ T) ∆ (A ∩ B)) ≤ volume.real (T ∆ B) :=
    measureReal_mono hsub (measure_symmDiff_ne_top hTfin hBfin)
  rw [weightedShearBoxLaw_map w s hw, weightedShearBoxLaw,
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    measureReal_restrict_apply hA, measureReal_restrict_apply hA]
  change |(volume B)⁻¹.toReal*volume.real (A ∩ T) -
    (volume B)⁻¹.toReal*volume.real (A ∩ B)| ≤ _
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    (volume B)⁻¹.toReal * |volume.real (A ∩ T)-volume.real (A ∩ B)| ≤
        (volume B)⁻¹.toReal * volume.real (T ∆ B) :=
      mul_le_mul_of_nonneg_left (h₁.trans h₂) ENNReal.toReal_nonneg
    _ = volume.real (B ∆ T) / volume.real B := by
      rw [symmDiff_comm T B, ENNReal.toReal_inv, div_eq_mul_inv, mul_comm]
      rfl

/-- For each fixed finite list of shears the laws are uniformly close on all events. -/
theorem weightedShearBoxLaw_finite_uniform (w : σ → ℕ) (s : ℕ)
    (hw : ∀ i, w i ≤ s) (hwpos : ∀ i, 0 < w i)
    (F : Finset (weightedShearGroup (R := ℝ) w)) (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ E : ℝ in atTop, ∀ f ∈ F, ∀ A : Set (σ → ℝ), MeasurableSet A →
      |((weightedShearBoxLaw w E).map (fun x : σ → ℝ => f • x)).real A -
        (weightedShearBoxLaw w E).real A| < ε := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert f F hf ih =>
      have hlim := weightedShearBox_relative_symmDiff_tendsto w s hw hwpos f
      have hsmall := hlim.eventually (gt_mem_nhds hε)
      filter_upwards [hsmall, ih] with E hE hF
      intro g hg A hA
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact (weightedShearBoxLaw_event_bound w s hw g E A hA).trans_lt hE
      · exact hF g hg A hA

end Hindman168
