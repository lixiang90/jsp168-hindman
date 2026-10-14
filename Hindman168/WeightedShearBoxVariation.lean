import Hindman168.WeightedShearMeasure
import Hindman168.WeightedShearBoxBounds
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Order.Field

/-!
The actual weighted boxes form a Følner family for every fixed polynomial shear.
The relative symmetric-difference estimate is the geometric total-variation
estimate in Lemma 7.7; no coefficient-uniform assertion is used.
-/

namespace Hindman168
open Set MeasureTheory Filter
open scoped BigOperators Topology symmDiff ENNReal

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem weightedShearBox_eq_Icc (w : σ → ℕ) (E : ℝ) :
    weightedShearBox w E = Icc (fun i => -(E ^ w i)) (fun i => E ^ w i) := by
  ext x
  simp only [weightedShearBox, mem_setOf_eq, abs_le, mem_Icc, Pi.le_def, forall_and]

omit [Fintype σ] in
theorem weightedShearBox_isCompact (w : σ → ℕ) (E : ℝ) :
    IsCompact (weightedShearBox w E) := by
  rw [weightedShearBox_eq_Icc]
  exact isCompact_Icc

theorem weightedShearRect_volume (r : σ → ℝ) (hr : ∀ i, 0 ≤ r i) :
    volume.real (Icc (-r) r) = ∏ i, 2*r i := by
  change (volume (Icc (-r) r)).toReal = _
  rw [Real.volume_Icc_pi_toReal (fun i => by simpa using neg_le_self (hr i))]
  apply Finset.prod_congr rfl
  intro i _
  change r i - -r i = _
  ring

theorem weightedShearBox_volume (w : σ → ℕ) {E : ℝ} (hE : 0 ≤ E) :
    volume.real (weightedShearBox w E) = ∏ i, 2*E ^ w i := by
  rw [weightedShearBox_eq_Icc]
  exact weightedShearRect_volume _ (fun _ => pow_nonneg hE _)

theorem weightedShearBox_volume_pos (w : σ → ℕ) {E : ℝ} (hE : 0 < E) :
    0 < volume.real (weightedShearBox w E) := by
  rw [weightedShearBox_volume w hE.le]
  exact Finset.prod_pos fun _ _ => mul_pos (by norm_num) (pow_pos hE _)

/-- Exact excess-volume factor for the expanded anisotropic box. -/
theorem weightedShearExpandedBox_volume (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    {C E : ℝ} (hC : 0 ≤ C) (hE : 0 < E) :
    volume.real (Icc (fun i => -(E ^ w i+C*E ^ (w i-1)))
      (fun i => E ^ w i+C*E ^ (w i-1))) =
      (1+C/E) ^ Fintype.card σ * volume.real (weightedShearBox w E) := by
  change volume.real (Icc (-(fun i => E ^ w i+C*E ^ (w i-1)))
    (fun i => E ^ w i+C*E ^ (w i-1))) = _
  rw [weightedShearRect_volume _ (by intro i; positivity), weightedShearBox_volume w hE.le]
  have hfactor (i : σ) : 2*(E ^ w i+C*E ^ (w i-1)) = (1+C/E)*(2*E ^ w i) := by
    have hpow : E ^ w i = E ^ (w i-1)*E := by
      rw [← pow_succ]
      congr 1
      have := hw i
      omega
    rw [hpow]
    field_simp
  simp_rw [hfactor]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]

/-- Equal-volume sets inside a common enlargement differ only in twice its excess volume. -/
theorem weightedShear_symmDiff_bound {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {B T U : Set X} (hB : MeasurableSet B) (hT : MeasurableSet T)
    (hUfin : μ U ≠ ∞) (hBU : B ⊆ U) (hTU : T ⊆ U)
    (heq : μ.real T = μ.real B) :
    μ.real (B ∆ T) ≤ 2*(μ.real U-μ.real B) := by
  have hBfin := measure_ne_top_of_subset hBU hUfin
  have hTfin := measure_ne_top_of_subset hTU hUfin
  have hdiff₁ := measureReal_inter_add_sdiff (μ := μ) hT hBfin
  have hdiff₂ := measureReal_inter_add_sdiff (μ := μ) hB hTfin
  have hsdiff : μ.real (T \ B) ≤ μ.real (U \ B) :=
    measureReal_mono (sdiff_subset_sdiff_left hTU) (measure_ne_top_of_subset sdiff_subset hUfin)
  rw [measureReal_sdiff hBU hB hUfin] at hsdiff
  rw [measureReal_symmDiff_eq hB hT hBfin hTfin]
  rw [inter_comm T B] at hdiff₂
  linarith

/-- Quantitative relative boundary estimate for each actual shear. -/
theorem weightedShearBox_relative_symmDiff_bound (w : σ → ℕ)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (hwpos : ∀ i, 0 < w i)
    (f : weightedShearGroup (R := ℝ) w) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : ℝ, 1 ≤ E →
      volume.real (weightedShearBox w E ∆ ((fun x : σ → ℝ => f • x) '' weightedShearBox w E)) /
        volume.real (weightedShearBox w E) ≤ 2*((1+C/E) ^ Fintype.card σ-1) := by
  classical
  obtain ⟨p, hp, haction⟩ := weightedShearPoint_displacements w f
  obtain ⟨C, hC, hbound⟩ := weightedShear_image_box_bound w p hp hwpos
  refine ⟨C, hC, ?_⟩
  intro E hE
  let B := weightedShearBox w E
  let T := (fun x : σ → ℝ => f • x) '' B
  let r : σ → ℝ := fun i => E ^ w i+C*E ^ (w i-1)
  let U := Icc (-r) r
  have hBc : IsCompact B := weightedShearBox_isCompact w E
  have hTc : IsCompact T := hBc.image (weightedShearPoint_continuous f.val)
  have hBU : B ⊆ U := by
    intro x hx
    constructor <;> intro i
    · have hx' := (abs_le.mp (hx i)).1
      change -(E ^ w i+C*E ^ (w i-1)) ≤ x i
      have hnonneg : 0 ≤ C*E ^ (w i-1) := by positivity
      linarith
    · have hx' := (abs_le.mp (hx i)).2
      change x i ≤ E ^ w i+C*E ^ (w i-1)
      have hnonneg : 0 ≤ C*E ^ (w i-1) := by positivity
      linarith
  have hTU : T ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    constructor <;> intro i
    · exact (abs_le.mp (by simpa only [haction x i] using hbound E hE x hx i)).1
    · exact (abs_le.mp (by simpa only [haction x i] using hbound E hE x hx i)).2
  have hmeasure : volume T = volume B := by
    have h := (weightedShearPoint_measurePreserving w s hw f).measure_preimage hTc.measurableSet.nullMeasurableSet
    rw [preimage_image_eq _ (MulAction.injective f)] at h
    exact h.symm
  have hrel := weightedShear_symmDiff_bound volume hBc.measurableSet hTc.measurableSet
    (show volume U ≠ ∞ from isCompact_Icc.measure_lt_top.ne) hBU hTU
    (congrArg ENNReal.toReal hmeasure)
  have hvol := weightedShearBox_volume_pos w (show 0 < E by linarith)
  apply (div_le_iff₀ hvol).mpr
  have hUvol : volume.real U = (1+C/E) ^ Fintype.card σ * volume.real B :=
    weightedShearExpandedBox_volume w hwpos hC (by linarith)
  rw [hUvol] at hrel
  change volume.real (B ∆ T) ≤ _
  calc
    volume.real (B ∆ T) ≤ 2*((1+C/E) ^ Fintype.card σ*volume.real B-volume.real B) := hrel
    _ = 2*((1+C/E) ^ Fintype.card σ-1)*volume.real B := by ring

/-- The relative symmetric-difference volume tends to zero for every fixed shear. -/
theorem weightedShearBox_relative_symmDiff_tendsto (w : σ → ℕ)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (hwpos : ∀ i, 0 < w i)
    (f : weightedShearGroup (R := ℝ) w) :
    Tendsto (fun E : ℝ =>
      volume.real (weightedShearBox w E ∆ ((fun x : σ → ℝ => f • x) '' weightedShearBox w E)) /
        volume.real (weightedShearBox w E)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := weightedShearBox_relative_symmDiff_bound w s hw hwpos f
  have hlim : Tendsto (fun E : ℝ => 2*((1+C/E) ^ Fintype.card σ-1)) atTop (𝓝 0) := by
    have hdiv : Tendsto (fun E : ℝ => C/E) atTop (𝓝 0) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul
        (tendsto_inv_atTop_zero : Tendsto (fun E : ℝ => E⁻¹) atTop (𝓝 0))
    have hbase : Tendsto (fun E : ℝ => 1+C/E) atTop (𝓝 1) := by
      simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add hdiv
    have hsub : Tendsto (fun E : ℝ => (1+C/E) ^ Fintype.card σ-1) atTop (𝓝 0) := by
      simpa only [one_pow, sub_self] using
        (hbase.pow (Fintype.card σ)).sub (tendsto_const_nhds (x := (1 : ℝ)))
    simpa only [mul_zero] using (tendsto_const_nhds (x := (2 : ℝ))).mul hsub
  apply squeeze_zero' _ _ hlim
  · exact Filter.Eventually.of_forall fun E => div_nonneg measureReal_nonneg measureReal_nonneg
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with E hE
    exact hbound E hE

end Hindman168
