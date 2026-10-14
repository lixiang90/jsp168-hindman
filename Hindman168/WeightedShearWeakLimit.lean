import Hindman168.WeightedShearBoxLaw
import Mathlib.MeasureTheory.Measure.Prokhorov

/-!
The compactness step from actual eventwise asymptotic invariance to weak
convergence. This is applied to the full joint homogeneous space, never to
separate marginal laws.
-/
namespace Hindman168
open MeasureTheory Filter Set Metric TopologicalSpace
open scoped Topology ENNReal

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Eventwise total-variation control bounds the actual Lévy–Prokhorov distance. -/
theorem weightedShear_probability_distance_le (μ ν : ProbabilityMeasure X)
    (δ : ℝ) (hδ : 0 ≤ δ)
    (h : ∀ A : Set X, MeasurableSet A →
      |μ.toMeasure.real A - ν.toMeasure.real A| ≤ δ) :
    dist (LevyProkhorov.ofMeasure μ) (LevyProkhorov.ofMeasure ν) ≤ δ := by
  change levyProkhorovDist μ.toMeasure ν.toMeasure ≤ δ
  apply levyProkhorovDist_le_of_forall_le μ.toMeasure ν.toMeasure hδ
  intro ε A hε hA
  have hεpos : 0 < ε := lt_of_le_of_lt hδ hε
  have hm : ν.toMeasure.real A ≤ ν.toMeasure.real (thickening ε A) :=
    measureReal_mono (self_subset_thickening hεpos A)
  have hreal : μ.toMeasure.real A ≤ ν.toMeasure.real (thickening ε A) + ε := by
    have := (le_abs_self (μ.toMeasure.real A - ν.toMeasure.real A)).trans (h A hA)
    linarith
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, ENNReal.ofReal_ne_top⟩)).mp
  simpa only [Measure.real, ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hεpos.le] using hreal

/-- Compactness and uniqueness of invariant probability force the full weak limit. -/
theorem weightedShear_probability_tendsto_of_unique_invariant
    [CompactSpace X] {ι G : Type*} (l : Filter ι)
    (μ : ι → ProbabilityMeasure X) (ν : ProbabilityMeasure X) (T : G → C(X, X))
    (hunique : ∀ η : ProbabilityMeasure X,
      (∀ g, η.map (T g).continuous.measurable.aemeasurable = η) → η = ν)
    (hclose : ∀ g ε, 0 < ε → ∀ᶠ t in l, ∀ A : Set X, MeasurableSet A →
      |((μ t).map (T g).continuous.measurable.aemeasurable).toMeasure.real A -
        (μ t).toMeasure.real A| < ε) :
    Tendsto μ l (𝓝 ν) := by
  let H := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)
  apply tendsto_nhds_of_unique_mapClusterPt
  intro η hη
  apply hunique η
  intro g
  let f : ProbabilityMeasure X → ℝ := fun ξ =>
    dist (H (ξ.map (T g).continuous.measurable.aemeasurable)) (H ξ)
  have hf : Continuous f :=
    (H.continuous.comp (ProbabilityMeasure.continuous_map (T g).continuous)).dist H.continuous
  have hzero : Tendsto (fun t => f (μ t)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hclose g (ε/2) (half_pos hε)] with t ht
    have hbound := weightedShear_probability_distance_le
      ((μ t).map (T g).continuous.measurable.aemeasurable) (μ t)
      (ε/2) (half_pos hε).le (fun A hA => (ht A hA).le)
    have hn : 0 ≤ f (μ t) := dist_nonneg
    change dist (f (μ t)) 0 < ε
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hn]
    exact hbound.trans_lt (half_lt_self hε)
  have hc := hη.tendsto_comp hf.continuousAt
  have hz : f η = 0 := eq_of_nhds_neBot (hc.clusterPt.mono hzero)
  exact H.injective (dist_eq_zero.mp hz)

/-- Eventwise total-variation convergence transfers an existing weak limit. -/
theorem weightedShear_probability_tendsto_congr [SeparableSpace X]
    {ι : Type*} (l : Filter ι) (μ ν : ι → ProbabilityMeasure X) (ρ : ProbabilityMeasure X)
    (hμ : Tendsto μ l (𝓝 ρ))
    (hclose : ∀ ε, 0 < ε → ∀ᶠ t in l, ∀ A : Set X, MeasurableSet A →
      |(ν t).toMeasure.real A - (μ t).toMeasure.real A| < ε) :
    Tendsto ν l (𝓝 ρ) := by
  let H := LevyProkhorov.probabilityMeasureHomeomorph (Ω := X)
  have hHμ : Tendsto (fun t => H (μ t)) l (𝓝 (H ρ)) :=
    (H.continuous.tendsto ρ).comp hμ
  have hHν : Tendsto (fun t => H (ν t)) l (𝓝 (H ρ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hhalf := (Metric.tendsto_nhds.mp hHμ) (ε/2) (half_pos hε)
    filter_upwards [hhalf, hclose (ε/4) (by positivity)] with t ht hclose
    have hbound := weightedShear_probability_distance_le (ν t) (μ t)
      (ε/4) (by positivity) (fun A hA => (hclose A hA).le)
    change dist (H (ν t)) (H (μ t)) ≤ ε/4 at hbound
    calc
      dist (H (ν t)) (H ρ) ≤ dist (H (ν t)) (H (μ t)) + dist (H (μ t)) (H ρ) :=
        dist_triangle _ _ _
      _ < ε := by linarith
  exact (H.symm.continuous.tendsto (H ρ)).comp hHν

/-- A probability-valued version of the actual box law, unchanged for `E ≥ 1`. -/
noncomputable def weightedShearBoxProbability {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (E : ℝ) : ProbabilityMeasure (σ → ℝ) :=
  ⟨weightedShearBoxLaw w (max E 1),
    weightedShearBoxLaw_probability w (lt_of_lt_of_le zero_lt_one (le_max_right E 1))⟩

/-- The projected original boxes converge on the whole compact quotient when its
translations have the proved weighted-shear lifts. -/
theorem weightedShearBoxProbability_projection_tendsto
    [CompactSpace X] {σ G : Type*} [Fintype σ]
    (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) (hwpos : ∀ i, 0 < w i)
    (π : (σ → ℝ) → X) (hπ : Continuous π) (ν : ProbabilityMeasure X) (T : G → C(X, X))
    (hunique : ∀ η : ProbabilityMeasure X,
      (∀ g, η.map (T g).continuous.measurable.aemeasurable = η) → η = ν)
    (hlift : ∀ g, ∃ f : weightedShearGroup (R := ℝ) w,
      ∀ x, π (f • x) = T g (π x)) :
    Tendsto (fun E : ℝ => (weightedShearBoxProbability w E).map hπ.measurable.aemeasurable)
      atTop (𝓝 ν) := by
  apply weightedShear_probability_tendsto_of_unique_invariant atTop _ ν T hunique
  intro g ε hε
  obtain ⟨f, hf⟩ := hlift g
  have hsmall := weightedShearBoxLaw_finite_uniform w s hw hwpos {f} ε hε
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with E hsmall hE
  intro A hA
  have hfcont : Continuous (fun x : σ → ℝ => f • x) := weightedShearPoint_continuous f.val
  have hmap : Measure.map (T g) (Measure.map π (weightedShearBoxLaw w E)) =
      Measure.map π (Measure.map (fun x : σ → ℝ => f • x) (weightedShearBoxLaw w E)) := by
    rw [Measure.map_map (T g).continuous.measurable hπ.measurable,
      Measure.map_map hπ.measurable hfcont.measurable]
    congr 1
    funext x
    exact (hf x).symm
  change |(Measure.map (T g) (Measure.map π (weightedShearBoxLaw w (max E 1)))).real A -
    (Measure.map π (weightedShearBoxLaw w (max E 1))).real A| < ε
  rw [max_eq_left hE, hmap]
  simp only [Measure.real, Measure.map_apply hπ.measurable hA]
  exact hsmall f (Finset.mem_singleton_self f) (π ⁻¹' A) (hπ.measurable hA)

/-- Every fixed shear has the same projected weak limit as the unaltered boxes. -/
theorem weightedShearBoxProbability_shear_projection_tendsto [SeparableSpace X]
    {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) (hwpos : ∀ i, 0 < w i)
    (π : (σ → ℝ) → X) (hπ : Continuous π) (ν : ProbabilityMeasure X)
    (f : weightedShearGroup (R := ℝ) w)
    (hlim : Tendsto (fun E : ℝ =>
      (weightedShearBoxProbability w E).map hπ.measurable.aemeasurable) atTop (𝓝 ν)) :
    Tendsto (fun E : ℝ => (weightedShearBoxProbability w E).map
      (hπ.comp (weightedShearPoint_continuous f.val)).measurable.aemeasurable) atTop (𝓝 ν) := by
  apply weightedShear_probability_tendsto_congr atTop _ _ ν hlim
  intro ε hε
  have hsmall := weightedShearBoxLaw_finite_uniform w s hw hwpos {f} ε hε
  filter_upwards [hsmall, eventually_ge_atTop (1 : ℝ)] with E hsmall hE
  intro A hA
  have hfcont : Continuous (fun x : σ → ℝ => f • x) := weightedShearPoint_continuous f.val
  change |(Measure.map (π ∘ fun x => f • x) (weightedShearBoxLaw w (max E 1))).real A -
    (Measure.map π (weightedShearBoxLaw w (max E 1))).real A| < ε
  rw [max_eq_left hE, ← Measure.map_map hπ.measurable hfcont.measurable]
  simp only [Measure.real, Measure.map_apply hπ.measurable hA]
  exact hsmall f (Finset.mem_singleton_self f) (π ⁻¹' A) (hπ.measurable hA)

end Hindman168
