import Hindman168.AlignmentJointObservableCompactnessNative
import Hindman168.NativeOriginalPointWeakLimit

/-! Common observable compactness on an already selected ORIGINAL source.
The output retains the full joint local law and cube alpha law with identical
H, M, sigma and h, and derives the actual integer point-mixture weak limit.
No independent marginal extraction or limiting-law identification is assumed. -/
namespace Hindman168
open Filter MeasureTheory NNReal
open scoped Topology Manifold ContDiff
universe u v w
attribute [local instance] lieGroup_smooth_min_three

/-- Apply this to the full joint native model, after all-target symmetry
selection. Any symmetry assertion about H, sigma and h remains literally the
same assertion, since none of these data are re-selected here. -/
theorem alignment_native_observables_same_source_compactness
    {ι : Type v} [Countable ι] {s t ℓ : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s)
    (J : NativeNilmanifoldData.{w} t) (H : NativeRationalSubgroupFiltration J ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → J.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → J.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := J.E) (I := J.I) J.Γ)
    (h : ℝ → J.G) (hh : Continuous h)
    (hlocal : NativeResidueLocalHaarLaw J H L P M hM sigma hRat h)
    (halpha : NativeCubeBoundedAlphaHaarLaw J H L P M hM sigma hRat h) :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
      fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : MeasurableSpace J.G := borel J.G
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
    ∀ (obs : ∀ ν, ℕ → (ℤ × ℤ) → C((D ν).G ⧸ (D ν).Γ, ℝ))
      (B : ι → ℝ) (Lip : ι → ℝ≥0),
      (∀ ν k p z, |obs ν k p z| ≤ B ν) →
      (∀ ν k p, LipschitzWith (Lip ν) (obs ν k p)) →
      ∀ (width : ℕ → ℕ) (label : ℕ → ∀ ν, ℤ × ℤ),
      ∃ limit : ∀ ν, C((D ν).G ⧸ (D ν).Γ, ℝ),
        ∃ further : ℕ → ℕ, StrictMono further ∧
          (∀ ν, TendstoUniformly
            (fun m => obs ν (width (further m)) (label (further m) ν)) (limit ν) atTop) ∧
          NativeResidueLocalHaarLaw J H (L ∘ further) (P ∘ further) M hM sigma hRat h ∧
          NativeCubeBoundedAlphaHaarLaw J H (L ∘ further) (P ∘ further) M hM sigma hRat h ∧
          Tendsto (fun m => finiteEmpiricalProbability (Finset.Ico 0 ⌊L (further m)⌋)
            (fun z => (P (further m) (z : ℝ) : J.G ⧸ J.Γ)) (1 : J.G)) atTop
            (𝓝 (nativePointMixtureProbability J H M hM sigma hRat h hh)) := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
    fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : MeasurableSpace J.G := borel J.G
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (J.G ⧸ J.Γ) := native_nilmanifold_metric_coset_borel J
  intro obs B Lip hB hLip width label
  obtain ⟨limit, further, hfurther, hconv⟩ :=
    alignment_native_frozen_observables_compactness D obs B Lip hB hLip width id label
  have hp := alignment_native_local_haar_subsequence J H L P M hM sigma hRat h
    hlocal further hfurther
  have ha := alignment_native_alpha_haar_subsequence J H L P M hM sigma hRat h
    halpha further hfurther
  refine ⟨limit, further, hfurther, hconv, hp, ha, ?_⟩
  exact native_original_point_weak_limit J H (L ∘ further)
    (hL.comp hfurther.tendsto_atTop) (P ∘ further) M hM sigma hRat h hh hp

end Hindman168
