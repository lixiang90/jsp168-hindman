import Hindman168.AlignmentJointObservableCompactness
import Hindman168.NativePieceRecipes
import Hindman168.NativeNilmanifoldConstruction
import Hindman168.NativeOriginalCubeBoundedAlpha
import Hindman168.NativeOriginalResidueLocalHaar
import Hindman168.NativeMetricMaskModelTesting

/-! The observable extraction uses the recipes already used by the selected
source. Both original-source Haar laws survive this further subsequence with
literally the same filtration, period, rational representatives and curve. -/
namespace Hindman168
open Filter NNReal
open scoped Topology Manifold ContDiff
universe u v
attribute [local instance] lieGroup_smooth_min_three

/-- Unpack actual representations before selecting a source. This does not
replace the observer or orbit parameters by surrogate data. -/
theorem alignment_native_piece_family_recipes {ι : Type v} {s N : ℕ}
    (D : ι → NativeNilmanifoldData.{u} s) (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (f : ι → ℕ → ℤ → ℝ)
    (hf : ∀ i, nativePieceOn (D i) F gap (f i)) :
    letI : ∀ i, MetricSpace ((D i).G ⧸ (D i).Γ) := fun i => (D i).metric
    letI : ∀ i, TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
      fun i => (D i).metric.toUniformSpace.toTopologicalSpace
    ∃ (obs : ∀ i, ℕ → (ℤ × ℤ) → C((D i).G ⧸ (D i).Γ, ℝ))
      (g a : ∀ i, ℕ → (ℤ × ℤ) → (D i).G) (B : ι → ℝ) (Lip : ι → ℝ≥0),
      (∀ i, 0 ≤ B i) ∧ (∀ i w p z, |obs i w p z| ≤ B i) ∧
      (∀ i w p, LipschitzWith (Lip i) (obs i w p)) ∧
      ∀ i, f i = piecewiseLinearNilsequence (D i).Γ F gap (obs i) (g i) (a i) := by
  letI : ∀ i, MetricSpace ((D i).G ⧸ (D i).Γ) := fun i => (D i).metric
  letI : ∀ i, TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
    fun i => (D i).metric.toUniformSpace.toTopologicalSpace
  choose obs g a B Lip hB hb hl he using hf
  exact ⟨obs, g, a, B, Lip, hB, hb, hl, he⟩

/-- Freeze any countable collection of actual observers at arbitrary selected
widths and piece labels. The supplied recipes are retained, not re-chosen. -/
theorem alignment_native_frozen_observables_compactness
    {ι : Type v} [Countable ι] {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s) :
    letI : ∀ i, MetricSpace ((D i).G ⧸ (D i).Γ) := fun i => (D i).metric
    letI : ∀ i, TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
      fun i => (D i).metric.toUniformSpace.toTopologicalSpace
    ∀ (obs : ∀ i, ℕ → (ℤ × ℤ) → C((D i).G ⧸ (D i).Γ, ℝ))
      (B : ι → ℝ) (Lip : ι → ℝ≥0),
      (∀ i w p z, |obs i w p z| ≤ B i) →
      (∀ i w p, LipschitzWith (Lip i) (obs i w p)) →
      ∀ (width selected : ℕ → ℕ) (label : ℕ → ∀ i, ℤ × ℤ),
      ∃ limit : ∀ i, C((D i).G ⧸ (D i).Γ, ℝ),
        ∃ further : ℕ → ℕ, StrictMono further ∧ ∀ i,
          TendstoUniformly
            (fun m => obs i (width (selected (further m))) (label (selected (further m)) i))
            (limit i) atTop := by
  letI : ∀ i, MetricSpace ((D i).G ⧸ (D i).Γ) := fun i => (D i).metric
  letI : ∀ i, TopologicalSpace ((D i).G ⧸ (D i).Γ) :=
    fun i => (D i).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ i, CompactSpace ((D i).G ⧸ (D i).Γ) := fun i => by
    exact Eq.mp (congrArg (fun t => @CompactSpace ((D i).G ⧸ (D i).Γ) t)
      (nativeNilmanifold_metric_topology (D i))) (D i).quotientCompact
  intro obs B Lip hB hLip width selected label
  exact alignment_countable_lipschitz_observable_compactness
    (fun i => (D i).metric) (fun _ => rfl)
    (fun m i => obs i (width m) (label m i)) B Lip
    (fun m i z => hB i _ _ z)
    (fun m i x y => (hLip i _ _).dist_le_mul x y) selected

/-- The radius, period and rational Haar measures are unchanged. -/
theorem alignment_native_local_haar_subsequence {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h)
    (further : ℕ → ℕ) (hfurther : StrictMono further) :
    NativeResidueLocalHaarLaw D H (L ∘ further) (P ∘ further) M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta ε hε
  obtain ⟨radius, hr, hwin⟩ := hlaw beta ε hε
  refine ⟨radius, hr, ?_⟩
  intro d hd hdM τ hτ hτ1
  exact hfurther.tendsto_atTop.eventually (hwin d hd hdM τ hτ hτ1)

/-- The full joint alpha law, including all cube dimensions and all tests,
survives on the very same extraction used to freeze the observables. -/
theorem alignment_native_alpha_haar_subsequence {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hlaw : NativeCubeBoundedAlphaHaarLaw D H L P M hM sigma hRat h)
    (further : ℕ → ℕ) (hfurther : StrictMono further) :
    NativeCubeBoundedAlphaHaarLaw D H (L ∘ further) (P ∘ further) M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro beta c C hc hC B hB T ε hε
  obtain ⟨α0, hα0, hwin⟩ := hlaw beta c C hc hC B hB T ε hε
  refine ⟨α0, hα0, ?_⟩
  intro α hα hα' t ht hMt
  exact hfurther.tendsto_atTop.eventually (hwin α hα hα' t ht hMt)

end Hindman168
