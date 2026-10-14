import Hindman168.PositivePrincipalSumMassCover

/-! The exact closed/open threshold buffers of (8.22)--(8.24). Boolean
palette equality is only used for the limiting closed comparisons; it is
not demanded of the prelimit model functions. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

def principalClosedComparisons {X O : Type*} {J : O → Type*}
    (θ : ℝ) (c t : ∀ o, J o → X → ℝ) (o : O) : Set X :=
  {x | ∀ j, c o j x ≤ 3*θ/2 ∨ 3*θ/2 ≤ t o j x}

def principalOpenComparisons {X O : Type*} {J : O → Type*}
    (θ : ℝ) (c t : ∀ o, J o → X → ℝ) (o : O) : Set X :=
  {x | ∀ j, c o j x < 7*θ/4 ∨ 5*θ/4 < t o j x}

def principalActualComparisons {X O : Type*} {J : O → Type*}
    (θ : ℝ) (c t : ∀ o, J o → X → ℝ) : Set X :=
  {x | ∃ o, ∀ j, 2*θ < c o j x → θ < t o j x}

theorem principal_closed_comparisons_isClosed {X O : Type*} [TopologicalSpace X]
    {J : O → Type*} (θ : ℝ) (c t : ∀ o, J o → X → ℝ)
    (hc : ∀ o j, Continuous (c o j)) (ht : ∀ o j, Continuous (t o j)) (o : O) :
    IsClosed (principalClosedComparisons θ c t o) := by
  have h := isClosed_iInter (fun j : J o =>
    (isClosed_le (hc o j) (continuous_const (y := 3*θ/2))).union
      (isClosed_le (continuous_const (y := 3*θ/2)) (ht o j)))
  simpa only [principalClosedComparisons, Set.setOf_forall, Set.setOf_or] using h

theorem principal_open_comparisons_isOpen {X O : Type*} [TopologicalSpace X]
    {J : O → Type*} [∀ o, Finite (J o)] (θ : ℝ) (c t : ∀ o, J o → X → ℝ)
    (hc : ∀ o j, Continuous (c o j)) (ht : ∀ o j, Continuous (t o j)) (o : O) :
    IsOpen (principalOpenComparisons θ c t o) := by
  have h := isOpen_iInter_of_finite (fun j : J o =>
    (isOpen_lt (hc o j) (continuous_const (y := 7*θ/4))).union
      (isOpen_lt (continuous_const (y := 5*θ/4)) (ht o j)))
  simpa only [principalOpenComparisons, Set.setOf_forall, Set.setOf_or] using h

theorem principal_closed_subset_open {X O : Type*} {J : O → Type*}
    {θ : ℝ} (hθ : 0 < θ) (c t : ∀ o, J o → X → ℝ) (o : O) :
    principalClosedComparisons θ c t o ⊆ principalOpenComparisons θ c t o := by
  intro x hx j
  rcases hx j with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

/-- Palette equality yields the weak closed alternatives, including equality
at the threshold; this is the only use of Boolean comparisons. -/
theorem principal_palette_implies_closed {X O : Type*} {J : O → Type*}
    (θ : ℝ) (c t : ∀ o, J o → X → ℝ) (o : O) (x : X)
    (h : ∀ j, decide (3*θ/2 < c o j x) = decide (3*θ/2 < t o j x)) :
    x ∈ principalClosedComparisons θ c t o := by
  intro j
  by_cases hc : 3*θ/2 < c o j x
  · have ht : 3*θ/2 < t o j x := by
      have he : decide (3*θ/2 < t o j x) = true := (h j).symm.trans (by simpa using hc)
      exact of_decide_eq_true he
    exact Or.inr ht.le
  · exact Or.inl (le_of_not_gt hc)

theorem principal_open_subset_actual {X O : Type*} {J : O → Type*}
    (θ : ℝ) (c t c' t' : ∀ o, J o → X → ℝ)
    (hc : ∀ o j x, |c' o j x - c o j x| < θ/4)
    (ht : ∀ o j x, |t' o j x - t o j x| < θ/4) :
    (⋃ o, principalOpenComparisons θ c t o) ⊆ principalActualComparisons θ c' t' := by
  intro x hx
  obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hx
  refine ⟨o, ?_⟩
  intro j hcenter
  rcases ho j with h | h
  · have he := (abs_lt.mp (hc o j x)).2
    linarith
  · have he := (abs_lt.mp (ht o j x)).1
    linarith

/-- Open-set Portmanteau and the original θ/4 uniform-error budget give
positive actual implications, without prelimit palette equality. -/
theorem principal_open_mass_yields_actual_liminf {X O I : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {J : O → Type*} [∀ o, Finite (J o)]
    (L : Filter I) (ν : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto ν L (𝓝 μ)) (θ : ℝ) (c t : ∀ o, J o → X → ℝ)
    (hc : ∀ o j, Continuous (c o j)) (ht : ∀ o j, Continuous (t o j))
    (c' t' : I → ∀ o, J o → X → ℝ)
    (herr : ∀ᶠ k in L, (∀ o j x, |c' k o j x - c o j x| < θ/4) ∧
      (∀ o j x, |t' k o j x - t o j x| < θ/4)) :
    (μ : Measure X) (⋃ o, principalOpenComparisons θ c t o) ≤
      L.liminf (fun k => (ν k : Measure X) (principalActualComparisons θ (c' k) (t' k))) := by
  have hop := isOpen_iUnion (principal_open_comparisons_isOpen θ c t hc ht)
  have hport := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim hop
  exact hport.trans (liminf_le_liminf (herr.mono (fun k hk =>
    measure_mono (principal_open_subset_actual θ c t (c' k) (t' k) hk.1 hk.2))))

theorem principal_closed_mass_yields_actual_liminf {X O I : Type*}
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    {J : O → Type*} [∀ o, Finite (J o)]
    (L : Filter I) (ν : I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (hlim : Tendsto ν L (𝓝 μ)) (θ : ℝ) (hθ : 0 < θ)
    (c t : ∀ o, J o → X → ℝ)
    (hc : ∀ o j, Continuous (c o j)) (ht : ∀ o j, Continuous (t o j))
    (c' t' : I → ∀ o, J o → X → ℝ)
    (herr : ∀ᶠ k in L, (∀ o j x, |c' k o j x - c o j x| < θ/4) ∧
      (∀ o j x, |t' k o j x - t o j x| < θ/4))
    (δ : ℝ≥0∞) (hmass : δ ≤ (μ : Measure X) (⋃ o, principalClosedComparisons θ c t o)) :
    δ ≤ L.liminf (fun k => (ν k : Measure X) (principalActualComparisons θ (c' k) (t' k))) := by
  have hsubset : (⋃ o, principalClosedComparisons θ c t o) ⊆
      ⋃ o, principalOpenComparisons θ c t o := by
    intro x hx
    obtain ⟨o, ho⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨o, principal_closed_subset_open hθ c t o ho⟩
  exact (hmass.trans (measure_mono hsubset)).trans
    (principal_open_mass_yields_actual_liminf L ν μ hlim θ c t hc ht c' t' herr)

end Hindman168
