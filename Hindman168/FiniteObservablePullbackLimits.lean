import Hindman168.ObservablePullbackCompactness

namespace Hindman168
open Filter NNReal
open scoped Topology

theorem finite_observable_pullback_uniform_subsequence
    {ι Y : Type*} [Fintype ι] {X J : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (evals : ∀ i, J i → Y → X i)
    (H : ∀ i, Set C(X i, ℝ)) (hH : ∀ i, IsCompact (H i))
    (f : ℕ → ∀ i, C(X i, ℝ)) (hf : ∀ k i, f k i ∈ H i) :
    ∃ g : ∀ i, C(X i, ℝ), (∀ i, g i ∈ H i) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i j y,
        |f (φ k) i (evals i j y) - g i (evals i j y)| < ε := by
  have hc : IsCompact (Set.pi Set.univ H) := isCompact_univ_pi hH
  have hm : ∀ k, f k ∈ Set.pi Set.univ H := fun k i _ => hf k i
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hc.tendsto_subseq hm
  refine ⟨g, (fun i => hg i (Set.mem_univ i)), φ, hφ, ?_⟩
  intro ε hε
  apply eventually_all.mpr
  intro i
  have hi := (continuous_apply i).tendsto g |>.comp hlim
  filter_upwards [(Metric.tendsto_nhds.mp hi) ε hε] with k hk
  intro j y
  have h := (ContinuousMap.dist_apply_le_dist (f := f (φ k) i) (g := g i) (evals i j y)).trans_lt hk
  simpa only [Real.dist_eq] using h

theorem finite_compatibleMetric_pullback_subsequence
    {ι Y : Type*} [Fintype ι] {X J : ι → Type*}
    [t : ∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (M : ∀ i, MetricSpace (X i))
    (ht : ∀ i, t i = (M i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (evals : ∀ i, J i → Y → X i) (f : ℕ → ∀ i, C(X i, ℝ))
    (B : ι → ℝ) (L : ι → ℝ≥0)
    (hB : ∀ k i x, |f k i x| ≤ B i)
    (hL : ∀ k i x y, dist (f k i x) (f k i y) ≤ (L i : ℝ) * @dist (X i) (M i).toDist x y) :
    ∃ g : ∀ i, C(X i, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ i j y,
        |f (φ k) i (evals i j y) - g i (evals i j y)| < ε := by
  have hh (i : ι) : ∃ H : Set C(X i, ℝ), IsCompact H ∧ ∀ k, f k i ∈ H := by
    have hb : ∀ g ∈ Set.range (fun k => f k i), ∀ x, |g x| ≤ B i := by
      rintro g ⟨k, rfl⟩ x
      exact hB k i x
    have hl : ∀ g ∈ Set.range (fun k => f k i), ∀ x y,
        dist (g x) (g y) ≤ (L i : ℝ) * @dist (X i) (M i).toDist x y := by
      rintro g ⟨k, rfl⟩ x y
      exact hL k i x y
    obtain ⟨H, hH, hsub⟩ := compatibleMetric_boundedLipschitz_compact_hull
      (M i) (ht i) (Set.range (fun k => f k i)) (B i) (L i) hb hl
    exact ⟨H, hH, fun k => hsub ⟨k, rfl⟩⟩
  choose H hH hm using hh
  obtain ⟨g, _, φ, hφ, hlim⟩ := finite_observable_pullback_uniform_subsequence evals H hH f
    (fun k i => hm i k)
  exact ⟨g, φ, hφ, hlim⟩

end Hindman168
