import Hindman168.NilObservableCompactHulls
import Mathlib.Topology.Sequences

namespace Hindman168
open Filter NNReal
open scoped Topology

/-- Compactness is preserved in the product of all prescribed reading spaces.
No Lipschitz bound for an evaluation map is assumed or inferred. -/
theorem observable_pullback_family_compact {X Y J : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (evals : J → C(Y, X)) (H : Set C(X, ℝ)) (hH : IsCompact H) :
    IsCompact ((fun f : C(X, ℝ) => fun j => f.comp (evals j)) '' H) := by
  exact hH.image (continuous_pi (fun j => ContinuousMap.continuous_precomp (evals j)))

theorem observable_pullback_uniform_subsequence {X Y J : Type*}
    [TopologicalSpace X] [CompactSpace X]
    (evals : J → Y → X) (H : Set C(X, ℝ)) (hH : IsCompact H)
    (f : ℕ → C(X, ℝ)) (hf : ∀ k, f k ∈ H) :
    ∃ g ∈ H, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ j y,
        |f (φ k) (evals j y) - g (evals j y)| < ε := by
  obtain ⟨g, hg, φ, hφ, hlim⟩ := hH.tendsto_subseq hf
  refine ⟨g, hg, φ, hφ, ?_⟩
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with k hk
  intro j y
  have h := (ContinuousMap.dist_apply_le_dist (f := f (φ k)) (g := g) (evals j y)).trans_lt hk
  simpa only [Real.dist_eq] using h

theorem compatibleMetric_observable_pullback_subsequence {X Y J : Type*}
    [t : TopologicalSpace X] [CompactSpace X] (M : MetricSpace X)
    (ht : t = M.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (evals : J → Y → X) (f : ℕ → C(X, ℝ)) (B : ℝ) (L : ℝ≥0)
    (hB : ∀ k x, |f k x| ≤ B)
    (hL : ∀ k x y, dist (f k x) (f k y) ≤ (L : ℝ) * @dist X M.toDist x y) :
    ∃ g : C(X, ℝ), ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, ∀ j y,
        |f (φ k) (evals j y) - g (evals j y)| < ε := by
  have hb : ∀ g ∈ Set.range f, ∀ x, |g x| ≤ B := by
    rintro g ⟨k, rfl⟩ x
    exact hB k x
  have hl : ∀ g ∈ Set.range f, ∀ x y,
      dist (g x) (g y) ≤ (L : ℝ) * @dist X M.toDist x y := by
    rintro g ⟨k, rfl⟩ x y
    exact hL k x y
  obtain ⟨H, hH, hsub⟩ := compatibleMetric_boundedLipschitz_compact_hull M ht (Set.range f) B L hb hl
  obtain ⟨g, _, φ, hφ, hlim⟩ := observable_pullback_uniform_subsequence evals H hH f
    (fun k => hsub ⟨k, rfl⟩)
  exact ⟨g, φ, hφ, hlim⟩

end Hindman168
