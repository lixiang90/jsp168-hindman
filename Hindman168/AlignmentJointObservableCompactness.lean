import Hindman168.FiniteObservablePullbackLimits
import Mathlib.Topology.MetricSpace.UniformConvergence

/-! A single further subsequence freezes countably many bounded Lipschitz
observables. The convergence is uniform on each complete quotient, hence
uniform simultaneously over every prescribed reading map and every finite
set of observers. The already selected index sequence is retained literally.
-/
namespace Hindman168
open Filter NNReal
open scoped Topology

/-- Countable compact products yield ONE subsequence for all observers.
The indices of the reading maps need not be countable. -/
theorem alignment_countable_observable_compactness
    {ι : Type*} [Countable ι] {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (K : ∀ i, Set C(X i, ℝ)) (hK : ∀ i, IsCompact (K i))
    (obs : ℕ → ∀ i, C(X i, ℝ)) (hobs : ∀ m i, obs m i ∈ K i)
    (selected : ℕ → ℕ) :
    ∃ limit : ∀ i, C(X i, ℝ), (∀ i, limit i ∈ K i) ∧
      ∃ further : ℕ → ℕ, StrictMono further ∧
        ∀ i, TendstoUniformly (fun m => obs (selected (further m)) i) (limit i) atTop := by
  have hc : IsCompact (Set.pi Set.univ K) := isCompact_univ_pi hK
  have hm : ∀ m, obs (selected m) ∈ Set.pi Set.univ K := fun m i _ => hobs _ i
  obtain ⟨limit, hlimit, further, hfurther, hconv⟩ := hc.tendsto_subseq hm
  refine ⟨limit, (fun i => hlimit i (Set.mem_univ i)), further, hfurther, ?_⟩
  intro i
  have hi := (continuous_apply i).tendsto limit |>.comp hconv
  exact (ContinuousMap.tendsto_iff_tendstoUniformly).mp hi

/-- Arzelà--Ascoli is applied to the actual, fixed metrics and their actual
bounds. This statement assumes no compact hull or convergent observables. -/
theorem alignment_countable_lipschitz_observable_compactness
    {ι : Type*} [Countable ι] {X : ι → Type*}
    [t : ∀ i, TopologicalSpace (X i)] [∀ i, CompactSpace (X i)]
    (M : ∀ i, MetricSpace (X i))
    (ht : ∀ i, t i = (M i).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace)
    (obs : ℕ → ∀ i, C(X i, ℝ)) (B : ι → ℝ) (Lip : ι → ℝ≥0)
    (hB : ∀ m i x, |obs m i x| ≤ B i)
    (hLip : ∀ m i x y, dist (obs m i x) (obs m i y) ≤
      (Lip i : ℝ) * @dist (X i) (M i).toDist x y)
    (selected : ℕ → ℕ) :
    ∃ limit : ∀ i, C(X i, ℝ), ∃ further : ℕ → ℕ, StrictMono further ∧
      ∀ i, TendstoUniformly (fun m => obs (selected (further m)) i) (limit i) atTop := by
  have hh (i : ι) : ∃ K : Set C(X i, ℝ), IsCompact K ∧ ∀ m, obs m i ∈ K := by
    obtain ⟨K, hK, hsub⟩ := compatibleMetric_boundedLipschitz_compact_hull
      (M i) (ht i) (Set.range (fun m => obs m i)) (B i) (Lip i)
      (by rintro f ⟨m, rfl⟩ x; exact hB m i x)
      (by rintro f ⟨m, rfl⟩ x y; exact hLip m i x y)
    exact ⟨K, hK, fun m => hsub ⟨m, rfl⟩⟩
  choose K hK hm using hh
  obtain ⟨limit, _, further, hfurther, hconv⟩ :=
    alignment_countable_observable_compactness K hK obs (fun m i => hm i m) selected
  exact ⟨limit, further, hfurther, hconv⟩

/-- The same uniform limit controls all readings on the SAME joint space,
including stage-dependent maps. No law or subsequence is chosen per reading. -/
theorem alignment_uniform_observers_finite_joint_readings
    {ι Y : Type*} {X J : ι → Type*}
    (obs : ℕ → ∀ i, X i → ℝ) (limit : ∀ i, X i → ℝ)
    (hconv : ∀ i, TendstoUniformly (fun m => obs m i) (limit i) atTop)
    (evals : ∀ i, ℕ → J i → Y → X i) (S : Finset ι)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ i ∈ S, ∀ j y,
      |obs m i (evals i m j y) - limit i (evals i m j y)| < ε := by
  have he : ∀ i ∈ S, ∀ᶠ m in atTop, ∀ x, |obs m i x - limit i x| < ε := by
    intro i _
    simpa only [Real.dist_eq, abs_sub_comm] using
      (Metric.tendstoUniformly_iff.mp (hconv i)) ε hε
  filter_upwards [(Filter.eventually_all_finset S).mpr he] with m hm
  exact fun i hi j y => hm i hi _

/-- Every previously established limit, on any target family, survives the
single further extraction. This includes the full joint probability law. -/
theorem alignment_observable_subsequence_preserves_limits
    {ι : Type*} {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)]
    (value : ∀ i, ℕ → Y i) (limit : ∀ i, Y i) (selected further : ℕ → ℕ)
    (hfurther : StrictMono further)
    (hconv : ∀ i, Tendsto (value i ∘ selected) atTop (𝓝 (limit i))) :
    ∀ i, Tendsto (value i ∘ (selected ∘ further)) atTop (𝓝 (limit i)) :=
  fun i => (hconv i).comp hfurther.tendsto_atTop

end Hindman168
