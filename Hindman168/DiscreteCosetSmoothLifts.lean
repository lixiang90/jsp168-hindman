import Hindman168.DiscreteCosetLocalLifts

namespace Hindman168
open Filter Topology
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {M G : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [TopologicalSpace G] [ChartedSpace H' G] [Group G] [LieGroup J ∞ G]

theorem discreteCoset_contMDiffAt_lift (Γ : Subgroup G) [DiscreteTopology Γ]
    {f g : M → G} {x : M} (hf : ContMDiffAt I J ∞ f x) (hg : ContinuousAt g x)
    (hq : ∀ᶠ y in 𝓝 x, (f y : G ⧸ Γ) = (g y : G ⧸ Γ)) :
    ContMDiffAt I J ∞ g x := by
  letI : IsTopologicalGroup G := topologicalGroup_of_lieGroup J ∞
  have he := discreteCoset_lifts_eventually_mul Γ hf.continuousAt hg hq
  exact (hf.mul contMDiffAt_const).congr_of_eventuallyEq he

end Hindman168

