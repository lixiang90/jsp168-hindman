import Mathlib.Topology.Covering.Quotient
import Mathlib.Geometry.Manifold.Algebra.LieGroup

namespace Hindman168
open Filter Topology
open scoped Manifold ContDiff

variable {X G : Type*} [TopologicalSpace X] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G]

theorem discreteCoset_lifts_eventually_mul (Γ : Subgroup G) [DiscreteTopology Γ]
    {f g : X → G} {x : X} (hf : ContinuousAt f x) (hg : ContinuousAt g x)
    (hq : ∀ᶠ y in 𝓝 x, (f y : G ⧸ Γ) = (g y : G ⧸ Γ)) :
    ∀ᶠ y in 𝓝 x, g y = f y * ((f x)⁻¹ * g x) := by
  have hm : ∀ᶠ y in 𝓝 x, (f y)⁻¹ * g y ∈ Γ :=
    hq.mono (fun _ h => QuotientGroup.eq.mp h)
  have hx : (f x)⁻¹ * g x ∈ Γ := hm.self_of_nhds
  have ht : Tendsto (fun y => (f y)⁻¹ * g y) (𝓝 x)
      (𝓝[(Γ : Set G)] ((f x)⁻¹ * g x)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hf.inv.mul hg, hm⟩
  have hd : IsDiscrete (Γ : Set G) := isDiscrete_iff_discreteTopology.mpr inferInstance
  rw [hd.nhdsWithin _ hx] at ht
  have he := tendsto_pure.mp ht
  exact he.mono (fun y hy => by rw [← hy, mul_inv_cancel_left])

end Hindman168
