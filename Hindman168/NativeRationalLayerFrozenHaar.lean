import Hindman168.NativeRationalLayerCompactWindowHaar
import Hindman168.NativeRationalLayerOrbitObservables

/-! Actual original-space window laws with frozen left factor, uniformly
over a genuine compact factor set and compact original observable family.
The target is the canonical ORIGINAL subgroup Haar image. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_frozen_window_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (d : ℚ) (hd : d ≠ 0) (τ : ℝ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (K : Set D.G) (hK : IsCompact K) (δ : ℝ) (hδ : 0 < δ) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ U : Set C(D.G ⧸ D.Γ,ℂ), IsCompact U →
    ∀ᶠ n in atTop, ∀ b : ℝ, ∀ m : ℕ, τ*L n ≤ m → ∀ h ∈ K, ∀ f ∈ U,
      ‖finiteComplexSetMean (scalarMvIntegerCube Unit m)
        (fun x => f (h * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
          (roughVectorMvEval (E := D.E) (p n) (fun i => b+(d : ℝ)*(x i : ℝ))) * rho : D.G ⧸ D.Γ)) -
          ∫ y, f y ∂nativeRationalLayerHaarImage D F 0 rho hRat h‖ < δ := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro U hU
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  let H := (fun z : C(D.G ⧸ D.Γ,ℂ) × D.G => nativeRationalLayerPullback D F 0 rho hRat z.1 z.2) '' (U ×ˢ K)
  have hH : IsCompact H := native_rational_layer_pullback_family_compact D F 0 rho hRat K hK U hU
  have h := native_rational_layer_compact_window_haar D F rho hRat L hL p hp hIrr d hd τ hτ hτ1 δ hδ H hH
  filter_upwards [h] with n hn
  intro b m hm h hh f hf
  have hg := hn b m hm (nativeRationalLayerPullback D F 0 rho hRat f h) ⟨(f,h),⟨hf,hh⟩,rfl⟩
  rw [native_rational_layer_haar_image_integral D F 0 rho hRat h f]
  simpa only [nativeRationalLayerPullback, ContinuousMap.coe_mk, native_rational_layer_orbit_map_mk,
    native_rational_subgroup_polynomial_orbit_original] using hg

end Hindman168
