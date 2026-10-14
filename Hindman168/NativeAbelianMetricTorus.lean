import Hindman168.NativeAbelianTorusEquivalence
import Hindman168.NativeMetricMaskModelTesting
import Hindman168.CompactUnitLipschitzObservables

/-! Transport the actual abelian quotient homeomorphism into the specified
compatible metric. Pullback of the original observable family is compact;
no Lipschitz estimate for the homeomorphism is asserted. -/

namespace Hindman168
open scoped Classical Manifold ContDiff Topology
universe u

noncomputable def nativeAbelianMetricTorusHomeomorph (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    (D.G ⧸ D.Γ) ≃ₜ UnitAddTorus ↥(nativeFilteredHorizontalIndices (I := D.I) D.Γ) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D)) D.quotientCompact
  let e := Equiv.ofBijective (nativeHorizontalTorusCosetMap (I := D.I) D.Γ)
    ⟨native_abelian_horizontal_torus_coset_injective (I := D.I) D.Γ D.step_le,
      native_horizontal_torus_coset_map_surjective (I := D.I) D.Γ⟩
  have he : Continuous e := D.metric_quotientMap.isQuotientMap.continuous_iff.mpr
    (native_horizontal_torus_projection_continuous (I := D.I) D.Γ)
  exact e.toHomeomorphOfContinuousClosed he he.isClosedMap

theorem native_abelian_metric_torus_homeomorph_mk (D : NativeNilmanifoldData.{u} 1) (g : D.G) :
    nativeAbelianMetricTorusHomeomorph D (g : D.G ⧸ D.Γ) =
      nativeHorizontalTorusProjection (I := D.I) D.Γ g := rfl

theorem native_abelian_metric_quotient_compact (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    CompactSpace (D.G ⧸ D.Γ) := by
  exact Eq.mp (congrArg (fun t : TopologicalSpace (D.G ⧸ D.Γ) =>
    @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D)) D.quotientCompact

theorem native_abelian_metric_observables_pullback_compact (D : NativeNilmanifoldData.{u} 1) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    IsCompact ((fun F : C(D.G ⧸ D.Γ, ℂ) =>
      F.comp ⟨(nativeAbelianMetricTorusHomeomorph D).symm,
        (nativeAbelianMetricTorusHomeomorph D).symm.continuous⟩) ''
        unitLipschitzObservables (D.G ⧸ D.Γ)) := by
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  exact (unit_lipschitz_observables_compact (D.G ⧸ D.Γ)).image
    (ContinuousMap.continuous_precomp ⟨(nativeAbelianMetricTorusHomeomorph D).symm,
      (nativeAbelianMetricTorusHomeomorph D).symm.continuous⟩)

end Hindman168
