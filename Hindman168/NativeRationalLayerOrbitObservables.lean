import Hindman168.NativeRationalLayerHaarImage
import Hindman168.NativeCompactFamilyUnitDetection
import Mathlib.Topology.CompactOpen

/-! Actual compact pullback observable families and Haar-image integrals
in the ORIGINAL compatible metrics. No global Lipschitz action is assumed. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_rational_layer_orbit_metric_joint_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeRationalLayerOrbitData D F i rho hRat
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun z : D.G × (A.G ⧸ A.Γ) => nativeRationalLayerOrbitMap D F i rho hRat z.1 z.2) := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  let P (tA : TopologicalSpace (A.G ⧸ A.Γ)) (tD : TopologicalSpace (D.G ⧸ D.Γ)) : Prop :=
    letI := tA
    letI := tD
    Continuous (fun z : D.G × (A.G ⧸ A.Γ) => nativeRationalLayerOrbitMap D F i rho hRat z.1 z.2)
  have hn : P (QuotientGroup.instTopologicalSpace A.Γ) (QuotientGroup.instTopologicalSpace D.Γ) :=
    roughConjugateOrbitMap_joint_continuous D.Γ _ _
  exact Eq.mp (congrArg₂ P (nativeNilmanifold_metric_topology A) (nativeNilmanifold_metric_topology D)) hn

noncomputable def nativeRationalLayerPullback {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeRationalLayerOrbitData D F i rho hRat
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    C(D.G ⧸ D.Γ,ℂ) → D.G → C(A.G ⧸ A.Γ,ℂ) := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  exact fun f h => ⟨fun x => f (nativeRationalLayerOrbitMap D F i rho hRat h x),
    f.continuous.comp ((native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
      (continuous_const.prodMk continuous_id))⟩

theorem native_rational_layer_pullback_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeRationalLayerOrbitData D F i rho hRat
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun z : C(D.G ⧸ D.Γ,ℂ) × D.G => nativeRationalLayerPullback D F i rho hRat z.1 z.2) := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_quotient_compact A
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.fst.prodMk
    ((native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
      (continuous_fst.snd.prodMk continuous_snd)))

theorem native_rational_layer_pullback_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (K : Set D.G) (hK : IsCompact K) :
    let A := nativeRationalLayerOrbitData D F i rho hRat
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ U : Set C(D.G ⧸ D.Γ,ℂ), IsCompact U →
      IsCompact ((fun z : C(D.G ⧸ D.Γ,ℂ) × D.G => nativeRationalLayerPullback D F i rho hRat z.1 z.2) ''
        (U ×ˢ K)) := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  dsimp only
  intro U hU
  exact (hU.prod hK).image (native_rational_layer_pullback_continuous D F i rho hRat)

theorem native_rational_layer_haar_image_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i : ℕ) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    let A := nativeRationalLayerOrbitData D F i rho hRat
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ f : C(D.G ⧸ D.Γ,ℂ), (∫ y, f y ∂nativeRationalLayerHaarImage D F i rho hRat h) =
      ∫ x, nativeRationalLayerPullback D F i rho hRat f h x ∂nativeNilmanifoldQuotientProbability A := by
  let A := nativeRationalLayerOrbitData D F i rho hRat
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  dsimp only
  intro f
  exact integral_map
    ((native_rational_layer_orbit_metric_joint_continuous D F i rho hRat).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

end Hindman168
