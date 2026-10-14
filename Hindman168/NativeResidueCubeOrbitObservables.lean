import Hindman168.NativeResidueCubeHaarImage
import Hindman168.NativeCompactFamilyUnitDetection
import Mathlib.Topology.CompactOpen

/-! Actual compact pullback observable families and Haar-image integrals
in the ORIGINAL compatible metrics. No global Lipschitz action is assumed. -/
namespace Hindman168
open Set MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_orbit_metric_joint_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeResidueCubeData D F rho hRat d n e
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun z : D.G × (A.G ⧸ A.Γ) => nativeResidueCubeOrbitMap D F rho hRat d n e z.1 z.2) := by
  let A := nativeResidueCubeData D F rho hRat d n e
  let P (tA : TopologicalSpace (A.G ⧸ A.Γ)) (tD : TopologicalSpace (D.G ⧸ D.Γ)) : Prop :=
    letI := tA
    letI := tD
    Continuous (fun z : D.G × (A.G ⧸ A.Γ) => nativeResidueCubeOrbitMap D F rho hRat d n e z.1 z.2)
  have hn : P (QuotientGroup.instTopologicalSpace A.Γ) (QuotientGroup.instTopologicalSpace D.Γ) := by
    have he : (fun z : D.G × (A.G ⧸ A.Γ) => nativeResidueCubeOrbitMap D F rho hRat d n e z.1 z.2) =
        (fun z => fun V => z.1 • nativeResidueCubeOrbitMap D F rho hRat d n e 1 z.2 V) := by
      funext z V
      obtain ⟨x,hx⟩ := QuotientGroup.mk_surjective z.2
      rw [← hx]
      change (z.1 * nativeCubeVertexHom (G := D.G) d n e x.val V * rho : D.G ⧸ D.Γ) =
        z.1 • (1 * nativeCubeVertexHom (G := D.G) d n e x.val V * rho : D.G ⧸ D.Γ)
      simp only [one_mul, MulAction.Quotient.smul_coe, smul_eq_mul, mul_assoc]
    dsimp only [P]
    rw [he]
    apply continuous_pi
    intro V
    exact continuous_fst.smul ((continuous_apply V).comp
      ((native_residue_cube_orbit_map_continuous D F rho hRat d n e 1).comp continuous_snd))
  exact Eq.mp (congrArg₂ P (nativeNilmanifold_metric_topology A) (nativeNilmanifold_metric_topology D)) hn

noncomputable def nativeResidueCubePullback {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeResidueCubeData D F rho hRat d n e
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ) → D.G → C(A.G ⧸ A.Γ,ℂ) := by
  let A := nativeResidueCubeData D F rho hRat d n e
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  exact fun f h => ⟨fun x => f (nativeResidueCubeOrbitMap D F rho hRat d n e h x),
    f.continuous.comp ((native_residue_cube_orbit_metric_joint_continuous D F d n e rho hRat).comp
      (continuous_const.prodMk continuous_id))⟩

theorem native_residue_cube_pullback_continuous {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let A := nativeResidueCubeData D F rho hRat d n e
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    Continuous (fun z : C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ) × D.G => nativeResidueCubePullback D F d n e rho hRat z.1 z.2) := by
  let A := nativeResidueCubeData D F rho hRat d n e
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : CompactSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_quotient_compact A
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_eval.comp (continuous_fst.fst.prodMk
    ((native_residue_cube_orbit_metric_joint_continuous D F d n e rho hRat).comp
      (continuous_fst.snd.prodMk continuous_snd)))

theorem native_residue_cube_pullback_family_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (K : Set D.G) (hK : IsCompact K) :
    let A := nativeResidueCubeData D F rho hRat d n e
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ U : Set C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ), IsCompact U →
      IsCompact ((fun z : C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ) × D.G => nativeResidueCubePullback D F d n e rho hRat z.1 z.2) ''
        (U ×ˢ K)) := by
  let A := nativeResidueCubeData D F rho hRat d n e
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  dsimp only
  intro U hU
  exact (hU.prod hK).image (native_residue_cube_pullback_continuous D F d n e rho hRat)

theorem native_residue_cube_haar_image_integral {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) :
    let A := nativeResidueCubeData D F rho hRat d n e
    letI : MeasurableSpace D.G := borel D.G
    letI : MeasurableSpace A.E := borel A.E
    letI : MeasurableSpace A.G := borel A.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI := A.metric
    letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
    ∀ f : C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ), (∫ y, f y ∂nativeResidueCubeHaarImage D F rho hRat d n e h) =
      ∫ x, nativeResidueCubePullback D F d n e rho hRat f h x ∂nativeNilmanifoldQuotientProbability A := by
  let A := nativeResidueCubeData D F rho hRat d n e
  letI : MeasurableSpace D.G := borel D.G
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : BorelSpace (A.G ⧸ A.Γ) := native_nilmanifold_metric_coset_borel A
  dsimp only
  intro f
  exact integral_map
    ((native_residue_cube_orbit_metric_joint_continuous D F d n e rho hRat).comp
      (continuous_const.prodMk continuous_id)).measurable.aemeasurable
    f.continuous.aestronglyMeasurable

end Hindman168
