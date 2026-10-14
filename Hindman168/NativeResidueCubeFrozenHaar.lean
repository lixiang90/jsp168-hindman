import Hindman168.NativeResidueCubeCompactHaar
import Hindman168.NativeResidueCubeOrbitObservables

/-! Actual cube Haar images in the ORIGINAL ambient quotient, uniform over
compact left-factor and continuous-observable families. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_residue_cube_frozen_progression_haar {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ m, RoughVectorMvWeightedDegree F.layer (p m) 0)
    (hIrr : NativeSubgroupSequentialIrrational D F L p)
    (t : ℕ) (ht : 0 < t)
    (c R η : ℝ) (hc : 0 < c) (hR : 0 ≤ R) (hη : 0 < η)
    (K : Set D.G) (hK : IsCompact K) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ U : Set C((Finset (Fin d) → D.G ⧸ D.Γ), ℂ), IsCompact U →
    ∀ᶠ m in atTop, ∀ lo hi v : Fin (d+1) → ℤ,
      (∀ i, c*L m ≤ (hi i : ℝ)-lo i ∧ (hi i : ℝ)-lo i ≤ R*L m) →
      (∀ i, |(lo i : ℝ)| ≤ R*L m ∧ |(hi i : ℝ)| ≤ R*L m) →
      ∀ h ∈ K, ∀ f ∈ U,
        ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
          (fun x => f (fun V => (h * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p m) (fun _ => (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))) * ρ : D.G ⧸ D.Γ))) -
              ∫ y, f y ∂nativeResidueCubeHaarImage D F ρ hρ d n e h‖ < η := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro U hU
  let A := nativeResidueCubeData D F ρ hρ d n e
  letI : MeasurableSpace A.E := borel A.E
  letI : MeasurableSpace A.G := borel A.G
  letI := A.metric
  letI : TopologicalSpace (A.G ⧸ A.Γ) := A.metric.toUniformSpace.toTopologicalSpace
  let H := (fun z : C((Finset (Fin d) → D.G ⧸ D.Γ),ℂ) × D.G =>
    nativeResidueCubePullback D F d n e ρ hρ z.1 z.2) '' (U ×ˢ K)
  have hH : IsCompact H := native_residue_cube_pullback_family_compact D F d n e ρ hρ K hK U hU
  have hq := native_residue_cube_compact_progression_haar D F ρ hρ d n e L hL p hp hIrr
    t ht c R η hc hR hη H hH
  filter_upwards [hq] with m hm
  intro lo hi v hlen hloc h hh f hf
  have hg := hm lo hi v hlen hloc 0 (nativeResidueCubePullback D F d n e ρ hρ f h)
    ⟨(f,h),⟨hf,hh⟩,rfl⟩
  rw [native_residue_cube_haar_image_integral D F d n e ρ hρ h f]
  have he : ∀ x : Fin (d+1) → ℤ,
      nativeResidueCubeOrbitMap D F ρ hρ d n e h
        (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
          (fun i => i.elim 0 (fun j => (x j : ℝ))) : A.G ⧸ A.Γ) =
      (fun V => (h * nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
        (roughVectorMvEval (E := D.E) (p m) (fun _ => (x 0 : ℝ) + ∑ i ∈ V, (x i.succ : ℝ))) * ρ : D.G ⧸ D.Γ)) := by
    intro x
    funext V
    rw [native_residue_cube_orbit_map_mk]
    have hv := native_residue_cube_spatial_original_vertices D F ρ hρ d n e (p m) (hp m)
      0 (fun j => (x j : ℝ)) (e.symm V)
    simp only [Equiv.apply_symm_apply] at hv
    change nativeCubeVertexHom (G := D.G) d n e
      (nativeResidueCubeSpatialOrbit D F ρ hρ d n e (p m) (hp m)
        (fun i => i.elim 0 (fun j => (x j : ℝ)))).val V = _ at hv
    rw [hv]
  simpa only [nativeResidueCubePullback, ContinuousMap.coe_mk, he] using hg

end Hindman168
