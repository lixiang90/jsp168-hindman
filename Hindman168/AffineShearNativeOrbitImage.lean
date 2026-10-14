import Hindman168.AffineShearNativeImageFiltration
import Hindman168.AffineShearCosetImage
import Hindman168.NativeResidueCubeOrbit
import Hindman168.NativeRationalCubeGroupIdentification

/-! The range of the full marginal cube orbit is exactly the actual native
cube orbit of the constructed image filtration.  The source quotient is the
original one; no independently selected target Haar law is introduced. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three
  pointwiseLieRing pointwiseLieAlgebra nativeFiniteProductRationalModule
  nativeFiniteProduct_topologicalGroup

 theorem affineShear_native_orbit_range {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    range (nativeResidueCubeOrbitMap D F ρ hρ d n e h) =
      (fun z : Finset (Fin d) → D.G => fun V => (h * z V * ρ : D.G ⧸ D.Γ)) ''
        (upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d : Set (Finset (Fin d) → D.G)) := by
  ext y
  constructor
  · rintro ⟨q, rfl⟩
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    refine ⟨nativeCubeVertexHom d n e x.val, ?_, rfl⟩
    rw [← native_rational_cube_group_identification D F d n e]
    exact ⟨x.val, x.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    rw [← native_rational_cube_group_identification D F d n e] at hz
    obtain ⟨g, hg, rfl⟩ := hz
    exact ⟨QuotientGroup.mk ⟨g, hg⟩, rfl⟩

 theorem affineShear_native_orbit_image {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) :
    let F' := affineShearNativeImageFiltration D C F p hp hΓ
    let hρ' := affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ
    (fun y : Finset (Fin d) → D.G ⧸ D.Γ => fun V =>
      affineShearCosetMap D.Γ C.Γ p hΓ (y V)) ''
        range (nativeResidueCubeOrbitMap D F ρ hρ d n e h) =
      range (nativeResidueCubeOrbitMap C F' (p ρ) hρ' d n e (p h)) := by
  dsimp only
  rw [affineShear_native_orbit_range, affineShear_native_orbit_range,
    affineShear_cube_coset_image]
  have hF : (fun i => (nativeRationalSubgroupLayer D F i).map p) =
      nativeRationalSubgroupLayer C (affineShearNativeImageFiltration D C F p hp hΓ) := by
    funext i
    exact (affineShear_native_image_layer D C F p hp hΓ i).symm
  rw [hF]

end Hindman168
