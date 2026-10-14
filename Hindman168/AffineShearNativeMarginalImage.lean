import Hindman168.AffineShearNativePiRestriction
import Hindman168.AffineShearNativeOrbitImage
import Hindman168.NativeFinitePiCubeReassembly

/-! Concrete bridge from the original repeated binary slots to the actual
full marginal native cube orbit.  The quotient reassembly, group projection,
image filtration and rational residue are all the original constructions. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

 theorem affineShear_native_pi_coset_map {ι κ : Type} [Fintype ι] [Fintype κ]
    {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι) :
    affineShearCosetMap (nativeFinitePiData D).Γ (nativeFinitePiData (D ∘ index)).Γ
        (affineShearNativePiRestriction D index) (affineShear_native_pi_restriction_lattice D index) =
      nativeFinitePiCosetRestriction D index := by
  funext x
  induction x using Quotient.inductionOn with
  | _ g =>
    rw [affineShearCosetMap_mk, native_finite_pi_coset_restriction_mk]
    rfl

 theorem affineShear_native_reassembled_marginal_cube {ι κ : Type} [Fintype ι] [Fintype κ]
    {s ℓ : ℕ} (D : ι → NativeNilmanifoldData.{u} s) (index : κ → ι)
    (F : NativeRationalSubgroupFiltration (nativeFinitePiData D) ℓ)
    (ρ : (nativeFinitePiData D).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull (E := (nativeFinitePiData D).E)
      (I := (nativeFinitePiData D).I) (nativeFinitePiData D).Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : (nativeFinitePiData D).G) :
    let A := nativeFinitePiData D
    let B := nativeFinitePiData (D ∘ index)
    let p := affineShearNativePiRestriction D index
    let hp := affineShear_native_pi_restriction_smooth D index
    let hΓ := affineShear_native_pi_restriction_lattice D index
    let F' := affineShearNativeImageFiltration A B F p hp hΓ
    let hρ' := affineShear_native_hom_rational_hull A B p (hp.mdifferentiable (by norm_num)) hΓ hρ
    nativeFinitePiCubeReassembly (D ∘ index) ''
      range (nativeFinitePiRestrictedCubeProjection D
        (fun a : κ × Finset (Fin d) => index a.1) Prod.snd ∘
          nativeResidueCubeOrbitMap A F ρ hρ d n e h) =
      range (nativeResidueCubeOrbitMap B F' (p ρ) hρ' d n e (p h)) := by
  dsimp only
  refine (native_finite_pi_repeated_projection_range D index
    (nativeResidueCubeOrbitMap (nativeFinitePiData D) F ρ hρ d n e h)).trans ?_
  have he := affineShear_native_orbit_image (nativeFinitePiData D) (nativeFinitePiData (D ∘ index)) F
    (affineShearNativePiRestriction D index) (affineShear_native_pi_restriction_smooth D index)
    (affineShear_native_pi_restriction_lattice D index) ρ hρ d n e h
  refine Eq.trans ?_ he
  rw [← Set.range_comp]
  apply congrArg Set.range
  funext x V
  exact (congrFun (affineShear_native_pi_coset_map D index)
    (nativeResidueCubeOrbitMap (nativeFinitePiData D) F ρ hρ d n e h x V)).symm

end Hindman168
