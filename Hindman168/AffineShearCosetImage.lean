import Hindman168.AffineShearCubeImage
import Mathlib.GroupTheory.Coset.Basic

/-! The full vertexwise image of an original cube coset is exactly the cube
coset of the image filtration.  No surjectivity on the ambient group or
choice of a separate target orbit is required. -/
namespace Hindman168

noncomputable def affineShearCosetMap {G K : Type*} [Group G] [Group K]
    (Γ : Subgroup G) (Λ : Subgroup K) (p : G →* K)
    (hΓ : ∀ g ∈ Γ, p g ∈ Λ) : G ⧸ Γ → K ⧸ Λ :=
  Quotient.map p (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := hΓ (a⁻¹*b) (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul, map_inv] using h)

 theorem affineShearCosetMap_mk {G K : Type*} [Group G] [Group K]
    (Γ : Subgroup G) (Λ : Subgroup K) (p : G →* K)
    (hΓ : ∀ g ∈ Γ, p g ∈ Λ) (g : G) :
    affineShearCosetMap Γ Λ p hΓ (g : G ⧸ Γ) = (p g : K ⧸ Λ) := rfl

 theorem affineShear_cube_coset_image {G K : Type*} [Group G] [Group K]
    (F : ℕ → Subgroup G) (d : ℕ) (Γ : Subgroup G) (Λ : Subgroup K)
    (p : G →* K) (hΓ : ∀ g ∈ Γ, p g ∈ Λ) (h ρ : G) :
    (fun y : Finset (Fin d) → G ⧸ Γ => fun V => affineShearCosetMap Γ Λ p hΓ (y V)) ''
        ((fun z : Finset (Fin d) → G => fun V => (h * z V * ρ : G ⧸ Γ)) ''
          (upperFaceCubeGroup F d : Set (Finset (Fin d) → G))) =
      (fun z : Finset (Fin d) → K => fun V => (p h * z V * p ρ : K ⧸ Λ)) ''
        (upperFaceCubeGroup (fun i => (F i).map p) d : Set (Finset (Fin d) → K)) := by
  rw [← affineShear_cube_image, Subgroup.coe_map, Set.image_image, Set.image_image]
  congr 1
  funext z V
  simp only [affineShearCosetMap_mk, map_mul]
  rfl

end Hindman168
