import Hindman168.AffineShearNativeMarginalImage
import Hindman168.AlignmentCubeUpperFaceReassembly

/-! Actual duplicated-slot symmetries yield the original marginal face
condition and hence a shear in the same, already chosen upstairs coordinates.
Neither a smoothness oracle nor a marginal cube identification is assumed. -/
namespace Hindman168
open Set Module
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ] {σ : ι → Type} {s ℓ : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ k, Fin (n k+1) → σ k → ℤ)
  (hv : ∀ k, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D k).E) (I := (D k).I) (G := (D k).G) (n k) (v k)))
  (index : κ → ι)

 theorem affineShear_alignment_duplicated_slots_face
    (F : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))) ℓ)
    (ρ : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).E)
      (I := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).I)
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ)
    (h : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (d : ℕ) (j : Fin d) (slots : ∀ k, σ (index k) → ℤ)
    (hsym :
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : κ × Finset (Fin d) => index a.1) Prod.snd ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : κ × Finset (Fin d) => D (index a.1))
        (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
        (fun a => if j ∈ a.2 then slots a.1 else 0) '' X = X) :
    let A := nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
    let C := nativeFinitePiData ((fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ∘ index)
    let p := affineShearNativePiRestriction
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) index
    let hp := affineShear_native_pi_restriction_smooth
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) index
    let hΓ := affineShear_native_pi_restriction_lattice
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) index
    let F' := affineShearNativeImageFiltration A C F p hp hΓ
    let hρ' := affineShear_native_hom_rational_hull A C p (hp.mdifferentiable (by norm_num)) hΓ hρ
    let S : C.G ≃* C.G := alignmentJointNativeSlotTranslation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots
    ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer C F') d,
      (fun V => if j ∈ V then
        (S (p h * z V * p ρ) : C.G ⧸ C.Γ)
        else (p h * z V * p ρ : C.G ⧸ C.Γ)) ∈
      range (nativeResidueCubeOrbitMap C F' (p ρ) hρ' d (2^d-1)
        (nativeCubeVertexEnumeration d) (p h)) := by
  let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
  let C := nativeFinitePiData (A ∘ index)
  let p := affineShearNativePiRestriction A index
  let hp := affineShear_native_pi_restriction_smooth A index
  let hΓ := affineShear_native_pi_restriction_lattice A index
  let F' := affineShearNativeImageFiltration (nativeFinitePiData A) C F p hp hΓ
  let hρ' := affineShear_native_hom_rational_hull (nativeFinitePiData A) C p
    (hp.mdifferentiable (by norm_num)) hΓ hρ
  dsimp only
  intro z hz
  have he := affineShear_native_reassembled_marginal_cube A index F ρ hρ d (2^d-1)
    (nativeCubeVertexEnumeration d) h
  have hzrange : (fun V => (p h * z V * p ρ : C.G ⧸ C.Γ)) ∈
      range (nativeResidueCubeOrbitMap C F' (p ρ) hρ' d (2^d-1)
        (nativeCubeVertexEnumeration d) (p h)) := by
    rw [affineShear_native_orbit_range]
    exact ⟨z, hz, rfl⟩
  have hzimage := he.symm ▸ hzrange
  obtain ⟨x, hx, hxe⟩ := hzimage
  let X := range (nativeFinitePiRestrictedCubeProjection A
    (fun a : κ × Finset (Fin d) => index a.1) Prod.snd ∘
      nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
        (nativeCubeVertexEnumeration d) h)
  let T := alignmentJointNativeCosetSlotTranslation
    (fun a : κ × Finset (Fin d) => D (index a.1))
    (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
    (fun a => if j ∈ a.2 then slots a.1 else 0)
  have hin : T x ∈ T '' X := ⟨x, hx, rfl⟩
  have hs : T '' X = X := hsym
  have htx : T x ∈ X := hs.subset hin
  have htimage := Set.mem_image_of_mem (nativeFinitePiCubeReassembly (A ∘ index)) htx
  have htimage' := he ▸ htimage
  have hface := alignment_cube_reassembly_face_translation (D ∘ index) (n ∘ index)
    (fun k => v (index k)) (fun k => hv (index k)) (fun V => j ∈ V) slots x
  have hface' : nativeFinitePiCubeReassembly (A ∘ index)
      (alignmentJointNativeCosetSlotTranslation
        (fun a : κ × Finset (Fin d) => D (index a.1))
        (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
        (fun a => if j ∈ a.2 then slots a.1 else 0) x) =
      fun V => if j ∈ V then alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index)
        (fun k => v (index k)) (fun k => hv (index k)) slots
        (nativeFinitePiCubeReassembly (A ∘ index) x V)
        else nativeFinitePiCubeReassembly (A ∘ index) x V := by
    convert hface using 1
    · rfl
    · congr 2
      funext a
      by_cases ha : j ∈ a.2 <;> simp only [ha, if_true, if_false]
    · apply heq_of_eq
      funext V
      by_cases hV : j ∈ V <;> simp only [hV, if_true, if_false]
      all_goals rfl
  change nativeFinitePiCubeReassembly (A ∘ index) (T x) ∈ _ at htimage'
  dsimp only [T] at htimage'
  rw [hface', hxe] at htimage'
  exact htimage'

end Hindman168
