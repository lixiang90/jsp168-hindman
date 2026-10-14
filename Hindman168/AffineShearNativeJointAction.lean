import Hindman168.AffineShearNativeOriginalAction
import Hindman168.AffineShearNativeImageSection
import Hindman168.AffineShearWeightedSection

/-! Proposition 7.5's genuine joint Lie-algebra shear lift.  The projection
is the original lattice-compatible group homomorphism and its image
filtration is constructed.  One upstairs adapted basis, one section and one
weighted shear group work simultaneously for every face-preserving S.
The input face condition is the actual marginal cube orbit, which the
separate full-marginal image theorem identifies with the original source. -/
namespace Hindman168
open Set Module
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

 theorem affineShear_native_joint_face_lifts_in_coordinates {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (h : D.G)
    (n : ℕ) (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E)
    (w : Fin n → ℕ)
    (hb : ∀ i, 1 ≤ w i ∧ w i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration D F ρ hρ (w i) ∧
      affineShearNativeInitialFiltration D F ρ hρ (w i+1) ≤ (b.coord i).ker) :
    let F' := affineShearNativeImageFiltration D C F p hp hΓ
    let hρ' := affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ
    let K := nativeRationalLayerOrbitData D F 1 ρ hρ
      ∀ S : C.G ≃* C.G, MDifferentiable C.I C.I (S : C.G → C.G) →
        (∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
          ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer C F') d,
            (fun V => if j ∈ V then (S (p h * z V * p ρ) : C.G ⧸ C.Γ)
              else (p h * z V * p ρ : C.G ⧸ C.Γ)) ∈
                range (nativeResidueCubeOrbitMap C F' (p ρ) hρ' d (2^d-1)
                  (nativeCubeVertexEnumeration d) (p h))) →
        ∃ U : weightedShearGroup (R := ℝ) w, ∀ x : Fin n → ℝ,
          (p h * p (nativeLieExponential (I := K.I) (G := K.G)
              (b.equivFun.symm (U • x))).val * p ρ : C.G ⧸ C.Γ) =
            (S (p h * p (nativeLieExponential (I := K.I) (G := K.G)
              (b.equivFun.symm x)).val * p ρ) : C.G ⧸ C.Γ) := by
  let F' := affineShearNativeImageFiltration D C F p hp hΓ
  let hρ' := affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ
  let K := nativeRationalLayerOrbitData D F 1 ρ hρ
  let J := nativeRationalLayerOrbitData C F' 1 (p ρ) hρ'
  let P := affineShearNativeInitialProjection D C F p hp hΓ ρ hρ
  let FK := affineShearNativeInitialFiltration D F ρ hρ
  let FJ := affineShearNativeInitialFiltration C F' (p ρ) hρ'
  have himage : ∀ i, (FK i).map P = FJ i :=
    affineShear_native_initial_projection_layers D C F p hp hΓ ρ hρ
  obtain ⟨m, c, v, hc⟩ := affineShear_native_initial_adapted_basis C F' (p ρ) hρ'
  have hcb : ∀ i, c i ∈ (FK (v i)).map P := by
    intro i
    rw [himage]
    exact (hc i).2.2.1
  have hcc : ∀ i z, z ∈ (FK (v i+1)).map P → c.coord i z = 0 := by
    intro i z hz
    rw [himage] at hz
    exact (hc i).2.2.2 hz
  obtain ⟨R, hR, hRlevels, hlift⟩ := affineShear_weighted_section_lifts ℓ w v
    (fun i => (hc i).1) FK (affineShear_native_initial_antitone D F ρ hρ)
    (affineShear_native_initial_terminal D F ρ hρ) P
    (affineShear_native_initial_projection_surjective D C F p hp hΓ ρ hρ) b c
    (fun i => (hb i).2.2.1) hcb (fun i z hz => (hb i).2.2.2 hz) hcc
  dsimp only
  intro S hS hfaces
  obtain ⟨T, hT⟩ := affineShear_native_original_faces_shear_in_coordinates C F' (p ρ) hρ'
    (p h) S hS hfaces m c v hc
  obtain ⟨U, _, hprojection⟩ := hlift T
  refine ⟨U, ?_⟩
  intro x
  have he : P (b.equivFun.symm (U • x)) =
      c.equivFun.symm (T • c.equivFun (P (b.equivFun.symm x))) := by
    apply c.equivFun.injective
    rw [LinearEquiv.apply_symm_apply]
    exact hprojection x
  rw [affineShear_native_initial_projection_exponential D C F p hp hΓ ρ hρ,
    affineShear_native_initial_projection_exponential D C F p hp hΓ ρ hρ]
  rw [he]
  simpa only [LinearEquiv.symm_apply_apply] using hT (c.equivFun (P (b.equivFun.symm x)))

 theorem affineShear_native_joint_face_lifts {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (h : D.G) :
    let F' := affineShearNativeImageFiltration D C F p hp hΓ
    let hρ' := affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ
    let K := nativeRationalLayerOrbitData D F 1 ρ hρ
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℝ K.E, ∃ weights : Fin n → ℕ,
      (∀ i, 1 ≤ weights i ∧ weights i ≤ ℓ ∧
        b i ∈ affineShearNativeInitialFiltration D F ρ hρ (weights i) ∧
        affineShearNativeInitialFiltration D F ρ hρ (weights i+1) ≤ (b.coord i).ker) ∧
      ∀ S : C.G ≃* C.G, MDifferentiable C.I C.I (S : C.G → C.G) →
        (∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
          ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer C F') d,
            (fun V => if j ∈ V then (S (p h * z V * p ρ) : C.G ⧸ C.Γ)
              else (p h * z V * p ρ : C.G ⧸ C.Γ)) ∈
                range (nativeResidueCubeOrbitMap C F' (p ρ) hρ' d (2^d-1)
                  (nativeCubeVertexEnumeration d) (p h))) →
        ∃ U : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
          (p h * p (nativeLieExponential (I := K.I) (G := K.G)
              (b.equivFun.symm (U • x))).val * p ρ : C.G ⧸ C.Γ) =
            (S (p h * p (nativeLieExponential (I := K.I) (G := K.G)
              (b.equivFun.symm x)).val * p ρ) : C.G ⧸ C.Γ) := by
  obtain ⟨n, b, w, hb⟩ := affineShear_native_initial_adapted_basis D F ρ hρ
  refine ⟨n, b, w, hb, ?_⟩
  exact affineShear_native_joint_face_lifts_in_coordinates D C F p hp hΓ ρ hρ h n b w hb

end Hindman168
