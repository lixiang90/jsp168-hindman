import Hindman168.AffineShearNativeOriginalGraded
import Hindman168.AffineShearNativeInitialLayer
import Hindman168.WeightedShearNativeAffine

/-! The actual automorphism appearing in Proposition 7.5 acts, in constructed
adapted coordinates of the original proper subgroup J, by an element of the
strict weighted polynomial-shear group.  The only action hypothesis is the
original preservation of native quotient cube faces. -/
namespace Hindman168
open Function Set Module
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

 theorem affineShear_native_original_faces_shear_in_coordinates {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) (S : D.G ≃* D.G)
    (hS : MDifferentiable D.I D.I (S : D.G → D.G))
    (hfaces : ∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
      ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d,
        (fun V => if j ∈ V then (S (h * z V * ρ) : D.G ⧸ D.Γ)
          else (h * z V * ρ : D.G ⧸ D.Γ)) ∈
            range (nativeResidueCubeOrbitMap D F ρ hρ d (2^d-1)
              (nativeCubeVertexEnumeration d) h))
    (n : ℕ) (b : Basis (Fin n) ℝ (nativeRationalLayerOrbitData D F 1 ρ hρ).E)
    (weights : Fin n → ℕ)
    (hb : ∀ i, 1 ≤ weights i ∧ weights i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration D F ρ hρ (weights i) ∧
      affineShearNativeInitialFiltration D F ρ hρ (weights i+1) ≤ (b.coord i).ker) :
    let C := nativeRationalLayerOrbitData D F 1 ρ hρ
    ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
        (h * (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm (f • x))).val * ρ :
            D.G ⧸ D.Γ) =
          (S (h * (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm x)).val * ρ) :
            D.G ⧸ D.Γ) := by
  let C := nativeRationalLayerOrbitData D F 1 ρ hρ
  let L := nativeRationalSubgroupLayerAlgebra D F 1
  let P := affineShearNativeInitialFiltration D F ρ hρ
  obtain ⟨c, hc, hbase, hpres, hgraded⟩ :=
    affineShear_native_original_faces_restrict_and_graded D F ρ hρ h S hS hfaces
  let φ := affineShearConjugatedAutomorphism S h c
  let ψ : C.G ≃* C.G := affineShearRestrictGroupAut
    (nativeRationalSubgroupLayer D F 1) φ hpres
  let cJ : C.G := ⟨c, hc⟩
  have hφ := affineShearConjugatedAutomorphism_mdifferentiable D S hS h c
  have hψ : MDifferentiable C.I C.I (ψ : C.G → C.G) :=
    affineShear_native_restriction_mdifferentiable D L φ hφ hpres
  have hcJ : nativeLieGlobalLogarithm (E := C.E) (I := C.I) (G := C.G) cJ ∈ P 1 := by
    exact (nativeLieGlobalLogarithm (E := C.E) (I := C.I) (G := C.G) cJ).property
  have hdiff : ∀ i, weightedShearNativeDifferential C ψ.toMonoidHom (b i) - b i ∈ P (weights i+1) := by
    intro i
    change (weightedShearNativeDifferential C ψ.toMonoidHom (b i)).val - (b i).val ∈
      F.layer (weights i+1)
    have he := affineShear_native_restriction_differential D L φ hφ hpres (b i)
    change (weightedShearNativeDifferential C ψ.toMonoidHom (b i)).val =
      affineShearNativeProjectionDifferential D D φ.toMonoidHom (b i).val at he
    rw [he]
    exact hgraded (weights i) (hb i).1 (hb i).2.1 (b i).val (hb i).2.2.1
  obtain ⟨f, hf⟩ := weightedShear_native_affine_hom_action C weights P
    (affineShear_native_initial_antitone D F ρ hρ)
    (affineShear_native_initial_bracket D F ρ hρ) b
    (fun i => (hb i).2.2.1) (fun i z hz => (hb i).2.2.2 hz) cJ hcJ ψ.toMonoidHom hψ hdiff
  refine ⟨f, ?_⟩
  intro x
  have he : nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm (f • x)) =
      cJ * ψ (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm x)) := by
    rw [hf, LinearEquiv.symm_apply_apply, nativeLieExponential_globalLogarithm]
    rfl
  have hev := congrArg Subtype.val he
  change (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm (f • x))).val =
    c * φ (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm x)).val at hev
  rw [hev]
  exact (affineShear_coset_normalization D.Γ S h c ρ _ hbase).symm

 theorem affineShear_native_original_faces_shear {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : D.G) (S : D.G ≃* D.G)
    (hS : MDifferentiable D.I D.I (S : D.G → D.G))
    (hfaces : ∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
      ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d,
        (fun V => if j ∈ V then (S (h * z V * ρ) : D.G ⧸ D.Γ)
          else (h * z V * ρ : D.G ⧸ D.Γ)) ∈
            range (nativeResidueCubeOrbitMap D F ρ hρ d (2^d-1)
              (nativeCubeVertexEnumeration d) h)) :
    let C := nativeRationalLayerOrbitData D F 1 ρ hρ
    ∃ n : ℕ, ∃ b : Basis (Fin n) ℝ C.E, ∃ weights : Fin n → ℕ,
      (∀ i, 1 ≤ weights i ∧ weights i ≤ ℓ ∧
        b i ∈ affineShearNativeInitialFiltration D F ρ hρ (weights i) ∧
        affineShearNativeInitialFiltration D F ρ hρ (weights i+1) ≤ (b.coord i).ker) ∧
      ∃ f : weightedShearGroup (R := ℝ) weights, ∀ x : Fin n → ℝ,
        (h * (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm (f • x))).val * ρ :
            D.G ⧸ D.Γ) =
          (S (h * (nativeLieExponential (I := C.I) (G := C.G) (b.equivFun.symm x)).val * ρ) :
            D.G ⧸ D.Γ) := by
  obtain ⟨n, b, weights, hb⟩ := affineShear_native_initial_adapted_basis D F ρ hρ
  refine ⟨n, b, weights, hb, ?_⟩
  exact affineShear_native_original_faces_shear_in_coordinates D F ρ hρ h S hS hfaces n b weights hb

end Hindman168
