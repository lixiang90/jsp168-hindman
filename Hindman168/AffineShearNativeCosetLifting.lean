import Hindman168.AffineShearCoverLifting
import Hindman168.AffineShearCosetNormalization
import Hindman168.AffineShearNativeGradedIdentity
import Hindman168.NativeResidueCubeOrbit
import Hindman168.NativeNilmanifoldQuotientCovering
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex

/-! The group-cover step of Proposition 7.5 for the ACTUAL rational cube
orbit.  Compactness, injectivity, and covering hypotheses are discharged by
the native cube and lattice constructions.  A continuous family of arrays
whose quotient stays in the cube coset, starting in the cube group, stays in
the actual upper-face generated cube group. -/
namespace Hindman168
open Function Set Topology
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

 theorem affineShear_native_cube_coset_lifts {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G)
    {A : Type*} [TopologicalSpace A] [SimplyConnectedSpace A] [LocallyPathConnectedSpace A]
    (z : A → (Finset (Fin d) → D.G)) (hz : Continuous z) (a₀ : A)
    (hz₀ : z a₀ ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d)
    (hcoset : ∀ a, (fun V => (h * z a V * ρ : D.G ⧸ D.Γ)) ∈
      range (nativeResidueCubeOrbitMap D F ρ hρ d n e h)) :
    ∀ a, z a ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d := by
  have ht : @T2Space (D.G ⧸ D.Γ) D.metric.toUniformSpace.toTopologicalSpace := by
    letI := D.metric
    infer_instance
  letI : T2Space (D.G ⧸ D.Γ) := Eq.mpr
    (congrArg (fun t => @T2Space (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D)) ht
  let C := nativeResidueCubeData D F ρ hρ d n e
  let i : C.G → (Finset (Fin d) → D.G) := fun x V =>
    h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ
  have hi : Continuous i := by
    apply continuous_pi
    intro V
    exact (continuous_const.mul
      ((nativeFiniteProductCoordinate_continuous n (e.symm V)).comp continuous_subtype_val)).mul
        continuous_const
  let f : A → (Finset (Fin d) → D.G) := fun a V => h * z a V * ρ
  have hf : Continuous f := by
    apply continuous_pi
    intro V
    exact (continuous_const.mul ((continuous_apply V).comp hz)).mul continuous_const
  rw [← native_rational_cube_group_identification D F d n e] at hz₀
  obtain ⟨x₀, hx₀, he₀⟩ := hz₀
  let c₀ : C.G := ⟨x₀, hx₀⟩
  have hstart : f a₀ = i c₀ := by
    funext V
    change h * z a₀ V * ρ = h * nativeCubeVertexHom (G := D.G) d n e x₀ V * ρ
    rw [he₀]
  have hlift := affineShear_pi_cover_range_lifting
    ((↑) : D.G → D.G ⧸ D.Γ) ((↑) : C.G → C.G ⧸ C.Γ)
    (native_nilmanifold_quotient_covering D) (native_nilmanifold_quotient_covering C)
    i hi (nativeResidueCubeOrbitMap D F ρ hρ d n e h)
    (native_residue_cube_orbit_map_continuous D F ρ hρ d n e h)
    (native_residue_cube_orbit_map_injective D F ρ hρ d n e h)
    (fun _ _ => rfl) f hf a₀ c₀ hstart hcoset
  intro a
  obtain ⟨x, hx⟩ := hlift a
  rw [← native_rational_cube_group_identification D F d n e]
  refine ⟨x.val, x.property, ?_⟩
  funext V
  have hv := congrFun hx V
  change h * nativeCubeVertexHom (G := D.G) d n e x.val V * ρ = h * z a V * ρ at hv
  exact mul_left_cancel (mul_right_cancel hv)

 theorem affineShear_native_coset_face_preserves_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) (j : Fin d)
    (c : D.G) (hc : c ∈ nativeRationalSubgroupLayer D F 1)
    (φ : D.G →* D.G) (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hcoset : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d,
      (fun V => (h * affineShearFaceAction j (fun y => c * φ y) z V * ρ : D.G ⧸ D.Γ)) ∈
        range (nativeResidueCubeOrbitMap D F ρ hρ d n e h))
    (z : Finset (Fin d) → D.G)
    (hz : z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d) :
    affineShearFaceAction j (fun y => c * φ y) z ∈
      upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d := by
  classical
  let v : Finset (Fin d) → GroupLieAlgebra D.I D.G := fun V =>
    nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) (z V)
  have hv : v ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0 := by
    apply (affineShear_native_cube_exp_mem_iff D F d n e v).mp
    convert hz using 1
    funext V
    exact nativeLieExponential_globalLogarithm (I := D.I) (z V)
  let γ : ℝ → (Finset (Fin d) → D.G) := fun t V =>
    nativeLieExponential (I := D.I) (G := D.G) (t • v V)
  have hγ (t : ℝ) : γ t ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d :=
    (affineShear_native_cube_exp_mem_iff D F d n e (t • v)).mpr
      ((upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0).smul_mem t hv)
  let δ : ℝ → (Finset (Fin d) → D.G) := fun t =>
    affineShearFaceAction j (fun y => c * φ y) (γ t)
  have hδ : Continuous δ := by
    apply continuous_pi
    intro V
    have hγV : Continuous (fun t : ℝ => γ t V) :=
      (nativeLieExponential_continuous (I := D.I) (G := D.G)).comp
        (continuous_id.smul continuous_const)
    by_cases hj : j ∈ V
    · change Continuous (fun t => if j ∈ V then c * φ (γ t V) else γ t V)
      simp only [if_pos hj]
      exact continuous_const.mul (hφ.continuous.comp hγV)
    · change Continuous (fun t => if j ∈ V then c * φ (γ t V) else γ t V)
      simpa only [if_neg hj] using hγV
  have hδ₀ : δ 0 = upperFaceArray {j} c := by
    funext V
    simp [δ, γ, affineShearFaceAction, upperFaceArray, nativeLieExponential_zero]
  have hmem₀ : δ 0 ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d := by
    rw [hδ₀]
    exact upperFaceArray_mem_cubeGroup _ {j} c (by simpa using hc)
  have hlift := affineShear_native_cube_coset_lifts D F ρ hρ d n e h δ hδ 0 hmem₀
    (fun t => hcoset (γ t) (hγ t)) 1
  have hγ₁ : γ 1 = z := by
    funext V
    simp only [γ, one_smul]
    exact nativeLieExponential_globalLogarithm (I := D.I) (z V)
  change affineShearFaceAction j (fun y => c * φ y) (γ 1) ∈ _ at hlift
  rwa [hγ₁] at hlift

/-- The actual quotient cube-coset face condition forces the associated
 graded identity.  Cover preservation and Lie-cube preservation are proved
 internally, rather than accepted as additional hypotheses. -/
 theorem affineShear_native_coset_face_forces_graded_identity {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (i n : ℕ) (e : Fin (n+1) ≃ Finset (Fin (i+1))) (h : D.G)
    (c : D.G) (hc : c ∈ nativeRationalSubgroupLayer D F 1)
    (φ : D.G →* D.G) (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hcoset : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1),
      (fun V => (h * affineShearFaceAction (Fin.last i) (fun y => c * φ y) z V * ρ : D.G ⧸ D.Γ)) ∈
        range (nativeResidueCubeOrbitMap D F ρ hρ (i+1) n e h))
    (x : D.E) (hx : x ∈ F.layer i) :
    affineShearNativeProjectionDifferential D D φ x - x ∈ F.layer (i+1) :=
  affineShear_native_face_forces_graded_identity D F i n e c φ hφ
    (affineShear_native_coset_face_preserves_group D F ρ hρ (i+1) n e h
      (Fin.last i) c hc φ hφ hcoset) x hx

 theorem affineShearConjugatedAutomorphism_mdifferentiable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : D.G ≃* D.G)
    (hS : MDifferentiable D.I D.I (S : D.G → D.G)) (h c : D.G) :
    MDifferentiable D.I D.I (affineShearConjugatedAutomorphism S h c : D.G → D.G) := by
  exact ((nativeLieConjugation_contMDiff (I := D.I) (c⁻¹ * h⁻¹ * S h)).mdifferentiable
    (by norm_num)).comp hS

/-- The original ambient automorphism's face condition, expressed on actual
coset representatives, implies (7.16) for its constructed affine linear part.
The basepoint equality is exactly (7.15) of Proposition 7.5. -/
 theorem affineShear_native_original_face_forces_graded_identity {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (i n : ℕ) (e : Fin (n+1) ≃ Finset (Fin (i+1))) (h : D.G)
    (S : D.G ≃* D.G) (hS : MDifferentiable D.I D.I (S : D.G → D.G))
    (c : D.G) (hc : c ∈ nativeRationalSubgroupLayer D F 1)
    (hbase : (S (h * ρ) : D.G ⧸ D.Γ) = (h * c * ρ : D.G ⧸ D.Γ))
    (hface : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1),
      (fun V => if Fin.last i ∈ V then (S (h * z V * ρ) : D.G ⧸ D.Γ)
        else (h * z V * ρ : D.G ⧸ D.Γ)) ∈
          range (nativeResidueCubeOrbitMap D F ρ hρ (i+1) n e h))
    (x : D.E) (hx : x ∈ F.layer i) :
    affineShearNativeProjectionDifferential D D (affineShearConjugatedAutomorphism S h c).toMonoidHom x - x ∈
      F.layer (i+1) := by
  apply affineShear_native_coset_face_forces_graded_identity D F ρ hρ i n e h c hc
    (affineShearConjugatedAutomorphism S h c).toMonoidHom
    (affineShearConjugatedAutomorphism_mdifferentiable D S hS h c) ?_ x hx
  intro z hz
  have hz' := hface z hz
  convert hz' using 1
  funext V
  classical
  by_cases hj : Fin.last i ∈ V
  · simp only [affineShearFaceAction, if_pos hj]
    exact (affineShear_coset_normalization D.Γ S h c ρ (z V) hbase).symm
  · simp only [affineShearFaceAction, if_neg hj]

end Hindman168
