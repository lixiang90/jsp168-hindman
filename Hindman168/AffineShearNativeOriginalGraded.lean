import Hindman168.AffineShearNativeCosetLifting

/-! The common basepoint and associated-graded conclusion in Proposition 7.5.
The element c is extracted from the actual one-face quotient orbit, then the
SAME c is used in every dimension.  No basepoint/lift/graded certificate is
assumed.  The hypothesis is the original face condition on representatives
of the given native cube cosets. -/
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

 theorem affineShear_native_basepoint_exists {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (h : D.G) (j : Fin d)
    (S : D.G → D.G)
    (hface : (fun V => if j ∈ V then (S (h * ρ) : D.G ⧸ D.Γ)
        else (h * ρ : D.G ⧸ D.Γ)) ∈
          range (nativeResidueCubeOrbitMap D F ρ hρ d n e h)) :
    ∃ c : D.G, c ∈ nativeRationalSubgroupLayer D F 1 ∧
      (S (h * ρ) : D.G ⧸ D.Γ) = (h * c * ρ : D.G ⧸ D.Γ) := by
  obtain ⟨q, hq⟩ := hface
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  let z := nativeCubeVertexHom (G := D.G) d n e x.val
  have hz : z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d := by
    rw [← native_rational_cube_group_identification D F d n e]
    exact ⟨x.val, x.property, rfl⟩
  have hant : Antitone (nativeRationalSubgroupLayer D F) := by
    intro a b hab g hg
    apply (native_rational_subgroup_layer_logarithm_iff D F a g).mpr
    exact F.antitone hab ((native_rational_subgroup_layer_logarithm_iff D F b g).mp hg)
  let c := z {j}
  have hc₀ := affineShear_cube_vertex_initial (nativeRationalSubgroupLayer D F) hant z hz {j}
  have hc : c ∈ nativeRationalSubgroupLayer D F 1 := by
    apply (native_rational_subgroup_layer_logarithm_iff D F 1 c).mpr
    rw [← F.initial]
    exact (native_rational_subgroup_layer_logarithm_iff D F 0 c).mp hc₀
  refine ⟨c, hc, ?_⟩
  have hv := (congrFun hq {j}).symm
  simpa only [native_residue_cube_orbit_map_mk, Finset.mem_singleton_self, if_true] using hv

 theorem affineShear_native_original_faces_graded_identity {s ℓ : ℕ}
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
    ∃ c : D.G, c ∈ nativeRationalSubgroupLayer D F 1 ∧
      (S (h * ρ) : D.G ⧸ D.Γ) = (h * c * ρ : D.G ⧸ D.Γ) ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ ℓ → ∀ x ∈ F.layer i,
        affineShearNativeProjectionDifferential D D (affineShearConjugatedAutomorphism S h c).toMonoidHom x - x ∈
          F.layer (i+1) := by
  have hbase := hfaces 1 le_rfl (Nat.succ_le_succ (Nat.zero_le ℓ)) 0 1
    (Subgroup.one_mem _)
  simp only [Pi.one_apply, mul_one] at hbase
  obtain ⟨c, hc, hcbase⟩ := affineShear_native_basepoint_exists D F ρ hρ 1 (2^1-1)
    (nativeCubeVertexEnumeration 1) h 0 S hbase
  refine ⟨c, hc, hcbase, ?_⟩
  intro i hi hile x hx
  exact affineShear_native_original_face_forces_graded_identity D F ρ hρ i (2^(i+1)-1)
    (nativeCubeVertexEnumeration (i+1)) h S hS c hc hcbase
    (hfaces (i+1) (Nat.succ_pos i) (Nat.succ_le_succ hile) (Fin.last i)) x hx

/-- The same normalized affine linear part is an actual automorphism of J,
and is the identity on every associated graded space. -/
 theorem affineShear_native_original_faces_restrict_and_graded {s ℓ : ℕ}
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
    ∃ c : D.G, c ∈ nativeRationalSubgroupLayer D F 1 ∧
      (S (h * ρ) : D.G ⧸ D.Γ) = (h * c * ρ : D.G ⧸ D.Γ) ∧
      (nativeRationalSubgroupLayer D F 1).map
        (affineShearConjugatedAutomorphism S h c).toMonoidHom =
          nativeRationalSubgroupLayer D F 1 ∧
      ∀ i : ℕ, 1 ≤ i → i ≤ ℓ → ∀ x ∈ F.layer i,
        affineShearNativeProjectionDifferential D D (affineShearConjugatedAutomorphism S h c).toMonoidHom x - x ∈
          F.layer (i+1) := by
  obtain ⟨c, hc, hbase, hgraded⟩ :=
    affineShear_native_original_faces_graded_identity D F ρ hρ h S hS hfaces
  let φ := affineShearConjugatedAutomorphism S h c
  have hφ := affineShearConjugatedAutomorphism_mdifferentiable D S hS h c
  have hnorm : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) 1,
      (fun V => (h * affineShearFaceAction (Fin.last 0) (fun y => c * φ y) z V * ρ : D.G ⧸ D.Γ)) ∈
        range (nativeResidueCubeOrbitMap D F ρ hρ 1 (2^1-1) (nativeCubeVertexEnumeration 1) h) := by
    intro z hz
    have hz' := hfaces 1 le_rfl (Nat.succ_le_succ (Nat.zero_le ℓ)) (Fin.last 0) z hz
    convert hz' using 1
    funext V
    classical
    by_cases hj : Fin.last 0 ∈ V
    · simp only [affineShearFaceAction, if_pos hj]
      exact (affineShear_coset_normalization D.Γ S h c ρ (z V) hbase).symm
    · simp only [affineShearFaceAction, if_neg hj]
  have hgroup := affineShear_native_face_preserves_group_layer D F 0 (2^1-1)
    (nativeCubeVertexEnumeration 1) c φ.toMonoidHom hφ φ.injective
    (affineShear_native_coset_face_preserves_group D F ρ hρ 1 (2^1-1)
      (nativeCubeVertexEnumeration 1) h (Fin.last 0) c hc φ.toMonoidHom hφ hnorm)
  have h01 : nativeRationalSubgroupLayer D F 0 = nativeRationalSubgroupLayer D F 1 := by
    ext g
    rw [native_rational_subgroup_layer_logarithm_iff, native_rational_subgroup_layer_logarithm_iff,
      F.initial]
  rw [h01] at hgroup
  exact ⟨c, hc, hbase, hgroup, hgraded⟩

end Hindman168
