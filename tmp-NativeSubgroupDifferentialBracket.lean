import Hindman168.NativeLieSubalgebraNativeCoordinates
import Hindman168.NativeSmoothHomLieBracket
import Hindman168.NativeNilmanifoldData
import Hindman168.NativeRationalLayerOrbit
import Hindman168.NativeSubgroupMaximalCharacter
import Hindman168.NativeRationalKernelLieFiltration
import Hindman168.RoughNativeHorizontalCharacterGrid

namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_subgroup_differential_bracket_original {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (S : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G)) :
    letI := nativeLieSubalgebraChartedSpace (E := D.E) S
    letI := nativeLieSubalgebra_lieGroup S
    letI := nativeLieSubalgebra_boundaryless S
    ∀ v w : nativeLieSubalgebraModel (E := D.E) S,
      (nativeLieAdjointDifferential (I := 𝓘(ℝ,nativeLieSubalgebraModel (E := D.E) S))
        (G := nativeLieSubalgebraSubgroup (E := D.E) S) v w : D.E) =
      nativeLieAdjointDifferential (I := D.I) (G := D.G) v.val w.val := by
  letI := nativeLieSubalgebraChartedSpace (E := D.E) S
  letI := nativeLieSubalgebra_lieGroup S
  letI := nativeLieSubalgebra_boundaryless S
  intro v w
  have h := nativeSmoothHom_generator_intertwine
    (E := nativeLieSubalgebraModel (E := D.E) S) (F := D.E)
    (I := 𝓘(ℝ,nativeLieSubalgebraModel (E := D.E) S)) (J := D.I)
    (nativeLieSubalgebraSubgroup (E := D.E) S).subtype
    (nativeLieSubalgebra_inclusion_contMDiff S) v w
  dsimp only at h
  simp only [Subgroup.coe_subtype] at h
  rw [nativeLieSubalgebra_inclusion_mfderiv S] at h
  simpa only [nativeLieAdjointGenerator_eq_differential, Submodule.subtype_apply,
    LinearMap.coe_toContinuousLinearMap'] using h

noncomputable def nativeSubgroupHorizontalExtension {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (chi : (nativeRationalLayerOrbitData D F 0 rho hRat).E →ₗ[ℝ] ℝ) : D.E →ₗ[ℝ] ℝ :=
  chi.comp (finiteRealSubmoduleRetraction (F.layer 0)).toLinearMap

theorem native_subgroup_horizontal_extension_agrees {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (chi : (nativeRationalLayerOrbitData D F 0 rho hRat).E →ₗ[ℝ] ℝ)
    (v : F.layer 0) :
    nativeSubgroupHorizontalExtension D F rho hRat chi v.val = chi v := by
  exact congrArg chi (finiteRealSubmoduleRetraction_left (F.layer 0) v)

theorem native_actual_subgroup_horizontal_maximal_level {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (rho : D.G) (hRat : rho ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (chi : (nativeRationalLayerOrbitData D F 0 rho hRat).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalLayerOrbitData D F 0 rho hRat).I)
      (nativeRationalLayerOrbitData D F 0 rho hRat).Γ chi) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧
      NativeSubgroupRationalLevelCharacter D F j (nativeSubgroupHorizontalExtension D F rho hRat chi) ∧
      ∀ k : ℕ, j < k → F.layer k ≤ (nativeSubgroupHorizontalExtension D F rho hRat chi).ker := by
  let A := nativeRationalLayerOrbitData D F 0 rho hRat
  let S := nativeRationalSubgroupLayerAlgebra D F 0
  let phi := nativeSubgroupHorizontalExtension D F rho hRat chi
  have hAgree (v : F.layer 0) : phi v.val = chi v :=
    native_subgroup_horizontal_extension_agrees D F rho hRat chi v
  apply native_subgroup_character_maximal_level D F phi
  · obtain ⟨v,hv⟩ := DFunLike.ne_iff.mp hChi.1
    have hv0 : chi v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
    exact ⟨v.val,v.property,by simpa only [hAgree v] using hv0⟩
  · intro v hv w hw
    let x : A.E := ⟨v,hv⟩
    let y : A.E := ⟨w,hw⟩
    let z : F.layer 0 := nativeLieAdjointDifferential (I := A.I) (G := A.G) x y
    have hz : chi z = 0 := hChi.2.1 (native_rational_lie_bracket_mem_commutator A x y)
    have he : (z : D.E) = nativeLieAdjointDifferential (I := D.I) (G := D.G) v w :=
      native_subgroup_differential_bracket_original D S x y
    rw [← he]
    exact (hAgree z).trans hz
  · apply native_subgroup_integral_character_rational_on_layer D F 0 rho hRat phi
    intro g hg
    let k : A.G := ⟨g,hg.2⟩
    have hk : k ∈ A.Γ := by
      rw [native_rational_layer_orbit_data_lattice]
      exact hg.1
    obtain ⟨m,hm⟩ := hChi.2.2 k hk
    let t : F.layer 0 := nativeLieGlobalLogarithm (E := A.E) (I := A.I) (G := A.G) k
    have hLog : t.val =
      nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g :=
      nativeLieSubalgebra_native_logarithm S k
    refine ⟨m,?_⟩
    rw [← hLog]
    exact (hAgree t).trans hm

end Hindman168
