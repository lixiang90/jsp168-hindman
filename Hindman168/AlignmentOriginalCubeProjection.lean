import Hindman168.AlignmentOriginalJointCubeOrbit
import Hindman168.NativeFinitePiCubeProjection

/-! Exact identification of actual selected-array cube states as coordinatewise
projections of the SAME original joint point-orbit cube. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentBinaryCubeVertex (weight : κ → ℤ) : Finset κ :=
  Finset.univ.filter (fun j => weight j = 1)

theorem alignment_binary_cube_vertex_sum (weight inc : κ → ℤ)
    (hw : ∀ j, weight j=0 ∨ weight j=1) :
    (∑ j, weight j*inc j) = ∑ j ∈ alignmentBinaryCubeVertex weight, inc j := by
  classical
  unfold alignmentBinaryCubeVertex
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  rcases hw j with h | h <;> simp [h]

theorem alignment_original_joint_cube_projection
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : ι → Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    let A := fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)
    let J := nativeFinitePiData A
    (alignmentOriginalJointCubeGroup D n v hv F q₀ w T y p Y shift weight g a ell : J.G ⧸ J.Γ) =
      nativeFinitePiCubeProjection A (fun ν => alignmentBinaryCubeVertex (weight ν))
        (fun V : Finset κ => (alignmentOriginalJointPointOrbit D n v hv F q₀ w T y p shift g a
          (ell none+∑ j ∈ V, ell (some j)) : J.G ⧸ J.Γ)) := by
  dsimp only
  apply (nativeFinitePiCosetHomeomorph _).injective
  funext ν
  rw [native_finite_pi_coset_homeomorph_apply,native_finite_pi_coset_homeomorph_apply,
    native_finite_pi_cube_projection_coordinate,native_finite_pi_coset_coordinate_mk,
    native_finite_pi_coset_coordinate_mk,
    alignment_original_joint_cube_point_component,
    alignment_binary_cube_vertex_sum (weight ν) (fun j => ell (some j)) (hw ν)]

theorem alignment_original_native_cube_projection
    (F : MasterParameterFamily) (q₀ w : ℕ) (T : Finset (Fin N))
    (y : Fin N → ℕ) (p Y : ℤ) (shift : ι → AlignmentAddingPair N i → ℤ)
    (weight : ι → κ → ℤ) (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (g a : ∀ ν, (D ν).G) (ell : Option κ → ℤ) :
    let A := fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)
    let J := nativeFinitePiData A
    alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a ell =
      nativeFinitePiCubeProjection A (fun ν => alignmentBinaryCubeVertex (weight ν))
        (fun V : Finset κ => (alignmentOriginalJointPointOrbit D n v hv F q₀ w (fun _ => T) y p shift g a
          (ell none+∑ j ∈ V, ell (some j)) : J.G ⧸ J.Γ)) :=
  alignment_original_joint_cube_projection D n v hv F q₀ w (fun _ => T) y p Y shift weight hw g a ell

end Hindman168
