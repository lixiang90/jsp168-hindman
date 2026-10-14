import Hindman168.AlignmentOriginalCubeProjection

/-! The actual binary-coordinate projection intertwines an own cube face
with its original slot translation on the projected native array. -/
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

theorem alignment_native_cube_projection_reading
    (weight : ι → κ → ℤ)
    (x : Finset κ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (ν : ι) (z : AlignmentAddingPair N i → ℤ) :
    alignmentJointNativeCosetEvaluation D n v hv ν z
      (nativeFinitePiCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
        (fun ν => alignmentBinaryCubeVertex (weight ν)) x) =
      alignmentJointNativeCosetEvaluation D n v hv ν z (x (alignmentBinaryCubeVertex (weight ν))) := by
  unfold alignmentJointNativeCosetEvaluation
  simp only [Function.comp_apply,native_finite_pi_cube_projection_coordinate]

theorem alignment_native_cube_projection_face
    (weight : ι → κ → ℤ) (hw : ∀ ν j, weight ν j=0 ∨ weight ν j=1)
    (e : AlignmentAddingPair N i) (j : κ)
    (x : Finset κ → (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    let project := nativeFinitePiCubeProjection
      (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
      (fun ν => alignmentBinaryCubeVertex (weight ν))
    alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) (project x) =
      project (fun V => alignmentJointNativeCosetSlotTranslation D n v hv
        (fun _ => Pi.single e (if j ∈ V then 1 else 0)) (x V)) := by
  classical
  dsimp only
  apply (alignment_joint_native_all_slot_readings_eq_iff D n v hv _ _).mp
  intro ν z
  rw [alignment_joint_native_coset_slot_translation_evaluation,
    alignment_native_cube_projection_reading,alignment_native_cube_projection_reading,
    alignment_joint_native_coset_slot_translation_evaluation]
  rcases hw ν j with h | h <;> simp [alignmentBinaryCubeVertex,h]

end Hindman168
