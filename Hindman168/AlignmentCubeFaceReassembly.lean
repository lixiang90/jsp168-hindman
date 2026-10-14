import Hindman168.NativeFinitePiCubeReassembly
import Hindman168.AlignmentJointNativeSlotHomeomorph
import Hindman168.AlignmentNativeArrayCosetTranslations

/-! Actual slot translations on repeated coordinates reassemble to the
vertexwise translations of one full marginal cube. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
variable {κ V : Type} [Fintype κ] [Fintype V] {σ : κ → Type} {s : ℕ}
  (D : κ → NativeNilmanifoldData.{u} s) (n : κ → ℕ)
  (v : ∀ k, Fin (n k+1) → σ k → ℤ)
  (hv : ∀ k, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D k).E) (I := (D k).I) (G := (D k).G) (n k) (v k)))

theorem alignment_joint_native_slot_coordinate (slots : ∀ k, σ k → ℤ) (k : κ)
    (x : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G ⧸
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ) :
    nativeFinitePiCosetCoordinate (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) k
      (alignmentJointNativeCosetSlotTranslation D n v hv slots x) =
      alignmentNativeArrayCosetTranslation (E := (D k).E) (I := (D k).I)
        (n k) (v k) (hv k) (D k).Γ (slots k)
        (nativeFinitePiCosetCoordinate (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) k x) := by
  induction x using Quotient.inductionOn with
  | _ a => rfl

theorem alignment_cube_reassembly_slot_translation (slots : ∀ p : κ × V, σ p.1 → ℤ)
    (x : (nativeFinitePiData (fun p : κ × V =>
      alignmentNativeArrayData (D p.1) (n p.1) (v p.1) (hv p.1))).G ⧸
      (nativeFinitePiData (fun p : κ × V =>
      alignmentNativeArrayData (D p.1) (n p.1) (v p.1) (hv p.1))).Γ) :
    nativeFinitePiCubeReassembly (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
      (alignmentJointNativeCosetSlotTranslation (fun p : κ × V => D p.1)
        (fun p => n p.1) (fun p => v p.1) (fun p => hv p.1) slots x) =
    fun z => alignmentJointNativeCosetSlotTranslation D n v hv (fun k => slots (k,z))
      (nativeFinitePiCubeReassembly (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) x z) := by
  funext z
  apply (nativeFinitePiCosetHomeomorph (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).injective
  funext k
  rw [native_finite_pi_coset_homeomorph_apply, native_finite_pi_coset_homeomorph_apply,
    native_finite_pi_cube_reassembly_coordinate]
  rw [alignment_joint_native_slot_coordinate, alignment_joint_native_slot_coordinate,
    native_finite_pi_cube_reassembly_coordinate]

end Hindman168
