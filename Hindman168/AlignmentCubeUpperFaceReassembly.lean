import Hindman168.AlignmentCubeFaceReassembly
import Hindman168.AlignmentOriginalCubeProjection

/-! The binary weight array for all vertices gives the actual upper-face
translation of a complete marginal cube after the explicit reassembly. -/
namespace Hindman168
open scoped Manifold ContDiff Classical
universe u

 theorem alignment_binary_vertex_indicator {q : ℕ} (V : Finset (Fin q)) :
    alignmentBinaryCubeVertex (fun j => if j ∈ V then (1 : ℤ) else 0) = V := by
  ext j
  simp [alignmentBinaryCubeVertex]

variable {κ V : Type} [Fintype κ] [Fintype V] {σ : κ → Type} {s : ℕ}
  (D : κ → NativeNilmanifoldData.{u} s) (n : κ → ℕ)
  (v : ∀ k, Fin (n k+1) → σ k → ℤ)
  (hv : ∀ k, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D k).E) (I := (D k).I) (G := (D k).G) (n k) (v k)))

theorem alignment_cube_reassembly_face_translation (face : V → Prop)
    (slots : ∀ k, σ k → ℤ)
    (x : (nativeFinitePiData (fun p : κ × V =>
      alignmentNativeArrayData (D p.1) (n p.1) (v p.1) (hv p.1))).G ⧸
      (nativeFinitePiData (fun p : κ × V =>
      alignmentNativeArrayData (D p.1) (n p.1) (v p.1) (hv p.1))).Γ) :
    nativeFinitePiCubeReassembly (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
      (alignmentJointNativeCosetSlotTranslation (fun p : κ × V => D p.1)
        (fun p => n p.1) (fun p => v p.1) (fun p => hv p.1)
        (fun p => if face p.2 then slots p.1 else 0) x) =
    fun z => if face z then alignmentJointNativeCosetSlotTranslation D n v hv slots
      (nativeFinitePiCubeReassembly (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) x z)
      else nativeFinitePiCubeReassembly (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) x z := by
  rw [alignment_cube_reassembly_slot_translation]
  funext z
  by_cases hz : face z
  · simp only [hz, if_true]
  · simp only [hz, if_false]
    exact alignmentNativeJointCosetTranslation_zero n v hv (fun k => (D k).Γ) _

end Hindman168
