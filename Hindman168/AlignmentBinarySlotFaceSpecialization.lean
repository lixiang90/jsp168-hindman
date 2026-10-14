import Hindman168.AlignmentSelectedAllTargetsCosets
import Hindman168.AlignmentCubeUpperFaceReassembly

/-! Specialize the selected binary-weight symmetries to all vertices of a
complete marginal cube. This is the literal duplicated-slot hypothesis
needed by the actual native shear lift. -/
namespace Hindman168
open Set
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three
variable {ι κ : Type} [Fintype ι] [Fintype κ] {N : ℕ} {i : Fin N} {s ℓ : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ k, Fin (n k+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ k, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D k).E) (I := (D k).I) (G := (D k).G) (n k) (v k)))
  (index : κ → ι)

 theorem alignment_binary_slot_symmetries_full_face
    (F : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))) ℓ)
    (ρ : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).E)
      (I := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).I)
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ)
    (h : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (d : ℕ) (e : AlignmentAddingPair N i)
    (hsym : ∀ weight : (κ × Finset (Fin d)) → Fin d → ℤ,
      (∀ a j, weight a j = 0 ∨ weight a j = 1) → ∀ j : Fin d,
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : κ × Finset (Fin d) => index a.1)
        (fun a => alignmentBinaryCubeVertex (weight a)) ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : κ × Finset (Fin d) => D (index a.1))
        (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
        (fun a => Pi.single e (weight a j)) '' X = X) :
    ∀ j : Fin d,
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : κ × Finset (Fin d) => index a.1) Prod.snd ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : κ × Finset (Fin d) => D (index a.1))
        (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
        (fun a => if j ∈ a.2 then Pi.single e 1 else 0) '' X = X := by
  intro j
  let weight : (κ × Finset (Fin d)) → Fin d → ℤ := fun a j => if j ∈ a.2 then 1 else 0
  have hw : ∀ a j, weight a j = 0 ∨ weight a j = 1 := by
    intro a j
    by_cases hj : j ∈ a.2 <;> simp [weight, hj]
  have hvtx : (fun a => alignmentBinaryCubeVertex (weight a)) =
      (Prod.snd : κ × Finset (Fin d) → Finset (Fin d)) := by
    funext a
    exact alignment_binary_vertex_indicator a.2
  have hslt : (fun a : κ × Finset (Fin d) => (Pi.single e (weight a j) : AlignmentAddingPair N i → ℤ)) =
      (fun a => if j ∈ a.2 then Pi.single e 1 else 0) := by
    funext a
    by_cases hj : j ∈ a.2 <;> simp [weight, hj]
  simpa only [hvtx, hslt] using hsym weight hw j

end Hindman168
