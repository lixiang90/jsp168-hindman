import Hindman168.AffineShearNativeJointAction
import Hindman168.AffineShearAlignmentSlotFaces
import Hindman168.AlignmentNativeJointCosetSmooth

/-! Actual duplicated-slot symmetries yield the original marginal face
condition and hence a shear in the same, already chosen upstairs coordinates.
Neither a smoothness oracle nor a marginal cube identification is assumed. -/
namespace Hindman168
open Set Module
open scoped Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three

variable {ι κ : Type} [Fintype ι] [Fintype κ] {σ : ι → Type} {s ℓ : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ k, Fin (n k+1) → σ k → ℤ)
  (hv : ∀ k, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D k).E) (I := (D k).I) (G := (D k).G) (n k) (v k)))
  (index : κ → ι)

 theorem affineShear_alignment_slot_smooth (slots : ∀ k, σ (index k) → ℤ) :
    let C := nativeFinitePiData ((fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ∘ index)
    let S : C.G ≃* C.G := alignmentJointNativeSlotTranslation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots
    ContMDiff C.I C.I ∞ (S : C.G → C.G) := by
  dsimp only
  let A := fun k => alignmentNativeArrayData (D (index k)) (n (index k))
    (v (index k)) (hv (index k))
  exact finitePiGroup_map_contMDiff
    (fun k => nativeLieExponentialDiffeomorph (E := (A k).E) (I := (A k).I) (G := (A k).G))
    (fun k => alignmentNativeArrayTranslation (E := (D (index k)).E) (I := (D (index k)).I)
      (G := (D (index k)).G) (n (index k)) (v (index k)) (hv (index k)) (slots k))
    (fun k => alignmentNativeArrayTranslation_contMDiff (E := (D (index k)).E)
      (I := (D (index k)).I) (G := (D (index k)).G)
      (n (index k)) (v (index k)) (hv (index k)) (slots k))


 theorem affineShear_alignment_slot_lift_in_coordinates
    (F : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))) ℓ)
    (ρ : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).E)
      (I := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).I)
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ)
    (h : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (slots : ∀ k, σ (index k) → ℤ)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
        F 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hb : ∀ i, 1 ≤ w i ∧ w i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          F ρ hρ (w i) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          F ρ hρ (w i+1) ≤ (b.coord i).ker)
    (hsym : ∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : κ × Finset (Fin d) => index a.1) Prod.snd ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : κ × Finset (Fin d) => D (index a.1))
        (fun a => n (index a.1)) (fun a => v (index a.1)) (fun a => hv (index a.1))
        (fun a => if j ∈ a.2 then slots a.1 else 0) '' X = X) :
    let A := nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
    let C := nativeFinitePiData ((fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ∘ index)
    let p := affineShearNativePiRestriction
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) index
    let K := nativeRationalLayerOrbitData A F 1 ρ hρ
    let S : C.G ≃* C.G := alignmentJointNativeSlotTranslation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots
    ∃ U : weightedShearGroup (R := ℝ) w, ∀ x : Fin m → ℝ,
      (p h * p (nativeLieExponential (I := K.I) (G := K.G)
        (b.equivFun.symm (U • x))).val * p ρ : C.G ⧸ C.Γ) =
      (S (p h * p (nativeLieExponential (I := K.I) (G := K.G)
          (b.equivFun.symm x)).val * p ρ) : C.G ⧸ C.Γ) := by
  let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
  let C := nativeFinitePiData (A ∘ index)
  let p := affineShearNativePiRestriction A index
  have hS := affineShear_alignment_slot_smooth D n v hv index slots
  apply affineShear_native_joint_face_lifts_in_coordinates (nativeFinitePiData A) C F p
    (affineShear_native_pi_restriction_smooth A index)
    (affineShear_native_pi_restriction_lattice A index) ρ hρ h m b w hb
    (alignmentJointNativeSlotTranslation (D ∘ index) (n ∘ index)
      (fun k => v (index k)) (fun k => hv (index k)) slots)
    (hS.mdifferentiable (by norm_num))
  intro d hd hd' j
  exact affineShear_alignment_duplicated_slots_face D n v hv index F ρ hρ h d j slots
    (hsym d hd hd' j)

 theorem affineShear_alignment_letter_lifts_in_coordinates
    {η : Type} {κs : η → Type} [∀ e, Fintype (κs e)]
    (indices : ∀ e, κs e → ι)
    (allSlots : ∀ e k, σ (indices e k) → ℤ)
    (F : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))) ℓ)
    (ρ : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).E)
      (I := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).I)
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ)
    (h : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
        F 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hb : ∀ i, 1 ≤ w i ∧ w i ≤ ℓ ∧
      b i ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          F ρ hρ (w i) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          F ρ hρ (w i+1) ≤ (b.coord i).ker)
    (hsym : ∀ e : η, ∀ d : ℕ, 1 ≤ d → d ≤ ℓ+1 → ∀ j : Fin d,
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : κs e × Finset (Fin d) => indices e a.1) Prod.snd ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) F ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : κs e × Finset (Fin d) => D (indices e a.1))
        (fun a => n (indices e a.1)) (fun a => v (indices e a.1)) (fun a => hv (indices e a.1))
        (fun a => if j ∈ a.2 then allSlots e a.1 else 0) '' X = X) :
    let A := nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
    ∃ L : η → weightedShearGroup (R := ℝ) w, ∀ e : η,
    let C := nativeFinitePiData ((fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ∘ indices e)
    let p := affineShearNativePiRestriction
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) (indices e)
    let K := nativeRationalLayerOrbitData A F 1 ρ hρ
    let S : C.G ≃* C.G := alignmentJointNativeSlotTranslation (D ∘ indices e) (n ∘ indices e)
      (fun k => v (indices e k)) (fun k => hv (indices e k)) (allSlots e)
    ∀ x : Fin m → ℝ,
      (p h * p (nativeLieExponential (I := K.I) (G := K.G)
        (b.equivFun.symm (L e • x))).val * p ρ : C.G ⧸ C.Γ) =
      (S (p h * p (nativeLieExponential (I := K.I) (G := K.G)
          (b.equivFun.symm x)).val * p ρ) : C.G ⧸ C.Γ) := by
  classical
  have hex := fun e => affineShear_alignment_slot_lift_in_coordinates D n v hv (indices e)
    F ρ hρ h (allSlots e) m b w hb (hsym e)
  choose L hL using hex
  exact ⟨L, hL⟩

end Hindman168
