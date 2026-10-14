import Hindman168.AlignmentJointRouteReadingsNative
import Hindman168.AlignmentCatalogueNativeLetters
import Hindman168.WeightedShearJointOrbitHaar

/-! The concrete own-target letters supplied by the selected joint coset
symmetries satisfy the reading identities used in the recurrence cover.
The projection is precisely the joint weighted-box Haar projection. -/
namespace Hindman168
open Module
open scoped Topology Manifold ContDiff Classical
universe u
attribute [local instance] lieGroup_smooth_min_three alignmentAddingPairFintype

variable {ι κ : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

/-- This is literally the projection occurring in the proved joint Haar law. -/
theorem alignment_joint_route_projection_restriction {η : Type} [Fintype η]
    (index : η → ι) {ℓ : ℕ}
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) ℓ)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H 1 ρ hρ).E)
    (x : Fin m → ℝ) :
    let A := fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)
    let J := nativeFinitePiData A
    let C := nativeFinitePiData (A ∘ index)
    let p := affineShearNativePiRestriction A index
    let K := nativeRationalLayerOrbitData J H 1 ρ hρ
    nativeFinitePiCosetRestriction A index
      (nativeRationalLayerOrbitMap J H 1 ρ hρ h (weightedShearNativeProjection K b x)) =
      (p h * p (nativeLieExponential (I := K.I) (G := K.G) (b.equivFun.symm x)).val * p ρ : C.G ⧸ C.Γ) := by
  dsimp only
  unfold weightedShearNativeProjection
  rw [native_rational_layer_orbit_map_mk, native_finite_pi_coset_restriction_mk]
  rfl

/-- No reading equivariance is assumed here: the common letters are obtained
from the actual selected coset symmetry, then restricted and evaluated. -/
theorem alignment_joint_native_letters_reading_equivariance
    (targets : ι → Finset (Fin N))
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hb : ∀ j, 1 ≤ w j ∧ w j ≤ s ∧
      b j ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H ρ hρ (w j) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) H ρ hρ (w j+1) ≤
          (b.coord j).ker)
    (hsym : AlignmentCatalogueCosetSymmetry D n v hv targets H ρ hρ h)
    (factor : Finset (Fin N) → ℚ → κ → (AlignmentAddingPair N i → ℤ) → Option ι)
    (obs : ∀ ν, (D ν).G ⧸ (D ν).Γ → ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    let K := nativeRationalLayerOrbitData J H 1 ρ hρ
    let projection := fun x => nativeRationalLayerOrbitMap J H 1 ρ hρ h (weightedShearNativeProjection K b x)
    ∃ L : AlignmentAddingPair N i → weightedShearGroup (R := ℝ) w,
      ∀ e B a c stored query ν, factor B a c stored = some ν → targets ν = e.targetTail →
      ∀ x : Fin m → ℝ,
        alignmentJointRouteNativeReading D n v hv factor obs B a c stored query (projection (L e • x)) =
          alignmentJointRouteNativeReading D n v hv factor obs B a c stored
            (query + alignmentAuxiliaryUnit e 1) (projection x) := by
  dsimp only
  obtain ⟨L, hL⟩ := alignment_catalogue_common_letters_in_coordinates D n v hv targets
    H ρ hρ h m b w hb hsym
  refine ⟨L, ?_⟩
  intro e B a c stored query ν hfactor htarget x
  let index := alignmentOwnTargetIndex targets e
  let k : AlignmentOwnTargetFactors targets e := ⟨ν, htarget⟩
  have hdelta : alignmentAuxiliaryUnit e 1 = Pi.single e 1 := by
    funext f
    simp only [alignmentAuxiliaryUnit, Pi.single_apply]
  rw [hdelta]
  apply alignment_joint_route_native_reading_restricted_lift D n v hv index k
    factor obs B a c stored query (Pi.single e 1) hfactor
  rw [alignment_joint_route_projection_restriction,
    alignment_joint_route_projection_restriction]
  exact hL e x

end Hindman168
