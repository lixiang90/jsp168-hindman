import Hindman168.AlignmentDuplicatedTargetCatalogue
import Hindman168.AlignmentBinarySlotFaceSpecialization
import Hindman168.AffineShearAlignmentSlotLifts

/-! Actual positive-event selection and one full-source extraction yield
both measure and setwise face symmetries for every target marginal. The
setwise assertion concerns the actual projection of the same full joint
cube orbit; no independent target filtration or Haar law is introduced. -/
namespace Hindman168
open Module Filter MeasureTheory FiniteMass Set
open scoped Manifold ContDiff BigOperators Classical Topology
universe u
attribute [local instance] alignmentAddingPairFintype lieGroup_smooth_min_three

variable {ι : Type} [Fintype ι] {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))
  (targets : ι → Finset (Fin N))

noncomputable def AlignmentTargetCodeCosetSymmetry
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (c : AlignmentPriorTail N i × ℕ) : Prop :=
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  let κ := AlignmentDuplicatedTargetSlots i targets c
  let index := alignmentDuplicatedTargetIndex i targets c
  let T := c.1.val
      ∀ (q : Fin (s+2))
        (weight : κ → Fin q.val → ℤ), (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
        ∀ e : AlignmentAddingPair N i, e.targetTail=T → ∀ j : Fin q.val,
      AlignmentRestrictedCubeHaarInvariant D n v hv (index) H
        ρ hρ q.val h
        (fun ν => alignmentBinaryCubeVertex (weight ν)) (fun ν => Pi.single e (weight ν j)) ∧
      (alignmentJointNativeCosetSlotTranslation (D ∘ index) (n ∘ index) (fun k => v (index k)) (fun k => hv (index k)) (fun ν => Pi.single e (weight ν j))) '' Set.range (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (index) (fun ν => alignmentBinaryCubeVertex (weight ν)) ∘ nativeResidueCubeOrbitMap J H ρ hρ q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) h) =
        Set.range (nativeFinitePiRestrictedCubeProjection (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) (index) (fun ν => alignmentBinaryCubeVertex (weight ν)) ∘ nativeResidueCubeOrbitMap J H ρ hρ q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) h)

noncomputable def AlignmentCatalogueCosetSymmetry
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G) : Prop :=
  ∀ τ, AlignmentTargetCodeCosetSymmetry D n v hv targets H ρ hρ h (alignmentDuplicatedTargetCode i τ)

 theorem alignment_catalogue_symmetry_full_faces
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) s)
    (ρ : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).E)
      (I := (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).I)
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ)
    (h : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G)
    (hsym : AlignmentCatalogueCosetSymmetry D n v hv targets H ρ hρ h) :
    ∀ e : AlignmentAddingPair N i, ∀ d : ℕ, 1 ≤ d → d ≤ s+1 → ∀ j : Fin d,
      let A := fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)
      let X := range (nativeFinitePiRestrictedCubeProjection A
        (fun a : {ν : ι // targets ν = e.targetTail} × Finset (Fin d) => a.1.val) Prod.snd ∘
          nativeResidueCubeOrbitMap (nativeFinitePiData A) H ρ hρ d (2^d-1)
            (nativeCubeVertexEnumeration d) h)
      alignmentJointNativeCosetSlotTranslation
        (fun a : {ν : ι // targets ν = e.targetTail} × Finset (Fin d) => D (a.1.val))
        (fun a => n (a.1.val)) (fun a => v (a.1.val)) (fun a => hv (a.1.val))
        (fun a => if j ∈ a.2 then Pi.single e 1 else 0) '' X = X := by
  intro e d hd hd' j
  apply alignment_binary_slot_symmetries_full_face D n v hv
    (fun ν : {ν : ι // targets ν = e.targetTail} => ν.val) H ρ hρ h d e
  intro weight hw k
  have hc : AlignmentTargetCodeCosetSymmetry D n v hv targets H ρ hρ h
      ((⟨e.targetTail, alignmentPair_target_before e⟩ : AlignmentPriorTail N i), d) :=
    (alignment_duplicated_target_code_encode i
      (⟨e.targetTail, alignmentPair_target_before e⟩ : AlignmentPriorTail N i) d) ▸
        hsym (Encodable.encode ((⟨e.targetTail, alignmentPair_target_before e⟩ :
          AlignmentPriorTail N i), d))
  exact (hc ⟨d, by omega⟩ weight hw e rfl k).2

abbrev AlignmentOwnTargetFactors (e : AlignmentAddingPair N i) :=
  {ν : ι // targets ν = e.targetTail}

noncomputable def alignmentOwnTargetIndex (e : AlignmentAddingPair N i) :
    AlignmentOwnTargetFactors targets e → ι := Subtype.val

 theorem alignment_catalogue_common_letters_in_coordinates
    (H : NativeRationalSubgroupFiltration
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))) s)
    (ρ : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (hρ : ρ ∈ nativeSubgroupRationalHull
      (E := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).E)
      (I := (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).I)
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).Γ)
    (h : (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))).G)
    (m : ℕ)
    (b : Basis (Fin m) ℝ (nativeRationalLayerOrbitData
      (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
        H 1 ρ hρ).E)
    (w : Fin m → ℕ)
    (hb : ∀ i, 1 ≤ w i ∧ w i ≤ s ∧
      b i ∈ affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          H ρ hρ (w i) ∧
      affineShearNativeInitialFiltration
        (nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)))
          H ρ hρ (w i+1) ≤ (b.coord i).ker)
    (hsym : AlignmentCatalogueCosetSymmetry D n v hv targets H ρ hρ h) :
    let A := nativeFinitePiData (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k))
    ∃ L : AlignmentAddingPair N i → weightedShearGroup (R := ℝ) w, ∀ e : AlignmentAddingPair N i,
    let C := nativeFinitePiData ((fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ∘ (alignmentOwnTargetIndex targets e))
    let p := affineShearNativePiRestriction
      (fun k => alignmentNativeArrayData (D k) (n k) (v k) (hv k)) ((alignmentOwnTargetIndex targets e))
    let K := nativeRationalLayerOrbitData A H 1 ρ hρ
    let S : C.G ≃* C.G := alignmentJointNativeSlotTranslation (D ∘ (alignmentOwnTargetIndex targets e)) (n ∘ (alignmentOwnTargetIndex targets e))
      (fun k => v ((alignmentOwnTargetIndex targets e) k)) (fun k => hv ((alignmentOwnTargetIndex targets e) k)) ((fun _ => Pi.single e 1))
    ∀ x : Fin m → ℝ,
      (p h * p (nativeLieExponential (I := K.I) (G := K.G)
        (b.equivFun.symm (L e • x))).val * p ρ : C.G ⧸ C.Γ) =
      (S (p h * p (nativeLieExponential (I := K.I) (G := K.G)
          (b.equivFun.symm x)).val * p ρ) : C.G ⧸ C.Γ) := by
  apply affineShear_alignment_letter_lifts_in_coordinates D n v hv
    (alignmentOwnTargetIndex targets) (fun e _ => Pi.single e 1) H ρ hρ h m b w hb
  exact alignment_catalogue_symmetry_full_faces D n v hv targets H ρ hρ h hsym

end Hindman168
