import Hindman168.AlignmentOriginalNativeCubeMeans
import Hindman168.AlignmentJointNativeCylinderDetection

/-! Complete tests of the ACTUAL native cube law, and its literal cylinder
detector failures. Own faces, zero/one profiles, boxes/residues and tests are
quantified AFTER sampling, with the unchanged original empirical mean. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators Classical
universe u

variable {ι : Type} [Fintype ι] {κ : Type*} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def selectedAlignmentNativeCompleteCubeAllFacesFailure
    (F : MasterParameterFamily) (gap : Fin N) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G)
    (B : ℝ) (L : NNReal) (c C η : ℝ) (y : Fin N → ℕ) : Prop := by
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
  exact ∃ weight : ι → κ → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) ∧
    ∃ e : AlignmentAddingPair N i, e.targetTail=T ∧ e.sourcePivot < gap ∧ ∃ (j : κ) (lower upper : Option κ → ℝ)
      (ellResidue : Option κ → ℤ) (obs : C(J.G ⧸ J.Γ,ℂ)),
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
      obs ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L ∧
      η ≤ ‖alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a
          (fun x => obs (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) x))-
        alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a obs‖

noncomputable def selectedAlignmentNativeCylinderCubeAllFacesFailure
    (F : MasterParameterFamily) (gap : Fin N) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G)
    (c C τ : ℝ)
    (test : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ → ℂ)
    (y : Fin N → ℕ) : Prop :=
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
  ∃ weight : ι → κ → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) ∧
    ∃ e : AlignmentAddingPair N i, e.targetTail=T ∧ e.sourcePivot < gap ∧ ∃ (j : κ) (lower upper : Option κ → ℝ)
      (ellResidue : Option κ → ℤ),
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) ∧
      τ ≤ ‖alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a
          (fun x => test (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) x))-
        alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a test‖

end Hindman168
