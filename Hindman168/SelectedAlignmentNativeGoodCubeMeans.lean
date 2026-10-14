import Hindman168.SelectedAlignmentFaceNativeFailure
import Hindman168.AlignmentOriginalProjectedCubeMeans

/-! Failure avoidance gives a strict bound for the actual original native
means, retaining uniformity over all endpoints, residues, profiles and tests. -/
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

theorem selected_alignment_native_complete_cube_good_mean_bound
    (F : MasterParameterFamily) (gap : Fin N) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
    (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G)
    (B : ℝ) (L : NNReal) (c C η : ℝ) (y : Fin N → ℕ)
    (hgood : ¬ selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F gap q₀ w T d shift g a B L c C η y) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    ∀ weight : ι → κ → ℤ, (∀ ν j, weight ν j=0 ∨ weight ν j=1) →
    ∀ e : AlignmentAddingPair N i, e.targetTail=T → e.sourcePivot < gap → ∀ (j : κ) (lower upper : Option κ → ℝ)
      (ellResidue : Option κ → ℤ) (obs : C(J.G ⧸ J.Γ,ℂ)),
      (∀ z, |lower z| ≤ C*alignmentLocalLength F w i ∧ |upper z| ≤ C*alignmentLocalLength F w i ∧
        c*alignmentLocalLength F w i ≤ upper z-lower z) →
      obs ∈ boundedComplexLipschitzObservables (J.G ⧸ J.Γ) B L →
    let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
    let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
    ‖alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a
          (fun x => obs (alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j)) x))-
        alignmentOriginalNativeCubeMean D n v hv F q₀ w T y p Y d ellResidue lower upper shift weight g a obs‖ < η := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  intro weight hw e he hbefore j lower upper ellResidue obs hbox hobs
  by_contra h
  apply hgood
  exact ⟨weight,hw,e,he,hbefore,j,lower,upper,ellResidue,obs,hbox,hobs,le_of_not_gt h⟩

end Hindman168
