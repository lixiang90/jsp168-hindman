import Hindman168.AlignmentNativeCompleteCubeDetection
import Hindman168.SelectedAlignmentFaceNativeFailure
import Hindman168.SelectedAlignmentFaceProductFailure

namespace Hindman168
open scoped Manifold ContDiff Classical NNReal Topology
universe u

variable {ι : Type} [Fintype ι] {κ : Type} [Fintype κ]
  {N : ℕ} {i : Fin N} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → AlignmentAddingPair N i → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem selected_alignment_native_complete_cube_failure_finite_detection
    (B : ℝ) (L : NNReal) (η : ℝ) (hη : 0 < η) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    ∃ (Q : Finset (List C(J.G ⧸ J.Γ,ℂ))) (τ : ℝ), 0 < τ ∧
      (∀ l ∈ Q, ∀ f ∈ l, f ∈ alignmentJointNativeCylinderGenerators D n v hv) ∧
      ∀ (F : MasterParameterFamily) (gap : Fin N) (q₀ w : ℕ) (T : Finset (Fin N)) (d : ℕ)
        (shift : ι → AlignmentAddingPair N i → ℤ) (g a : ∀ ν, (D ν).G) (c C : ℝ) (y : Fin N → ℕ),
        selectedAlignmentNativeCompleteCubeAllFacesFailure (κ := κ) D n v hv F gap q₀ w T d shift g a B L c C η y →
        ∃ l ∈ Q, selectedAlignmentNativeCylinderCubeAllFacesFailure (κ := κ) D n v hv F gap q₀ w T d shift g a c C τ l.prod y := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  obtain ⟨Q,τ,hτ,hQ,hdetect⟩ := alignment_joint_native_complete_cylinder_detection D n v hv B L η hη
  refine ⟨Q,τ,hτ,hQ,?_⟩
  intro F gap q₀ w T d shift g a c C y hbad
  obtain ⟨weight,hw,e,he,hegap,j,lower,upper,ellResidue,obs,hgeo,hobs,hbad⟩ := hbad
  let p := alignmentMicrocellFirst (alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w)) (F.modulus w) (y i)
  let Y : ℤ := (alignmentShortBinStart F w i T y : ℤ)/(F.modulus w : ℤ)
  let S := alignmentBoxClass (fun j => ⌈lower j⌉) (fun j => ⌈upper j⌉) ellResidue d
  let state := alignmentOriginalNativeCubeState D n v hv F q₀ w T y p Y shift weight g a
  let action := alignmentJointNativeCosetSlotTranslation D n v hv (fun ν => Pi.single e (weight ν j))
  have hh : η ≤ ‖FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) (fun ell => obs (action (state ell)))-
      FiniteMass.complexExpectation (FiniteMass.uniformFinsetMass S) (fun ell => obs (state ell))‖ := hbad
  obtain ⟨l,hl,herror⟩ := hdetect S S (fun ell => action (state ell)) state obs hobs hh
  exact ⟨l,hl,weight,hw,e,he,hegap,j,lower,upper,ellResidue,hgeo,herror⟩

end Hindman168
