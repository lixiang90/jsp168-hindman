import Hindman168.NativeFinitePiCosetCoordinates
import Hindman168.AlignmentArrayNativeCosetEvaluation
import Hindman168.AlignmentJointExposedNativeSource

/-! Actual complex observations on the genuine joint native quotient.
Every reading is exactly the original component observation at its integer
array slot. Continuity is proved in both quotient and supplied metric topologies. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeCosetEvaluation (ν : ι) (z : σ ν → ℤ) :
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ → (D ν).G ⧸ (D ν).Γ :=
  alignmentArrayNativeCosetEvaluation (D ν) (n ν) (v ν) (hv ν) z ∘
    nativeFinitePiCosetCoordinate (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) ν

theorem alignment_joint_native_coset_evaluation_continuous (ν : ι) (z : σ ν → ℤ) :
    Continuous (alignmentJointNativeCosetEvaluation D n v hv ν z) :=
  (alignment_array_native_coset_evaluation_continuous (D ν) (n ν) (v ν) (hv ν) z).comp
    (native_finite_pi_coset_coordinate_continuous (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) ν)

theorem alignment_joint_native_metric_coset_evaluation_continuous (ν : ι) (z : σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    Continuous (alignmentJointNativeCosetEvaluation D n v hv ν z) := by
  dsimp only
  rw [←nativeNilmanifold_metric_topology
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))),
    ←nativeNilmanifold_metric_topology (D ν)]
  exact alignment_joint_native_coset_evaluation_continuous D n v hv ν z

noncomputable def alignmentJointNativeComplexReading (ν : ι) (z : σ ν → ℤ)
    (f : C((D ν).G ⧸ (D ν).Γ,ℂ)) :
    C((nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ,ℂ) :=
  f.comp ⟨alignmentJointNativeCosetEvaluation D n v hv ν z,
    alignment_joint_native_coset_evaluation_continuous D n v hv ν z⟩

theorem alignment_joint_native_complex_reading_mk (ν : ι) (z : σ ν → ℤ)
    (f : C((D ν).G ⧸ (D ν).Γ,ℂ))
    (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G) :
    alignmentJointNativeComplexReading D n v hv ν z f
      (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
        (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) =
      f ((alignmentArrayNativeEvaluation (D ν) (n ν) (v ν) (hv ν) z
        (nativeFinitePiGroupEquiv (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν)) a ν) :
        (D ν).G ⧸ (D ν).Γ)) := rfl

theorem alignment_joint_native_complex_reading_bound (ν : ι) (z : σ ν → ℤ)
    (f : C((D ν).G ⧸ (D ν).Γ,ℂ)) (B : ℝ) (hf : ∀ x, ‖f x‖ ≤ B)
    (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    ‖alignmentJointNativeComplexReading D n v hv ν z f a‖ ≤ B := hf _

theorem alignment_joint_native_complex_reading_difference (ν : ι) (z : σ ν → ℤ)
    (f f' : C((D ν).G ⧸ (D ν).Γ,ℂ)) (ε : ℝ) (h : ∀ x, ‖f x-f' x‖ ≤ ε)
    (a : (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).G ⧸
      (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))).Γ) :
    ‖alignmentJointNativeComplexReading D n v hv ν z f a-
      alignmentJointNativeComplexReading D n v hv ν z f' a‖ ≤ ε := h _

end Hindman168
