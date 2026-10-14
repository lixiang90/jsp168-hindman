import Hindman168.AlignmentJointMetricProducts
import Hindman168.NativeRealResidualObservableApproximation

/-! The original simultaneous product-observation family in the ACTUAL
joint array quotient supplies the compact family required for rough events. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointOriginalTestFamily (z : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    Set C(J.G ⧸ J.Γ,ℂ) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact alignmentJointNativeMetricProduct D n v hv z ''
    Set.pi Set.univ (fun ν => boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν))

theorem alignment_joint_original_test_family_compact (z : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    IsCompact (alignmentJointOriginalTestFamily D n v hv z B L) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact alignment_joint_native_metric_product_family_compact D n v hv z B L

theorem alignment_joint_original_test_family_residual_bounds (z : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) (η : ℝ) (hη : 0 < η) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∃ B' L' : ℝ, 0 < B' ∧ 0 < L' ∧
      ∀ F ∈ alignmentJointOriginalTestFamily D n v hv z B L,
        ∃ G : C(J.G ⧸ J.Γ,ℂ), LipschitzWith (Real.toNNReal L') G ∧
          (∀ y, ‖G y‖ ≤ B') ∧ ‖F-G‖ < η/4 := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  exact rough_native_real_residual_compact_family_bounds
    (nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))) η hη
    (alignmentJointOriginalTestFamily D n v hv z B L)
    (alignment_joint_original_test_family_compact D n v hv z B L)

end Hindman168
