import Hindman168.AlignmentJointMetricReadings

/-! The ACTUAL finite product test family on the joint native quotient.
Input numerical bounds are fixed; compactness gives ONE finite Lipschitz
approximation list before every choice of original component observations. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeMetricProduct (z : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) :=
      fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)) → C(J.G ⧸ J.Γ,ℂ) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact fun F => ∏ ν, alignmentJointNativeMetricReading D n v hv ν (z ν) (F ν)

theorem alignment_joint_native_metric_product_continuous (z : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    Continuous (alignmentJointNativeMetricProduct D n v hv z) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  apply continuous_finsetProd
  intro ν _
  exact (alignment_joint_native_metric_reading_continuous D n v hv ν (z ν)).comp (continuous_apply ν)

theorem alignment_joint_native_metric_product_family_compact (z : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    IsCompact (alignmentJointNativeMetricProduct D n v hv z ''
      Set.pi Set.univ (fun ν => boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν))) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  exact (isCompact_univ_pi (fun ν => bounded_complex_lipschitz_observables_compact
    ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν))).image
    (alignment_joint_native_metric_product_continuous D n v hv z)

theorem alignment_joint_native_metric_product_uniform_approximation (z : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ ε : ℝ, 0 < ε → ∃ B' L' : ℝ, 0 < B' ∧ 0 < L' ∧ ∃ P : Finset C(J.G ⧸ J.Γ,ℂ),
      (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B') ∧ LipschitzWith (Real.toNNReal L') G) ∧
      ∀ F : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
        (∀ ν, F ν ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν)) →
        ∃ G ∈ P, ‖alignmentJointNativeMetricProduct D n v hv z F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro ε hε
  obtain ⟨B',L',hB',hL',P,hP,hclose⟩ := compact_family_bounded_lipschitz_approximation
    (J.G ⧸ J.Γ) _ (alignment_joint_native_metric_product_family_compact D n v hv z B L) ε hε
  refine ⟨B',L',hB',hL',P,hP,?_⟩
  intro F hF
  exact hclose _ ⟨F,(fun ν _ => hF ν),rfl⟩

end Hindman168
