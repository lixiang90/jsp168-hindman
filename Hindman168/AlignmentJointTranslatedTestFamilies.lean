import Hindman168.AlignmentJointNativeSlotTranslations
import Hindman168.AlignmentJointMetricProducts
import Hindman168.AlignmentJointNativeSampleReadings

/-! Fixed face-composed ORIGINAL product tests. Slot evaluation identifies
composition exactly with shifted original slots. Compact input families
therefore admit one finite bounded/Lipschitz approximant list BEFORE sources,
endpoints, denominator choices and posterior samples; numerical projection
Lipschitz bounds are never assumed. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeTranslatedMetricProduct (slots face : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    (∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ)) → C(J.G ⧸ J.Γ,ℂ) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs
  exact (alignmentJointNativeMetricProduct D n v hv slots obs).comp
    ⟨alignmentJointNativeCosetSlotTranslation D n v hv face,
      alignment_joint_native_metric_coset_slot_translation_continuous D n v hv face⟩

theorem alignment_joint_native_translated_metric_product_eq (slots face : ∀ ν, σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ),
      alignmentJointNativeTranslatedMetricProduct D n v hv slots face obs=
        alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+face ν) obs := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro obs
  ext y
  change alignmentJointNativeMetricProduct D n v hv slots obs
    (alignmentJointNativeCosetSlotTranslation D n v hv face y)=_
  rw [alignment_joint_native_metric_product_apply,alignment_joint_native_metric_product_apply]
  simp_rw [alignment_joint_native_coset_slot_translation_evaluation]

theorem alignment_joint_native_translated_metric_product_family_compact (slots face : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    IsCompact (alignmentJointNativeTranslatedMetricProduct D n v hv slots face ''
      Set.pi Set.univ (fun ν => boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) (B ν) (L ν))) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have he : alignmentJointNativeTranslatedMetricProduct D n v hv slots face=
      alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+face ν) := by
    funext obs
    exact alignment_joint_native_translated_metric_product_eq D n v hv slots face obs
  rw [he]
  exact alignment_joint_native_metric_product_family_compact D n v hv (fun ν => slots ν+face ν) B L

theorem alignment_joint_native_translated_metric_product_uniform_approximation (slots face : ∀ ν, σ ν → ℤ)
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
        ∃ G ∈ P, ‖alignmentJointNativeTranslatedMetricProduct D n v hv slots face F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  have he : alignmentJointNativeTranslatedMetricProduct D n v hv slots face=
      alignmentJointNativeMetricProduct D n v hv (fun ν => slots ν+face ν) := by
    funext obs
    exact alignment_joint_native_translated_metric_product_eq D n v hv slots face obs
  rw [he]
  exact alignment_joint_native_metric_product_uniform_approximation D n v hv (fun ν => slots ν+face ν) B L

end Hindman168
