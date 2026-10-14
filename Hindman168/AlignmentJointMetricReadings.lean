import Hindman168.AlignmentJointNativeReadings
import Hindman168.BoundedComplexLipschitzObservables
import Hindman168.CompactLipschitzApproximation

/-! Exact observations in the ACTUAL specified native metrics. The genuine
bounded/Lipschitz input class has compact image; one finite approximant list
and numerical output bounds are chosen BEFORE arbitrary input observations. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_metric_quotient_compact {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    CompactSpace (D.G ⧸ D.Γ) :=
  Eq.mp (congrArg (fun t => @CompactSpace (D.G ⧸ D.Γ) t) (nativeNilmanifold_metric_topology D)) D.quotientCompact

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

noncomputable def alignmentJointNativeMetricReading (ν : ι) (z : σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    C((D ν).G ⧸ (D ν).Γ,ℂ) → C(J.G ⧸ J.Γ,ℂ) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI := (D ν).metric
  letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
  intro F
  exact F.comp ⟨alignmentJointNativeCosetEvaluation D n v hv ν z,
    alignment_joint_native_metric_coset_evaluation_continuous D n v hv ν z⟩

theorem alignment_joint_native_metric_reading_apply (ν : ι) (z : σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ (F : C((D ν).G ⧸ (D ν).Γ,ℂ)) (y : J.G ⧸ J.Γ),
      alignmentJointNativeMetricReading D n v hv ν z F y = F (alignmentJointNativeCosetEvaluation D n v hv ν z y) := by
  dsimp only
  intro F y
  rfl

theorem alignment_joint_native_metric_reading_continuous (ν : ι) (z : σ ν → ℤ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    Continuous (alignmentJointNativeMetricReading D n v hv ν z) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI := (D ν).metric
  letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
  exact ContinuousMap.continuous_precomp
    ⟨alignmentJointNativeCosetEvaluation D n v hv ν z,
      alignment_joint_native_metric_coset_evaluation_continuous D n v hv ν z⟩

theorem alignment_joint_native_metric_reading_family_compact (ν : ι) (z : σ ν → ℤ) (B : ℝ) (L : NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    IsCompact (alignmentJointNativeMetricReading D n v hv ν z ''
      boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) B L) := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI := (D ν).metric
  letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
  exact (bounded_complex_lipschitz_observables_compact ((D ν).G ⧸ (D ν).Γ) B L).image
    (alignment_joint_native_metric_reading_continuous D n v hv ν z)

theorem alignment_joint_native_metric_reading_uniform_approximation (ν : ι) (z : σ ν → ℤ) (B : ℝ) (L : NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
    letI := (D ν).metric
    letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ ε : ℝ, 0 < ε → ∃ B' L' : ℝ, 0 < B' ∧ 0 < L' ∧ ∃ P : Finset C(J.G ⧸ J.Γ,ℂ),
      (∀ G ∈ P, (∀ y, ‖G y‖ ≤ B') ∧ LipschitzWith (Real.toNNReal L') G) ∧
      ∀ F ∈ boundedComplexLipschitzObservables ((D ν).G ⧸ (D ν).Γ) B L,
        ∃ G ∈ P, ‖alignmentJointNativeMetricReading D n v hv ν z F-G‖ < ε := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (J.G ⧸ J.Γ) := native_metric_quotient_compact J
  letI := (D ν).metric
  letI : TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := (D ν).metric.toUniformSpace.toTopologicalSpace
  intro ε hε
  obtain ⟨B',L',hB',hL',P,hP,hclose⟩ := compact_family_bounded_lipschitz_approximation
    (J.G ⧸ J.Γ) _ (alignment_joint_native_metric_reading_family_compact D n v hv ν z B L) ε hε
  refine ⟨B',L',hB',hL',P,hP,?_⟩
  intro F hF
  exact hclose _ ⟨F,hF,rfl⟩

end Hindman168
