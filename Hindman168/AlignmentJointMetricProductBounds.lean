import Hindman168.AlignmentJointNativeSampleReadings
import Hindman168.AlignmentJointResidualTestFamily

/-! The literal original joint product test has the product of original sup
bounds on EVERY actual joint quotient point. No Lipschitz property of a
projection, source or composed test is asserted. -/
namespace Hindman168
open scoped Manifold ContDiff BigOperators
universe u

variable {ι : Type} [Fintype ι] {σ : ι → Type} {s : ℕ}
  (D : ι → NativeNilmanifoldData.{u} s) (n : ι → ℕ)
  (v : ∀ ν, Fin (n ν+1) → σ ν → ℤ)
  (hv : ∀ ν, Function.Injective
    (alignmentNativeFiniteEvaluation (E := (D ν).E) (I := (D ν).I) (G := (D ν).G) (n ν) (v ν)))

theorem alignment_joint_native_metric_product_norm_bound (slots : ∀ ν, σ ν → ℤ) (B : ι → ℝ) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ obs : ∀ ν, C((D ν).G ⧸ (D ν).Γ,ℂ), (∀ ν x, ‖obs ν x‖ ≤ B ν) →
    ∀ y : J.G ⧸ J.Γ, ‖alignmentJointNativeMetricProduct D n v hv slots obs y‖ ≤ ∏ ν, B ν := by
  dsimp only
  intro obs hobs y
  rw [alignment_joint_native_metric_product_apply,norm_prod]
  exact Finset.prod_le_prod (fun _ _ => norm_nonneg _)
    (fun ν _ => hobs ν (alignmentJointNativeCosetEvaluation D n v hv ν (slots ν) y))

theorem alignment_joint_original_test_family_norm_bound (slots : ∀ ν, σ ν → ℤ)
    (B : ι → ℝ) (L : ι → NNReal) :
    let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
    letI := J.metric
    letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    ∀ F ∈ alignmentJointOriginalTestFamily D n v hv slots B L, ∀ y : J.G ⧸ J.Γ, ‖F y‖ ≤ ∏ ν, B ν := by
  dsimp only
  let J := nativeFinitePiData (fun ν => alignmentNativeArrayData (D ν) (n ν) (v ν) (hv ν))
  letI := J.metric
  letI : TopologicalSpace (J.G ⧸ J.Γ) := J.metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  intro F hF y
  obtain ⟨obs,hobs,rfl⟩ := hF
  exact alignment_joint_native_metric_product_norm_bound D n v hv slots B obs
    (fun ν x => (hobs ν (Set.mem_univ ν)).2 x) y

end Hindman168
