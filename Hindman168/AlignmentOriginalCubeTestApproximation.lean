import Hindman168.AlignmentOriginalContinuousCubeMean
import Hindman168.BoundedComplexLipschitzObservables

/-! The COMPLETE original numerical bounded/Lipschitz cube test class is
compact in its genuine product metric. ONE finite product-span approximant
list is fixed before original sources, endpoints, residues or samples. -/
namespace Hindman168
open scoped Classical
universe u
variable {ι : Type} [Fintype ι] {s : ℕ} (D : ι → NativeNilmanifoldData.{u} s)

theorem alignment_original_complete_cube_test_product_approximation (B : ℝ) (L : NNReal) :
    letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
    letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
    letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
    ∀ ε : ℝ, 0 < ε → ∃ P : Finset C((∀ ν, (D ν).G ⧸ (D ν).Γ),ℂ),
      (∀ G ∈ P, G ∈ finitePiLipschitzProductSpan (fun ν => (D ν).G ⧸ (D ν).Γ)) ∧
      ∀ F ∈ boundedComplexLipschitzObservables (∀ ν, (D ν).G ⧸ (D ν).Γ) B L,
        ∃ G ∈ P, ‖F-G‖ < ε := by
  letI : ∀ ν, MetricSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric
  letI : ∀ ν, TopologicalSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => (D ν).metric.toUniformSpace.toTopologicalSpace
  letI : ∀ ν, CompactSpace ((D ν).G ⧸ (D ν).Γ) := fun ν => native_metric_quotient_compact (D ν)
  intro ε hε
  exact compact_family_finite_pi_product_span_approximation (fun ν => (D ν).G ⧸ (D ν).Γ)
    (boundedComplexLipschitzObservables (∀ ν, (D ν).G ⧸ (D ν).Γ) B L)
    (bounded_complex_lipschitz_observables_compact (∀ ν, (D ν).G ⧸ (D ν).Γ) B L) ε hε

end Hindman168
